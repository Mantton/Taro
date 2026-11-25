#include "tree_sitter/parser.h"
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

enum TokenType {
  STRING_START, STRING_CONTENT, STRING_END,
  INTERPOLATION_START, INTERPOLATION_FORMAT, INTERPOLATION_END, STRING_ESCAPE, BLOCK_COMMENT, ERRDEFER_KEYWORD,
};

typedef struct {
  uint32_t hashes;
  bool multiline;
  bool expression;
} Frame;

// Fits within Tree-sitter's scanner-state serialization budget. Each nested
// literal owns its delimiter state; interpolation bodies use the normal grammar.
#define MAX_DEPTH 128
typedef struct { Frame frames[MAX_DEPTH]; uint8_t depth; } Scanner;

void *tree_sitter_taro_external_scanner_create(void) { return calloc(1, sizeof(Scanner)); }
void tree_sitter_taro_external_scanner_destroy(void *payload) { free(payload); }

unsigned tree_sitter_taro_external_scanner_serialize(void *payload, char *buffer) {
  Scanner *scanner = payload;
  unsigned n = 0;
  buffer[n++] = scanner->depth;
  for (unsigned i = 0; i < scanner->depth; i++) {
    Frame *frame = &scanner->frames[i];
    for (unsigned byte = 0; byte < 4; byte++) buffer[n++] = (char)(frame->hashes >> (byte * 8));
    buffer[n++] = (char)(frame->multiline | (frame->expression << 1));
  }
  return n;
}

void tree_sitter_taro_external_scanner_deserialize(void *payload, const char *buffer, unsigned length) {
  Scanner *scanner = payload;
  scanner->depth = 0;
  if (!length) return;
  unsigned count = (uint8_t)buffer[0];
  if (count > MAX_DEPTH || length != 1 + count * 5) return;
  unsigned n = 1;
  for (unsigned i = 0; i < count; i++) {
    Frame *frame = &scanner->frames[i];
    frame->hashes = 0;
    for (unsigned byte = 0; byte < 4; byte++) frame->hashes |= (uint32_t)(uint8_t)buffer[n++] << (byte * 8);
    uint8_t flags = (uint8_t)buffer[n++];
    frame->multiline = flags & 1;
    frame->expression = flags & 2;
  }
  scanner->depth = (uint8_t)count;
}

static void advance(TSLexer *lexer) { lexer->advance(lexer, false); }

static bool block_comment(TSLexer *lexer) {
  advance(lexer);
  if (lexer->lookahead != '*') return false;
  advance(lexer);
  unsigned depth = 1;
  while (!lexer->eof(lexer) && depth) {
    int32_t ch = lexer->lookahead;
    advance(lexer);
    if (ch == '/' && lexer->lookahead == '*') { advance(lexer); depth++; }
    else if (ch == '*' && lexer->lookahead == '/') { advance(lexer); depth--; }
  }
  return depth == 0;
}

static bool word_char(int32_t ch) {
  return ch == '_' || (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') ||
         (ch >= '0' && ch <= '9');
}

// The grammar accepts adjacent statements, so a bare identifier followed by
// a call or subscript must be distinguished before consuming the keyword.
static bool errdefer_keyword(TSLexer *lexer) {
  for (const char *p = "errdefer"; *p; ++p) {
    if (lexer->lookahead != *p) return false;
    advance(lexer);
  }
  if (word_char(lexer->lookahead)) return false;
  lexer->mark_end(lexer);
  for (;;) {
    while (lexer->lookahead == ' ' || lexer->lookahead == '\t') advance(lexer);
    if (lexer->lookahead != '/') break;
    if (!block_comment(lexer)) return false;
  }
  int32_t ch = lexer->lookahead;
  if (ch == 'a' || ch == 'i') {
    advance(lexer);
    if ((ch == 'a' && lexer->lookahead == 's') ||
        (ch == 'i' && (lexer->lookahead == 's' || lexer->lookahead == 'n'))) {
      advance(lexer);
      if (!word_char(lexer->lookahead)) return false;
    }
  }
  return word_char(ch) || ch == '{' || ch == '#' || ch == '~' || ch == '"' || ch == '\'';
}

bool tree_sitter_taro_external_scanner_scan(void *payload, TSLexer *lexer, const bool *valid) {
  Scanner *scanner = payload;
  Frame *frame = scanner->depth ? &scanner->frames[scanner->depth - 1] : NULL;
  if (frame && !frame->expression && (valid[STRING_CONTENT] || valid[STRING_END])) {
    bool content = false;
    lexer->mark_end(lexer);
    while (!lexer->eof(lexer)) {
      if (lexer->lookahead == '"') {
        unsigned quotes = frame->multiline ? 3 : 1;
        unsigned seen = 0;
        while (seen < quotes && lexer->lookahead == '"') { advance(lexer); seen++; }
        unsigned hashes = 0;
        if (seen == quotes) {
          while (hashes < frame->hashes && lexer->lookahead == '#') { advance(lexer); hashes++; }
        }
        if (seen == quotes && hashes == frame->hashes) {
          if (content) { lexer->result_symbol = STRING_CONTENT; return true; }
          lexer->mark_end(lexer);
          scanner->depth--;
          lexer->result_symbol = STRING_END;
          return valid[STRING_END];
        }
      } else if (lexer->lookahead == '$') {
        advance(lexer);
        uint32_t hashes = 0;
        while (lexer->lookahead == '#') { advance(lexer); hashes++; }
        if (hashes == frame->hashes && lexer->lookahead == '{') {
          if (content) { lexer->result_symbol = STRING_CONTENT; return true; }
          advance(lexer);
          lexer->mark_end(lexer);
          frame->expression = true;
          lexer->result_symbol = INTERPOLATION_START;
          return valid[INTERPOLATION_START];
        }
      } else if (lexer->lookahead == '\\' && frame->hashes == 0) {
        if (content) { lexer->result_symbol = STRING_CONTENT; return true; }
        advance(lexer);
        int32_t kind = lexer->lookahead;
        if (!lexer->eof(lexer)) advance(lexer);
        if (kind == 'x') {
          for (unsigned i = 0; i < 2 && !lexer->eof(lexer); i++) advance(lexer);
        } else if (kind == 'u' && lexer->lookahead == '{') {
          advance(lexer);
          while (!lexer->eof(lexer) && lexer->lookahead != '}' && lexer->lookahead != '\n') advance(lexer);
          if (lexer->lookahead == '}') advance(lexer);
        } else if (kind == '$' && lexer->lookahead == '{') { advance(lexer); }
        lexer->mark_end(lexer);
        lexer->result_symbol = STRING_ESCAPE;
        return valid[STRING_ESCAPE];
      } else {
        if (lexer->lookahead == '\n' && !frame->multiline) return false;
        advance(lexer);
      }
      content = true;
      lexer->mark_end(lexer);
    }
    if (content) { lexer->result_symbol = STRING_CONTENT; return valid[STRING_CONTENT]; }
    return false;
  }

  while (lexer->lookahead == ' ' || lexer->lookahead == '\t' || lexer->lookahead == '\n' || lexer->lookahead == '\r') {
    lexer->advance(lexer, true);
  }
  if (valid[ERRDEFER_KEYWORD] && lexer->lookahead == 'e') {
    if (!errdefer_keyword(lexer)) return false;
    lexer->result_symbol = ERRDEFER_KEYWORD;
    return true;
  }
  if (valid[BLOCK_COMMENT] && lexer->lookahead == '/') {
    if (!block_comment(lexer)) return false;
    lexer->mark_end(lexer);
    lexer->result_symbol = BLOCK_COMMENT;
    return true;
  }
  if (valid[INTERPOLATION_FORMAT] && frame && frame->expression && lexer->lookahead == ':') {
    advance(lexer);
    if (lexer->lookahead == ':' || lexer->lookahead == '=' || lexer->lookahead == '}' ||
        lexer->lookahead == '\n' || lexer->eof(lexer)) {
      return false;
    }
    // A label can introduce a loop inside the hole. Returning false lets
    // the grammar consume its colon without swallowing the loop body.
    while (lexer->lookahead == ' ' || lexer->lookahead == '\t') advance(lexer);
    if (lexer->lookahead == 'l') {
      const char *keyword = "loop";
      while (*keyword && lexer->lookahead == *keyword) {
        advance(lexer);
        keyword++;
      }
      if (!*keyword && !word_char(lexer->lookahead)) return false;
    }
    while (!lexer->eof(lexer) && lexer->lookahead != '}' && lexer->lookahead != '\n') {
      advance(lexer);
    }
    lexer->mark_end(lexer);
    lexer->result_symbol = INTERPOLATION_FORMAT;
    return true;
  }
  if (valid[INTERPOLATION_END] && frame && frame->expression && lexer->lookahead == '}') {
    advance(lexer);
    lexer->mark_end(lexer);
    frame->expression = false;
    lexer->result_symbol = INTERPOLATION_END;
    return true;
  }
  if (!valid[STRING_START] || scanner->depth >= MAX_DEPTH) return false;
  uint32_t hashes = 0;
  while (lexer->lookahead == '#') { advance(lexer); hashes++; }
  if (lexer->lookahead != '"') return false;
  advance(lexer);
  lexer->mark_end(lexer);
  bool multiline = false;
  // Speculate past a second quote, but commit it only for a triple delimiter.
  if (lexer->lookahead == '"') {
    advance(lexer);
    if (lexer->lookahead == '"') { advance(lexer); lexer->mark_end(lexer); multiline = true; }
  }
  scanner->frames[scanner->depth++] = (Frame){ .hashes = hashes, .multiline = multiline, .expression = false };
  lexer->result_symbol = STRING_START;
  return true;
}
