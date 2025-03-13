use index_vec::define_index_type;
use std::{
    cell::{Ref, RefCell},
    fs::read_to_string,
    path::PathBuf,
};
use taroc_error::{CompileError, CompileResult};

define_index_type! {
    pub struct FileID = u32;
}

pub struct SourceFile {
    path: PathBuf,
    content: RefCell<Option<String>>,
    lines_and_chars: RefCell<Option<SourceFileContent>>,
}

pub struct SourceFileContent {
    pub lines: Vec<usize>,
    pub characters: Vec<char>,
}

impl SourceFile {
    pub fn new(path: PathBuf) -> SourceFile {
        SourceFile {
            path,
            content: RefCell::new(None),
            lines_and_chars: RefCell::new(None),
        }
    }
}

impl SourceFile {
    pub fn path(&self) -> &PathBuf {
        &self.path
    }
    pub fn content(&self) -> CompileResult<Ref<String>> {
        if self.content.borrow().is_none() {
            let mut content_ref = self.content.borrow_mut();
            let content = read_to_string(&self.path).map_err(|err| {
                CompileError::Message(format!("failed to read file contents: {}", err))
            })?;
            *content_ref = Some(content);
        }

        // Now we can get an immutable borrow
        match Ref::filter_map(self.content.borrow(), |opt| opt.as_ref()) {
            Ok(string_ref) => Ok(string_ref),
            Err(_) => Err(CompileError::Message("Failed to borrow content".into())),
        }
    }

    pub fn body(&self) -> CompileResult<Ref<SourceFileContent>> {
        {
            let mut body_ref = self.lines_and_chars.borrow_mut();
            if body_ref.is_none() {
                let source = self.content()?;
                let characters: Vec<char> = source.chars().collect();
                let mut lines = vec![];
                let mut start = 0;
                // Iterate over the string's characters with their byte indices.
                for (i, c) in characters.iter().enumerate() {
                    if *c == '\n' {
                        // Push the current line slice and its starting index.
                        lines.push(start);
                        // Set the start of the next line to be after the newline character.
                        start = i + c.len_utf8();
                    }
                }
                // Add the last line (if the string doesn't end with a newline)
                if start <= source.len() {
                    lines.push(start);
                }

                let body = SourceFileContent { lines, characters };

                *body_ref = Some(body);
            }
        }

        match Ref::filter_map(self.lines_and_chars.borrow(), |opt| opt.as_ref()) {
            Ok(string_ref) => Ok(string_ref),
            Err(_) => Err(CompileError::Message("Failed to borrow content".into())),
        }
    }
}
