#include "llvm/ADT/StringRef.h"
#include "llvm/Analysis/ModuleSummaryAnalysis.h"
#include "llvm/Analysis/ProfileSummaryInfo.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/IR/Module.h"
#include "llvm/LTO/legacy/ThinLTOCodeGenerator.h"
#include "llvm/Support/CBindingWrapping.h"
#include "llvm/Support/CodeGen.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm-c/Core.h"
#include "llvm-c/TargetMachine.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <new>
#include <string>

namespace {

struct TaroThinLTOCodeGenerator {
  llvm::ThinLTOCodeGenerator Generator;
};

llvm::StringRef string_ref(const std::uint8_t *data, std::size_t length) {
  return llvm::StringRef(reinterpret_cast<const char *>(data), length);
}

std::string string_copy(const std::uint8_t *data, std::size_t length) {
  return string_ref(data, length).str();
}

} // namespace

extern "C" {

bool taro_write_thin_lto_bitcode(LLVMModuleRef module,
                                 const std::uint8_t *path,
                                 std::size_t path_length) {
  if (module == nullptr)
    return false;
  std::error_code error;
  llvm::raw_fd_ostream output(string_ref(path, path_length), error,
                             llvm::sys::fs::OF_None);
  if (error)
    return false;

  llvm::Module &native_module = *llvm::unwrap(module);
  llvm::ProfileSummaryInfo profile_summary(native_module);
  llvm::ModuleSummaryIndex index = llvm::buildModuleSummaryIndex(
      native_module, {}, &profile_summary);
  llvm::WriteBitcodeToFile(native_module, output, false, &index, true);
  output.flush();
  return !output.has_error();
}

std::uint8_t taro_llvm_global_prefix(LLVMModuleRef module) {
  if (module == nullptr)
    return 0;
  return static_cast<std::uint8_t>(
      llvm::unwrap(module)->getDataLayout().getGlobalPrefix());
}

bool taro_target_machine_uses_global_isel(LLVMTargetMachineRef target_machine) {
  if (target_machine == nullptr)
    return false;
  auto *native_target_machine =
      reinterpret_cast<llvm::TargetMachine *>(target_machine);
  return native_target_machine->Options.EnableGlobalISel;
}

TaroThinLTOCodeGenerator *taro_thin_lto_create() {
  return new (std::nothrow) TaroThinLTOCodeGenerator();
}

void taro_thin_lto_dispose(TaroThinLTOCodeGenerator *codegen) {
  delete codegen;
}

void taro_thin_lto_set_optimization(TaroThinLTOCodeGenerator *codegen,
                                    unsigned ir_level,
                                    unsigned codegen_level) {
  if (codegen == nullptr)
    return;
  codegen->Generator.setOptLevel(std::min(ir_level, 3U));
  codegen->Generator.setCodeGenOptLevel(
      static_cast<llvm::CodeGenOptLevel>(std::min(codegen_level, 3U)));
}

void taro_thin_lto_set_target(TaroThinLTOCodeGenerator *codegen,
                              const std::uint8_t *cpu, std::size_t cpu_length,
                              const std::uint8_t *features,
                              std::size_t features_length) {
  if (codegen == nullptr)
    return;
  codegen->Generator.setCpu(string_copy(cpu, cpu_length));
  codegen->Generator.setAttr(string_copy(features, features_length));
}

void taro_thin_lto_set_cache_dir(TaroThinLTOCodeGenerator *codegen,
                                 const std::uint8_t *path,
                                 std::size_t path_length) {
  if (codegen != nullptr)
    codegen->Generator.setCacheDir(string_copy(path, path_length));
}

void taro_thin_lto_set_output_dir(TaroThinLTOCodeGenerator *codegen,
                                  const std::uint8_t *path,
                                  std::size_t path_length) {
  if (codegen != nullptr)
    codegen->Generator.setGeneratedObjectsDirectory(
        string_copy(path, path_length));
}

void taro_thin_lto_disable_codegen(TaroThinLTOCodeGenerator *codegen,
                                   bool disable) {
  if (codegen != nullptr)
    codegen->Generator.disableCodeGen(disable);
}

void taro_thin_lto_add_module(TaroThinLTOCodeGenerator *codegen,
                              const std::uint8_t *identifier,
                              std::size_t identifier_length,
                              const std::uint8_t *data,
                              std::size_t data_length) {
  if (codegen != nullptr)
    codegen->Generator.addModule(string_ref(identifier, identifier_length),
                                 string_ref(data, data_length));
}

void taro_thin_lto_preserve_symbol(TaroThinLTOCodeGenerator *codegen,
                                   const std::uint8_t *name,
                                   std::size_t name_length) {
  if (codegen != nullptr)
    codegen->Generator.preserveSymbol(string_ref(name, name_length));
}

void taro_thin_lto_cross_reference_symbol(TaroThinLTOCodeGenerator *codegen,
                                          const std::uint8_t *name,
                                          std::size_t name_length) {
  if (codegen != nullptr)
    codegen->Generator.crossReferenceSymbol(string_ref(name, name_length));
}

void taro_thin_lto_process(TaroThinLTOCodeGenerator *codegen) {
  if (codegen != nullptr)
    codegen->Generator.run();
}

std::size_t
taro_thin_lto_object_count(TaroThinLTOCodeGenerator *codegen) {
  if (codegen == nullptr)
    return 0;
  return codegen->Generator.getProducedBinaryFiles().size();
}

const std::uint8_t *
taro_thin_lto_object_path(TaroThinLTOCodeGenerator *codegen,
                          std::size_t index, std::size_t *length) {
  if (codegen == nullptr || length == nullptr)
    return nullptr;
  auto &files = codegen->Generator.getProducedBinaryFiles();
  if (index >= files.size())
    return nullptr;
  const std::string &path = files[index];
  *length = path.size();
  return reinterpret_cast<const std::uint8_t *>(path.data());
}

} // extern "C"
