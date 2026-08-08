#include "llvm/ADT/StringRef.h"
#include "llvm/Analysis/ModuleSummaryAnalysis.h"
#include "llvm/Analysis/ProfileSummaryInfo.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/IR/Module.h"
#include "llvm/LTO/legacy/ThinLTOCodeGenerator.h"
#include "llvm/ObjCopy/ConfigManager.h"
#include "llvm/ObjCopy/ObjCopy.h"
#include "llvm/Object/Binary.h"
#include "llvm/Object/ObjectFile.h"
#include "llvm/Object/StackMapParser.h"
#include "llvm/Object/SymbolSize.h"
#include "llvm/Support/CBindingWrapping.h"
#include "llvm/Support/CodeGen.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/TargetParser/Triple.h"
#include "llvm-c/Core.h"
#include "llvm-c/TargetMachine.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <new>
#include <optional>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

namespace {

struct TaroThinLTOCodeGenerator {
  llvm::ThinLTOCodeGenerator Generator;
};

struct TaroStackMapLocation {
  std::uint8_t Kind = 0;
  std::uint16_t Size = 0;
  std::uint16_t DwarfRegister = 0;
  std::int64_t Value = 0;
};

struct TaroStackMapRecord {
  std::uint64_t ID = 0;
  std::uint32_t InstructionOffset = 0;
  std::size_t FunctionIndex = 0;
  std::vector<TaroStackMapLocation> Locations;
};

struct TaroStackMapFunction {
  std::string Symbol;
  std::uint64_t StackSize = 0;
  std::uint64_t CodeSize = 0;
  std::size_t RecordStart = 0;
  std::size_t RecordCount = 0;
};

struct TaroParsedStackMap {
  std::string Error;
  std::string Architecture;
  std::uint8_t PointerBytes = 0;
  std::vector<TaroStackMapFunction> Functions;
  std::vector<TaroStackMapRecord> Records;
};

struct TaroObjectRewriteResult {
  std::string Error;
};

llvm::StringRef string_ref(const std::uint8_t *data, std::size_t length) {
  return llvm::StringRef(reinterpret_cast<const char *>(data), length);
}

std::string string_copy(const std::uint8_t *data, std::size_t length) {
  return string_ref(data, length).str();
}

template <typename T>
bool checked_add(T Left, T Right, T &Result) {
  if (Right > std::numeric_limits<T>::max() - Left)
    return false;
  Result = Left + Right;
  return true;
}

template <typename T>
bool checked_mul(T Left, T Right, T &Result) {
  if (Left != 0 && Right > std::numeric_limits<T>::max() / Left)
    return false;
  Result = Left * Right;
  return true;
}

bool align_to_eight(std::size_t Value, std::size_t &Result) {
  std::size_t WithPadding = 0;
  if (!checked_add(Value, std::size_t{7}, WithPadding))
    return false;
  Result = WithPadding & ~std::size_t{7};
  return true;
}

template <llvm::endianness Endianness, typename T>
T read_integer(const llvm::ArrayRef<std::uint8_t> Bytes, std::size_t Offset) {
  return llvm::support::endian::read<T, Endianness>(Bytes.data() + Offset);
}

template <llvm::endianness Endianness>
bool validate_stack_map_layout(llvm::ArrayRef<std::uint8_t> Bytes,
                               std::string &Error) {
  using Parser = llvm::StackMapParser<Endianness>;
  if (llvm::Error HeaderError = Parser::validateHeader(Bytes)) {
    Error = llvm::toString(std::move(HeaderError));
    return false;
  }

  const std::size_t FunctionCount =
      read_integer<Endianness, std::uint32_t>(Bytes, 4);
  const std::size_t ConstantCount =
      read_integer<Endianness, std::uint32_t>(Bytes, 8);
  const std::size_t RecordCount =
      read_integer<Endianness, std::uint32_t>(Bytes, 12);

  std::size_t FunctionBytes = 0;
  std::size_t ConstantBytes = 0;
  std::size_t RecordsOffset = 16;
  if (!checked_mul(FunctionCount, std::size_t{24}, FunctionBytes) ||
      !checked_mul(ConstantCount, std::size_t{8}, ConstantBytes) ||
      !checked_add(RecordsOffset, FunctionBytes, RecordsOffset) ||
      !checked_add(RecordsOffset, ConstantBytes, RecordsOffset) ||
      RecordsOffset > Bytes.size()) {
    Error = "stack map function and constant tables exceed the section size";
    return false;
  }

  std::uint64_t FunctionRecordCount = 0;
  for (std::size_t Index = 0; Index < FunctionCount; ++Index) {
    const std::size_t Offset = 16 + Index * 24 + 16;
    const std::uint64_t Count =
        read_integer<Endianness, std::uint64_t>(Bytes, Offset);
    if (Count > std::numeric_limits<std::uint64_t>::max() -
                    FunctionRecordCount) {
      Error = "stack map function record counts overflow";
      return false;
    }
    FunctionRecordCount += Count;
  }
  if (FunctionRecordCount != RecordCount) {
    Error = "stack map function record counts do not match the header";
    return false;
  }

  std::size_t RecordOffset = RecordsOffset;
  for (std::size_t Index = 0; Index < RecordCount; ++Index) {
    std::size_t HeaderEnd = 0;
    if (!checked_add(RecordOffset, std::size_t{16}, HeaderEnd) ||
        HeaderEnd > Bytes.size()) {
      Error = "stack map record header exceeds the section size";
      return false;
    }

    const std::size_t LocationCount =
        read_integer<Endianness, std::uint16_t>(Bytes, RecordOffset + 14);
    std::size_t LocationBytes = 0;
    std::size_t LocationEnd = HeaderEnd;
    if (!checked_mul(LocationCount, std::size_t{12}, LocationBytes) ||
        !checked_add(LocationEnd, LocationBytes, LocationEnd) ||
        LocationEnd > Bytes.size()) {
      Error = "stack map location table exceeds the section size";
      return false;
    }

    std::size_t LiveOutHeader = 0;
    std::size_t LiveOutCountOffset = 0;
    if (!align_to_eight(LocationEnd, LiveOutHeader) ||
        !checked_add(LiveOutHeader, std::size_t{2}, LiveOutCountOffset) ||
        !checked_add(LiveOutCountOffset, std::size_t{2}, LiveOutHeader) ||
        LiveOutHeader > Bytes.size()) {
      Error = "stack map live-out header exceeds the section size";
      return false;
    }

    const std::size_t LiveOutCount = read_integer<Endianness, std::uint16_t>(
        Bytes, LiveOutCountOffset);
    std::size_t LiveOutBytes = 0;
    std::size_t UnalignedRecordEnd = LiveOutHeader;
    if (!checked_mul(LiveOutCount, std::size_t{4}, LiveOutBytes) ||
        !checked_add(UnalignedRecordEnd, LiveOutBytes, UnalignedRecordEnd) ||
        !align_to_eight(UnalignedRecordEnd, RecordOffset) ||
        RecordOffset > Bytes.size()) {
      Error = "stack map live-out table exceeds the section size";
      return false;
    }
  }

  return true;
}

std::optional<std::string>
relocation_symbol(const llvm::object::ObjectFile &Object,
                  const llvm::object::RelocationRef &Relocation,
                  std::string &Error) {
  auto Symbol = Relocation.getSymbol();
  if (Symbol == Object.symbol_end()) {
    Error = "stack map function relocation has no symbol";
    return std::nullopt;
  }
  auto Name = Symbol->getName();
  if (!Name) {
    Error = "failed to read stack map function symbol: " +
            llvm::toString(Name.takeError());
    return std::nullopt;
  }
  llvm::StringRef Normalized = *Name;
  if (Object.isMachO() && Normalized.starts_with("_"))
    Normalized = Normalized.drop_front();
  if (Normalized.empty()) {
    Error = "stack map function relocation has an empty symbol";
    return std::nullopt;
  }
  return Normalized.str();
}

template <llvm::endianness Endianness>
bool parse_stack_map_records(const llvm::ArrayRef<std::uint8_t> Bytes,
                             const llvm::object::ObjectFile &Object,
                             const llvm::object::SectionRef &Section,
                             TaroParsedStackMap &Result) {
  using Parser = llvm::StackMapParser<Endianness>;
  if (!validate_stack_map_layout<Endianness>(Bytes, Result.Error))
    return false;

  Parser StackMap(Bytes);
  std::unordered_map<std::string, std::uint64_t> FunctionSizes;
  for (const auto &[Symbol, Size] : llvm::object::computeSymbolSizes(Object)) {
    auto Name = Symbol.getName();
    if (!Name) {
      llvm::consumeError(Name.takeError());
      continue;
    }
    llvm::StringRef Normalized = *Name;
    if (Object.isMachO() && Normalized.starts_with("_"))
      Normalized = Normalized.drop_front();
    if (Normalized.empty())
      continue;
    auto [Entry, Inserted] = FunctionSizes.emplace(Normalized.str(), Size);
    if (!Inserted && Entry->second != Size) {
      Result.Error = "object contains conflicting sizes for symbol '" +
                     Normalized.str() + "'";
      return false;
    }
  }
  std::unordered_map<std::uint64_t, std::string> FunctionSymbols;
  auto CollectRelocations = [&](const llvm::object::SectionRef &RelocationSection) {
    for (const llvm::object::RelocationRef &Relocation :
         RelocationSection.relocations()) {
      const std::uint64_t Offset = Relocation.getOffset();
      if (Offset < 16 || (Offset - 16) % 24 != 0)
        continue;
      const std::size_t FunctionIndex = (Offset - 16) / 24;
      if (FunctionIndex >= StackMap.getNumFunctions())
        continue;
      auto Symbol = relocation_symbol(Object, Relocation, Result.Error);
      if (!Symbol)
        return false;
      if (!FunctionSymbols.emplace(Offset, std::move(*Symbol)).second) {
        Result.Error = "stack map function address has multiple relocations";
        return false;
      }
    }
    return true;
  };

  // Mach-O exposes relocations through the data section itself. ELF exposes
  // them through a separate `.rel[a].llvm_stackmaps` section whose relocated
  // section points back to the stack-map data.
  if (!CollectRelocations(Section))
    return false;
  for (const llvm::object::SectionRef &Candidate : Object.sections()) {
    if (Candidate == Section)
      continue;
    auto RelocatedSection = Candidate.getRelocatedSection();
    if (!RelocatedSection) {
      llvm::consumeError(RelocatedSection.takeError());
      continue;
    }
    if (*RelocatedSection == Object.section_end() ||
        **RelocatedSection != Section)
      continue;
    if (!CollectRelocations(Candidate))
      return false;
  }

  Result.Functions.reserve(StackMap.getNumFunctions());
  std::size_t RecordStart = 0;
  for (std::size_t Index = 0; Index < StackMap.getNumFunctions(); ++Index) {
    const std::uint64_t RelocationOffset = 16 + Index * 24;
    auto Symbol = FunctionSymbols.find(RelocationOffset);
    if (Symbol == FunctionSymbols.end()) {
      Result.Error = "stack map function address is missing its symbol relocation";
      return false;
    }
    auto Function = StackMap.getFunction(Index);
    const std::uint64_t Count = Function.getRecordCount();
    if (Count > std::numeric_limits<std::size_t>::max() - RecordStart) {
      Result.Error = "stack map function record range overflows";
      return false;
    }
    auto Size = FunctionSizes.find(Symbol->second);
    if (Size == FunctionSizes.end() || Size->second == 0) {
      Result.Error = "stack map function '" + Symbol->second +
                     "' has no non-zero object symbol size";
      return false;
    }
    Result.Functions.push_back(TaroStackMapFunction{
        std::move(Symbol->second), Function.getStackSize(), Size->second,
        RecordStart, static_cast<std::size_t>(Count)});
    RecordStart += static_cast<std::size_t>(Count);
  }

  Result.Records.reserve(StackMap.getNumRecords());
  std::size_t FunctionIndex = 0;
  std::size_t FunctionRecordEnd = Result.Functions.empty()
                                      ? 0
                                      : Result.Functions[0].RecordCount;
  for (std::size_t RecordIndex = 0;
       RecordIndex < StackMap.getNumRecords(); ++RecordIndex) {
    while (FunctionIndex < Result.Functions.size() &&
           RecordIndex >= FunctionRecordEnd) {
      ++FunctionIndex;
      if (FunctionIndex < Result.Functions.size())
        FunctionRecordEnd = Result.Functions[FunctionIndex].RecordStart +
                            Result.Functions[FunctionIndex].RecordCount;
    }
    if (FunctionIndex >= Result.Functions.size()) {
      Result.Error = "stack map record is not owned by a function";
      return false;
    }

    auto SourceRecord = StackMap.getRecord(RecordIndex);
    TaroStackMapRecord Record;
    Record.ID = SourceRecord.getID();
    Record.InstructionOffset = SourceRecord.getInstructionOffset();
    Record.FunctionIndex = FunctionIndex;
    Record.Locations.reserve(SourceRecord.getNumLocations());
    for (auto Location : SourceRecord.locations()) {
      TaroStackMapLocation ParsedLocation;
      ParsedLocation.Kind = static_cast<std::uint8_t>(Location.getKind());
      ParsedLocation.Size = Location.getSizeInBytes();
      ParsedLocation.DwarfRegister = Location.getDwarfRegNum();
      switch (Location.getKind()) {
      case Parser::LocationKind::Direct:
      case Parser::LocationKind::Indirect:
        ParsedLocation.Value = Location.getOffset();
        break;
      case Parser::LocationKind::Constant:
        ParsedLocation.Value = Location.getSmallConstant();
        break;
      case Parser::LocationKind::ConstantIndex: {
        const std::uint32_t ConstantIndex = Location.getConstantIndex();
        if (ConstantIndex >= StackMap.getNumConstants()) {
          Result.Error = "stack map location references an invalid constant";
          return false;
        }
        ParsedLocation.Value =
            static_cast<std::int64_t>(StackMap.getConstant(ConstantIndex).getValue());
        break;
      }
      case Parser::LocationKind::Register:
        break;
      }
      Record.Locations.push_back(ParsedLocation);
    }
    Result.Records.push_back(std::move(Record));
  }

  return true;
}

TaroParsedStackMap *parse_stack_map_object(const std::uint8_t *Path,
                                           std::size_t PathLength) {
  auto *Result = new (std::nothrow) TaroParsedStackMap();
  if (Result == nullptr)
    return nullptr;

  auto ObjectOrError = llvm::object::ObjectFile::createObjectFile(
      string_ref(Path, PathLength));
  if (!ObjectOrError) {
    Result->Error = "failed to open stack map object: " +
                    llvm::toString(ObjectOrError.takeError());
    return Result;
  }
  llvm::object::OwningBinary<llvm::object::ObjectFile> OwningObject =
      std::move(*ObjectOrError);
  const llvm::object::ObjectFile &Object = *OwningObject.getBinary();

  std::optional<llvm::object::SectionRef> StackMapSection;
  for (const llvm::object::SectionRef &Section : Object.sections()) {
    auto Name = Section.getName();
    if (!Name) {
      Result->Error = "failed to read object section name: " +
                      llvm::toString(Name.takeError());
      return Result;
    }
    if (*Name != "__llvm_stackmaps" && *Name != ".llvm_stackmaps")
      continue;
    if (StackMapSection) {
      Result->Error = "object contains multiple LLVM stack map sections";
      return Result;
    }
    StackMapSection = Section;
  }
  if (!StackMapSection) {
    Result->Error = "object does not contain an LLVM stack map section";
    return Result;
  }

  auto Contents = StackMapSection->getContents();
  if (!Contents) {
    Result->Error = "failed to read LLVM stack map section: " +
                    llvm::toString(Contents.takeError());
    return Result;
  }
  const auto *Data = reinterpret_cast<const std::uint8_t *>(Contents->data());
  llvm::ArrayRef<std::uint8_t> Bytes(Data, Contents->size());

  Result->Architecture =
      llvm::Triple::getArchTypeName(Object.getArch()).str();
  Result->PointerBytes = Object.getBytesInAddress();
  const bool Parsed = Object.isLittleEndian()
                          ? parse_stack_map_records<llvm::endianness::little>(
                                Bytes, Object, *StackMapSection, *Result)
                          : parse_stack_map_records<llvm::endianness::big>(
                                Bytes, Object, *StackMapSection, *Result);
  if (!Parsed) {
    Result->Functions.clear();
    Result->Records.clear();
  }
  return Result;
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

TaroParsedStackMap *taro_stack_map_parse_object(const std::uint8_t *path,
                                                std::size_t path_length) {
  if (path == nullptr)
    return nullptr;
  return parse_stack_map_object(path, path_length);
}

TaroObjectRewriteResult *
taro_stack_map_strip_object(const std::uint8_t *input_path,
                            std::size_t input_path_length,
                            const std::uint8_t *output_path,
                            std::size_t output_path_length) {
  auto *Result = new (std::nothrow) TaroObjectRewriteResult();
  if (Result == nullptr)
    return nullptr;
  if (input_path == nullptr || output_path == nullptr) {
    Result->Error = "stack-map strip path is null";
    return Result;
  }

  auto Input = llvm::object::createBinary(
      string_ref(input_path, input_path_length));
  if (!Input) {
    Result->Error = llvm::toString(Input.takeError());
    return Result;
  }

  llvm::objcopy::ConfigManager Config;
  Config.Common.InputFilename = string_ref(input_path, input_path_length);
  Config.Common.OutputFilename = string_ref(output_path, output_path_length);
  auto PropagateError = [](llvm::Error Error) { return Error; };
  for (llvm::StringRef Name : {
           llvm::StringRef("__LLVM_STACKMAPS,__llvm_stackmaps"),
           llvm::StringRef("__llvm_stackmaps"),
           llvm::StringRef(".llvm_stackmaps")}) {
    if (llvm::Error Error = Config.Common.ToRemove.addMatcher(
            llvm::objcopy::NameOrPattern::create(
                Name, llvm::objcopy::MatchStyle::Literal, PropagateError))) {
      Result->Error = llvm::toString(std::move(Error));
      return Result;
    }
  }

  std::error_code FileError;
  llvm::raw_fd_ostream Output(string_ref(output_path, output_path_length),
                             FileError, llvm::sys::fs::OF_None);
  if (FileError) {
    Result->Error = FileError.message();
    return Result;
  }
  if (llvm::Error Error = llvm::objcopy::executeObjcopyOnBinary(
          Config, *Input->getBinary(), Output)) {
    Result->Error = llvm::toString(std::move(Error));
    return Result;
  }
  Output.flush();
  if (Output.has_error())
    Result->Error = "failed to flush stripped stack-map object";
  return Result;
}

void taro_object_rewrite_dispose(TaroObjectRewriteResult *result) {
  delete result;
}

bool taro_object_rewrite_is_valid(const TaroObjectRewriteResult *result) {
  return result != nullptr && result->Error.empty();
}

const std::uint8_t *
taro_object_rewrite_error(const TaroObjectRewriteResult *result,
                          std::size_t *length) {
  if (result == nullptr || length == nullptr)
    return nullptr;
  *length = result->Error.size();
  return reinterpret_cast<const std::uint8_t *>(result->Error.data());
}

void taro_stack_map_dispose(TaroParsedStackMap *stack_map) {
  delete stack_map;
}

bool taro_stack_map_is_valid(const TaroParsedStackMap *stack_map) {
  return stack_map != nullptr && stack_map->Error.empty();
}

const std::uint8_t *
taro_stack_map_error(const TaroParsedStackMap *stack_map,
                     std::size_t *length) {
  if (stack_map == nullptr || length == nullptr)
    return nullptr;
  *length = stack_map->Error.size();
  return reinterpret_cast<const std::uint8_t *>(stack_map->Error.data());
}

const std::uint8_t *
taro_stack_map_architecture(const TaroParsedStackMap *stack_map,
                            std::size_t *length) {
  if (stack_map == nullptr || length == nullptr)
    return nullptr;
  *length = stack_map->Architecture.size();
  return reinterpret_cast<const std::uint8_t *>(
      stack_map->Architecture.data());
}

std::uint8_t
taro_stack_map_pointer_bytes(const TaroParsedStackMap *stack_map) {
  return stack_map == nullptr ? 0 : stack_map->PointerBytes;
}

std::size_t
taro_stack_map_function_count(const TaroParsedStackMap *stack_map) {
  return stack_map == nullptr ? 0 : stack_map->Functions.size();
}

const std::uint8_t *
taro_stack_map_function_symbol(const TaroParsedStackMap *stack_map,
                               std::size_t index, std::size_t *length) {
  if (stack_map == nullptr || length == nullptr ||
      index >= stack_map->Functions.size())
    return nullptr;
  const std::string &Symbol = stack_map->Functions[index].Symbol;
  *length = Symbol.size();
  return reinterpret_cast<const std::uint8_t *>(Symbol.data());
}

std::uint64_t
taro_stack_map_function_stack_size(const TaroParsedStackMap *stack_map,
                                   std::size_t index) {
  if (stack_map == nullptr || index >= stack_map->Functions.size())
    return 0;
  return stack_map->Functions[index].StackSize;
}

std::uint64_t
taro_stack_map_function_code_size(const TaroParsedStackMap *stack_map,
                                  std::size_t index) {
  if (stack_map == nullptr || index >= stack_map->Functions.size())
    return 0;
  return stack_map->Functions[index].CodeSize;
}

std::size_t
taro_stack_map_function_record_start(const TaroParsedStackMap *stack_map,
                                     std::size_t index) {
  if (stack_map == nullptr || index >= stack_map->Functions.size())
    return 0;
  return stack_map->Functions[index].RecordStart;
}

std::size_t
taro_stack_map_function_record_count(const TaroParsedStackMap *stack_map,
                                     std::size_t index) {
  if (stack_map == nullptr || index >= stack_map->Functions.size())
    return 0;
  return stack_map->Functions[index].RecordCount;
}

std::size_t taro_stack_map_record_count(const TaroParsedStackMap *stack_map) {
  return stack_map == nullptr ? 0 : stack_map->Records.size();
}

std::uint64_t taro_stack_map_record_id(const TaroParsedStackMap *stack_map,
                                       std::size_t index) {
  if (stack_map == nullptr || index >= stack_map->Records.size())
    return 0;
  return stack_map->Records[index].ID;
}

std::uint32_t
taro_stack_map_record_instruction_offset(const TaroParsedStackMap *stack_map,
                                         std::size_t index) {
  if (stack_map == nullptr || index >= stack_map->Records.size())
    return 0;
  return stack_map->Records[index].InstructionOffset;
}

std::size_t
taro_stack_map_record_function_index(const TaroParsedStackMap *stack_map,
                                     std::size_t index) {
  if (stack_map == nullptr || index >= stack_map->Records.size())
    return 0;
  return stack_map->Records[index].FunctionIndex;
}

std::size_t
taro_stack_map_location_count(const TaroParsedStackMap *stack_map,
                              std::size_t record_index) {
  if (stack_map == nullptr || record_index >= stack_map->Records.size())
    return 0;
  return stack_map->Records[record_index].Locations.size();
}

std::uint8_t taro_stack_map_location_kind(const TaroParsedStackMap *stack_map,
                                          std::size_t record_index,
                                          std::size_t location_index) {
  if (stack_map == nullptr || record_index >= stack_map->Records.size() ||
      location_index >= stack_map->Records[record_index].Locations.size())
    return 0;
  return stack_map->Records[record_index].Locations[location_index].Kind;
}

std::uint16_t taro_stack_map_location_size(const TaroParsedStackMap *stack_map,
                                           std::size_t record_index,
                                           std::size_t location_index) {
  if (stack_map == nullptr || record_index >= stack_map->Records.size() ||
      location_index >= stack_map->Records[record_index].Locations.size())
    return 0;
  return stack_map->Records[record_index].Locations[location_index].Size;
}

std::uint16_t
taro_stack_map_location_dwarf_register(const TaroParsedStackMap *stack_map,
                                       std::size_t record_index,
                                       std::size_t location_index) {
  if (stack_map == nullptr || record_index >= stack_map->Records.size() ||
      location_index >= stack_map->Records[record_index].Locations.size())
    return 0;
  return stack_map->Records[record_index]
      .Locations[location_index]
      .DwarfRegister;
}

std::int64_t
taro_stack_map_location_value(const TaroParsedStackMap *stack_map,
                              std::size_t record_index,
                              std::size_t location_index) {
  if (stack_map == nullptr || record_index >= stack_map->Records.size() ||
      location_index >= stack_map->Records[record_index].Locations.size())
    return 0;
  return stack_map->Records[record_index].Locations[location_index].Value;
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
