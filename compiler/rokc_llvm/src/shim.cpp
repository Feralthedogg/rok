// C ABI over the statically linked LLVM / MLIR / lld that rokc uses.
// Every entry point reports failure as text in `err`; buffers handed out
// are malloc'd and released with rok_llvm_free.

#include "lld/Common/Driver.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/MC/TargetRegistry.h"
#include "llvm/Object/ArchiveWriter.h"
#include "llvm/Object/COFFImportFile.h"
#include "llvm/Object/COFFModuleDefinition.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetOptions.h"
#include "llvm/TargetParser/Host.h"
#include "llvm/TargetParser/Triple.h"
#include "llvm/Transforms/Utils/SplitModule.h"
#include "llvm/Support/LLVMDriver.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/Diagnostics.h"
#include "mlir/IR/MLIRContext.h"
#include "mlir/InitAllDialects.h"
#include "mlir/InitAllExtensions.h"
#include "mlir/InitAllPasses.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "mlir/Pass/PassRegistry.h"
#include "mlir/Target/LLVMIR/Dialect/All.h"
#include "mlir/Target/LLVMIR/Export.h"
#include "mlir/Tools/Plugins/DialectPlugin.h"
#include "mlir/Tools/Plugins/PassPlugin.h"

#include <cstdlib>
#include <cstring>
#include <mutex>
#include <optional>
#include <string>
#include <thread>
#include <vector>

LLD_HAS_DRIVER(macho)
LLD_HAS_DRIVER(elf)
LLD_HAS_DRIVER(coff)
LLD_HAS_DRIVER(mingw)
LLD_HAS_DRIVER(wasm)

int dsymutil_main(int argc, char **argv, const llvm::ToolContext &);

extern "C" {

struct RokBuf {
  char *ptr;
  size_t len;
};

// opt: 0..3, 's' (Os), 'z' (Oz). emit: 0 LLVM IR text, 1 asm, 2 object.
struct RokCompile {
  const char *triple;
  const char *cpu;
  const char *features;
  int opt;
  int emit;
  // rok_tls_* globals use the initial-exec TLS model (spec 8.3.8).
  int tls_initial_exec;
  // A textual MLIR pass pipeline on builtin.module, mlir-opt syntax
  // without the anchor: "canonicalize,cse,convert-scf-to-cf,...".
  const char *mlir_pipeline;
  const char *const *dialect_plugins;
  size_t n_dialect_plugins;
  const char *const *pass_plugins;
  size_t n_pass_plugins;
  // Objects to split the optimized module into, compiled in parallel
  // (`out` holds this many); 1 for one object, an IR text or assembly.
  size_t parts;
};

void rok_llvm_free(RokBuf *b) {
  free(b->ptr);
  b->ptr = nullptr;
  b->len = 0;
}

} // extern "C"

namespace {

void put(RokBuf *b, llvm::StringRef s) {
  b->ptr = static_cast<char *>(malloc(s.size() + 1));
  memcpy(b->ptr, s.data(), s.size());
  b->ptr[s.size()] = 0;
  b->len = s.size();
}

int fail(RokBuf *err, llvm::StringRef msg) {
  put(err, msg);
  return 1;
}

void init_llvm() {
  static std::once_flag once;
  std::call_once(once, [] {
    llvm::InitializeAllTargetInfos();
    llvm::InitializeAllTargets();
    llvm::InitializeAllTargetMCs();
    llvm::InitializeAllAsmPrinters();
    llvm::InitializeAllAsmParsers();
  });
}

// Pass names, like mlir-opt's. Plugins add theirs under the same lock.
std::mutex pass_registry_lock;

void init_passes() {
  static std::once_flag once;
  std::call_once(once, [] { mlir::registerAllPasses(); });
}

std::unique_ptr<llvm::TargetMachine>
target_machine(const RokCompile &o, std::string &error) {
  init_llvm();
  llvm::Triple triple(o.triple);
  const llvm::Target *t = llvm::TargetRegistry::lookupTarget(triple, error);
  if (!t)
    return nullptr;
  llvm::TargetOptions opts;
  opts.UseInitArray = true;
  opts.EmulatedTLS = triple.hasDefaultEmulatedTLS();
  // Lets the link drop what nothing references; Mach-O strips by symbol.
  opts.FunctionSections = opts.DataSections = !triple.isOSBinFormatMachO();
  llvm::CodeGenOptLevel cg;
  switch (o.opt) {
  case 0:
    cg = llvm::CodeGenOptLevel::None;
    break;
  case 1:
    cg = llvm::CodeGenOptLevel::Less;
    break;
  case 3:
    cg = llvm::CodeGenOptLevel::Aggressive;
    break;
  default:
    cg = llvm::CodeGenOptLevel::Default;
  }
  std::unique_ptr<llvm::TargetMachine> tm(t->createTargetMachine(
      triple, o.cpu, o.features, opts, llvm::Reloc::PIC_, std::nullopt, cg));
  if (!tm) {
    error = "cannot create a target machine for " + triple.str();
    return nullptr;
  }
  // One instruction selector at every level: at -O0 AArch64 would pick
  // GlobalISel, which falls back to SelectionDAG per function, and the
  // two lay out sub-word aggregate arguments on the stack differently.
  tm->setGlobalISel(false);
  return tm;
}

// What clang -O<n> runs on an IR input (shouldEnableVectorizerAtOLevel,
// -funroll-loops).
void optimize(llvm::Module &m, llvm::TargetMachine &tm, int opt) {
  llvm::PipelineTuningOptions pto;
  bool vec = opt >= 2 || opt == 's';
  pto.LoopVectorization = vec;
  pto.SLPVectorization = vec || opt == 'z';
  pto.LoopUnrolling = opt >= 2 || opt == 's';
  pto.LoopInterleaving = pto.LoopUnrolling;
  llvm::LoopAnalysisManager lam;
  llvm::FunctionAnalysisManager fam;
  llvm::CGSCCAnalysisManager cgam;
  llvm::ModuleAnalysisManager mam;
  llvm::PassBuilder pb(&tm, pto);
  pb.registerModuleAnalyses(mam);
  pb.registerCGSCCAnalyses(cgam);
  pb.registerFunctionAnalyses(fam);
  pb.registerLoopAnalyses(lam);
  pb.crossRegisterProxies(lam, fam, cgam, mam);
  llvm::OptimizationLevel level = llvm::OptimizationLevel::O2;
  switch (opt) {
  case 0:
    level = llvm::OptimizationLevel::O0;
    break;
  case 1:
    level = llvm::OptimizationLevel::O1;
    break;
  case 3:
    level = llvm::OptimizationLevel::O3;
    break;
  case 's':
    level = llvm::OptimizationLevel::Os;
    break;
  case 'z':
    level = llvm::OptimizationLevel::Oz;
    break;
  }
  llvm::ModulePassManager mpm = opt == 0
                                    ? pb.buildO0DefaultPipeline(level)
                                    : pb.buildPerModuleDefaultPipeline(level);
  mpm.run(m, mam);
}

int codegen(llvm::Module &m, llvm::TargetMachine &tm,
            llvm::CodeGenFileType kind, RokBuf *out, RokBuf *err) {
  llvm::SmallString<0> buf;
  llvm::raw_svector_ostream os(buf);
  llvm::legacy::PassManager cg;
  if (tm.addPassesToEmitFile(cg, os, nullptr, kind))
    return fail(err, "the target cannot emit this file type");
  cg.run(m);
  put(out, buf.str());
  return 0;
}

// The module's target is the requested one (as clang -target overrides
// the triple of an IR input), then the requested output.
int finish(llvm::Module &m, const RokCompile &o, RokBuf *out, RokBuf *err) {
  if (o.tls_initial_exec) {
    for (llvm::GlobalVariable &g : m.globals())
      if (g.isThreadLocal() && g.getName().starts_with("rok_tls_"))
        g.setThreadLocalMode(llvm::GlobalValue::InitialExecTLSModel);
  }
  if (o.emit == 0) {
    std::string text;
    llvm::raw_string_ostream os(text);
    m.print(os, nullptr);
    put(out, text);
    return 0;
  }
  std::string error;
  auto tm = target_machine(o, error);
  if (!tm)
    return fail(err, error);
  m.setTargetTriple(tm->getTargetTriple());
  m.setDataLayout(tm->createDataLayout());
  if (tm->getTargetTriple().isOSWindows()) {
    // Windows debuggers read CodeView (lld-link writes it into a PDB).
    if (m.getModuleFlag("Debug Info Version") && !m.getModuleFlag("CodeView"))
      m.addModuleFlag(llvm::Module::Warning, "CodeView", 1);
    // Every function in .pdata / .xdata: without an entry the unwinder
    // takes a function for a leaf and cannot walk past it.
    for (llvm::Function &f : m)
      if (!f.isDeclaration())
        f.setUWTableKind(llvm::UWTableKind::Async);
  }
  {
    std::string msg;
    llvm::raw_string_ostream os(msg);
    if (llvm::verifyModule(m, &os))
      return fail(err, "invalid LLVM IR:\n" + msg);
  }
  optimize(m, *tm, o.opt);
  auto kind = o.emit == 1 ? llvm::CodeGenFileType::AssemblyFile
                          : llvm::CodeGenFileType::ObjectFile;
  if (o.parts <= 1 || o.emit != 2)
    return codegen(m, *tm, kind, out, err);
  // Each part travels as bitcode into a context of its own: modules of
  // one context cannot be compiled in parallel.
  std::vector<llvm::SmallString<0>> bitcode;
  llvm::SplitModule(
      m, o.parts,
      [&](std::unique_ptr<llvm::Module> part) {
        llvm::SmallString<0> bc;
        llvm::raw_svector_ostream os(bc);
        llvm::WriteBitcodeToFile(*part, os);
        bitcode.push_back(std::move(bc));
      },
      true);
  std::vector<int> rc(bitcode.size());
  std::vector<std::thread> threads;
  for (size_t i = 0; i < bitcode.size(); ++i)
    threads.emplace_back([&, i] {
      llvm::LLVMContext ctx;
      auto part = llvm::parseBitcodeFile(
          llvm::MemoryBufferRef(bitcode[i].str(), "part"), ctx);
      if (!part) {
        rc[i] = fail(&out[i], llvm::toString(part.takeError()));
        return;
      }
      std::string error;
      auto ptm = target_machine(o, error);
      rc[i] = ptm ? codegen(**part, *ptm, kind, &out[i], &out[i])
                  : fail(&out[i], error);
    });
  for (auto &t : threads)
    t.join();
  for (size_t i = 0; i < rc.size(); ++i)
    if (rc[i]) {
      put(err, llvm::StringRef(out[i].ptr, out[i].len));
      return 1;
    }
  return 0;
}

} // namespace

extern "C" {

// The MLIR module `src` (standard dialects) through `o.mlir_pipeline`
// into LLVM IR, then `finish`.
int rok_llvm_compile_mlir(const char *src, size_t len, const RokCompile *o,
                          RokBuf *out, RokBuf *err) {
  mlir::DialectRegistry registry;
  mlir::registerAllDialects(registry);
  mlir::registerAllExtensions(registry);
  mlir::registerAllToLLVMIRTranslations(registry);
  for (size_t i = 0; i < o->n_dialect_plugins; ++i) {
    auto p = mlir::DialectPlugin::load(o->dialect_plugins[i]);
    if (!p)
      return fail(err, "Failed to load dialect plugin " +
                           std::string(o->dialect_plugins[i]) + ": " +
                           llvm::toString(p.takeError()));
    p->registerDialectRegistryCallbacks(registry);
  }
  init_passes();
  {
    std::lock_guard<std::mutex> lock(pass_registry_lock);
    for (size_t i = 0; i < o->n_pass_plugins; ++i) {
      auto p = mlir::PassPlugin::load(o->pass_plugins[i]);
      if (!p)
        return fail(err, "Failed to load pass plugin " +
                             std::string(o->pass_plugins[i]) + ": " +
                             llvm::toString(p.takeError()));
      p->registerPassRegistryCallbacks();
    }
  }
  mlir::MLIRContext ctx(registry, mlir::MLIRContext::Threading::DISABLED);

  std::string diag;
  llvm::raw_string_ostream diag_os(diag);
  llvm::SourceMgr sm;
  sm.AddNewSourceBuffer(
      llvm::MemoryBuffer::getMemBufferCopy(llvm::StringRef(src, len), "<stdin>"),
      llvm::SMLoc());
  mlir::SourceMgrDiagnosticHandler handler(sm, &ctx, diag_os);

  mlir::OwningOpRef<mlir::ModuleOp> module =
      mlir::parseSourceFile<mlir::ModuleOp>(sm, &ctx);
  if (!module)
    return fail(err, diag);
  mlir::PassManager pm(&ctx, mlir::ModuleOp::getOperationName());
  if (mlir::failed(mlir::parsePassPipeline(o->mlir_pipeline, pm, diag_os)))
    return fail(err, diag);
  if (mlir::failed(pm.run(*module)))
    return fail(err, diag);

  llvm::LLVMContext llctx;
  auto m = mlir::translateModuleToLLVMIR(*module, llctx);
  if (!m)
    return fail(err, diag.empty() ? "cannot translate MLIR to LLVM IR" : diag);
  return finish(*m, *o, out, err);
}

// LLVM IR text `src` through `finish`.
int rok_llvm_compile_ir(const char *src, size_t len, const RokCompile *o,
                        RokBuf *out, RokBuf *err) {
  llvm::LLVMContext ctx;
  llvm::SMDiagnostic d;
  // The IR lexer reads up to a NUL.
  auto buf = llvm::MemoryBuffer::getMemBufferCopy(llvm::StringRef(src, len),
                                                  "<stdin>");
  auto m = llvm::parseIR(buf->getMemBufferRef(), d, ctx);
  if (!m) {
    std::string msg;
    llvm::raw_string_ostream os(msg);
    d.print("rokc", os, false);
    return fail(err, msg);
  }
  return finish(*m, *o, out, err);
}

// The data layout LLVM uses for o->triple / o->cpu.
int rok_llvm_data_layout(const RokCompile *o, RokBuf *out, RokBuf *err) {
  std::string error;
  auto tm = target_machine(*o, error);
  if (!tm)
    return fail(err, error);
  put(out, tm->createDataLayout().getStringRepresentation());
  return 0;
}

// The triple LLVM was configured to run on.
void rok_llvm_process_triple(RokBuf *out) {
  put(out, llvm::sys::getProcessTriple());
}

// dsymutil's command line (argv[0] is "dsymutil"); it reports on stderr.
int rok_llvm_dsymutil(const char *const *argv, size_t argc) {
  static std::mutex lock;
  std::lock_guard<std::mutex> guard(lock);
  std::vector<char *> args;
  for (size_t i = 0; i < argc; ++i)
    args.push_back(const_cast<char *>(argv[i]));
  args.push_back(nullptr);
  llvm::ToolContext ctx{};
  return dsymutil_main(static_cast<int>(argc), args.data(), ctx);
}

// lld with argv[0] naming the flavor (ld64.lld, ld.lld, lld-link,
// wasm-ld). Its output goes to `log`. Returns lld's exit code.
int rok_llvm_lld(const char *const *argv, size_t argc, RokBuf *log) {
  static std::mutex lock; // lld keeps per-link globals
  std::lock_guard<std::mutex> guard(lock);
  std::string text;
  llvm::raw_string_ostream os(text);
  lld::Result r = lld::lldMain(llvm::ArrayRef<const char *>(argv, argc), os,
                               os, LLD_ALL_DRIVERS);
  put(log, text);
  return r.retCode;
}

// An archive of the files `members` with a symbol table; `kind` 0 GNU,
// 1 BSD (Darwin), 2 COFF.
int rok_llvm_write_archive(const char *path, const char *const *members,
                           size_t n, int kind, RokBuf *err) {
  init_llvm();
  std::vector<llvm::NewArchiveMember> ms;
  for (size_t i = 0; i < n; ++i) {
    auto m = llvm::NewArchiveMember::getFile(members[i], true);
    if (!m)
      return fail(err, llvm::toString(m.takeError()));
    // Named by the file alone, as ar names it.
    m->MemberName = llvm::sys::path::filename(members[i]);
    ms.push_back(std::move(*m));
  }
  auto format = kind == 1   ? llvm::object::Archive::K_DARWIN
                : kind == 2 ? llvm::object::Archive::K_COFF
                            : llvm::object::Archive::K_GNU;
  if (auto e = llvm::writeArchive(path, ms, llvm::SymtabWritingMode::NormalSymtab,
                                  format, true, false))
    return fail(err, llvm::toString(std::move(e)));
  return 0;
}

// The import library `path` of a module definition (`.def`, mingw-w64
// syntax) for COFF machine type `machine`. x86 names are decorated
// (`_f`, stdcall `_f@8`) and import undecorated (llvm-dlltool -k).
int rok_llvm_import_lib(const char *def, size_t len, uint16_t machine_type,
                        const char *path, RokBuf *err) {
  auto machine = static_cast<llvm::COFF::MachineTypes>(machine_type);
  bool x86 = machine == llvm::COFF::IMAGE_FILE_MACHINE_I386;
  auto parsed = llvm::object::parseCOFFModuleDefinition(
      llvm::MemoryBufferRef(llvm::StringRef(def, len), path), machine, true,
      x86);
  if (!parsed)
    return fail(err, llvm::toString(parsed.takeError()));
  if (x86)
    for (auto &e : parsed->Exports) {
      if (!e.ImportName.empty() || (!e.Name.empty() && e.Name[0] == '?'))
        continue;
      e.SymbolName = e.Name;
      e.Name = e.Name.substr(0, e.Name.find('@', 1));
    }
  if (auto e = llvm::object::writeImportLibrary(parsed->OutputFile, path,
                                                parsed->Exports, machine, true))
    return fail(err, llvm::toString(std::move(e)));
  return 0;
}

} // extern "C"
