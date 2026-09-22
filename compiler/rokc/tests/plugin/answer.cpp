// A dialect and pass plugin built against rokc's own MLIR: its MLIR
// symbols stay undefined and bind to rokc's at load time (Windows: through
// rokc.lib, rokc.exe's import library). docs/mlir-plugins.md builds it.
//
//   rokt.answer : () -> i32       the dialect's one op
//   --rokt-lower                  rewrites it to `arith.constant 42`

#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/Dialect.h"
#include "mlir/IR/OpDefinition.h"
#include "mlir/IR/PatternMatch.h"
#include "mlir/Pass/Pass.h"
#include "mlir/Tools/Plugins/DialectPlugin.h"
#include "mlir/Tools/Plugins/PassPlugin.h"
#include "llvm/Config/llvm-config.h"

using namespace mlir;

namespace rokt {

struct AnswerOp
    : Op<AnswerOp, OpTrait::ZeroRegions, OpTrait::OneResult,
         OpTrait::OneTypedResult<IntegerType>::Impl, OpTrait::ZeroSuccessors,
         OpTrait::ZeroOperands> {
  using Op::Op;
  static StringRef getOperationName() { return "rokt.answer"; }
  static ArrayRef<StringRef> getAttributeNames() { return {}; }
};

struct RoktDialect : Dialect {
  explicit RoktDialect(MLIRContext *ctx)
      : Dialect(getDialectNamespace(), ctx, TypeID::get<RoktDialect>()) {
    addOperations<AnswerOp>();
  }
  static StringRef getDialectNamespace() { return "rokt"; }
};

struct LowerPass : PassWrapper<LowerPass, OperationPass<ModuleOp>> {
  StringRef getArgument() const final { return "rokt-lower"; }
  StringRef getDescription() const final { return "rokt.answer to 42"; }
  void getDependentDialects(DialectRegistry &r) const final {
    r.insert<arith::ArithDialect>();
  }
  void runOnOperation() final {
    getOperation().walk([](AnswerOp op) {
      OpBuilder b(op);
      auto c = arith::ConstantOp::create(
          b, op.getLoc(), b.getIntegerAttr(op.getType(), 42));
      op->getResult(0).replaceAllUsesWith(c.getResult());
      op->erase();
    });
  }
};

} // namespace rokt

extern "C" LLVM_ATTRIBUTE_WEAK LLVM_ALWAYS_EXPORT DialectPluginLibraryInfo
mlirGetDialectPluginInfo() {
  return {MLIR_PLUGIN_API_VERSION, "rokt", LLVM_VERSION_STRING,
          [](DialectRegistry *r) { r->insert<rokt::RoktDialect>(); }};
}

extern "C" LLVM_ATTRIBUTE_WEAK LLVM_ALWAYS_EXPORT PassPluginLibraryInfo
mlirGetPassPluginInfo() {
  return {MLIR_PLUGIN_API_VERSION, "rokt", LLVM_VERSION_STRING,
          [] { PassRegistration<rokt::LowerPass>(); }};
}
