module {
  func.func @pick(%arg0: i1) -> !llvm.struct<(i32, i32)> {
    %p0 = memref.alloca() : memref<i1>
    %0 = llvm.mlir.constant(1 : i32) : i32
    %p1 = llvm.alloca %0 x !llvm.struct<(i32, i32)> : (i32) -> !llvm.ptr
    %p2 = llvm.alloca %0 x !llvm.struct<(i32, i32)> : (i32) -> !llvm.ptr
    memref.store %arg0, %p0[] : memref<i1>
    %1 = memref.load %p0[] : memref<i1>
    cf.cond_br %1, ^bb1, ^bb2
  ^bb1:
    %2 = llvm.mlir.undef : !llvm.struct<(i32, i32)>
    %3 = arith.constant 0 : i32
    %4 = llvm.insertvalue %3, %2[0] : !llvm.struct<(i32, i32)>
    %5 = arith.constant 10 : i32
    %6 = llvm.insertvalue %5, %4[1] : !llvm.struct<(i32, i32)>
    llvm.store %6, %p1 : !llvm.struct<(i32, i32)>, !llvm.ptr
    %7 = llvm.load %p1 : !llvm.ptr -> !llvm.struct<(i32, i32)>
    func.return %7 : !llvm.struct<(i32, i32)>
  ^bb2:
    %8 = llvm.mlir.undef : !llvm.struct<(i32, i32)>
    %9 = arith.constant 1 : i32
    %10 = llvm.insertvalue %9, %8[0] : !llvm.struct<(i32, i32)>
    %11 = arith.constant 0 : i32
    %12 = llvm.insertvalue %11, %10[1] : !llvm.struct<(i32, i32)>
    llvm.store %12, %p2 : !llvm.struct<(i32, i32)>, !llvm.ptr
    %13 = llvm.load %p2 : !llvm.ptr -> !llvm.struct<(i32, i32)>
    func.return %13 : !llvm.struct<(i32, i32)>
  }
  func.func @unwrap_or_zero(%arg0: i1) -> i32 {
    %p0 = memref.alloca() : memref<i1>
    %p1 = memref.alloca() : memref<i32>
    %p2 = memref.alloca() : memref<i32>
    %0 = llvm.mlir.constant(1 : i32) : i32
    %p3 = llvm.alloca %0 x !llvm.struct<(i32, i32)> : (i32) -> !llvm.ptr
    %p5 = memref.alloca() : memref<i32>
    %p6 = memref.alloca() : memref<i1>
    %p7 = memref.alloca() : memref<i32>
    memref.store %arg0, %p0[] : memref<i1>
    %2 = memref.load %p0[] : memref<i1>
    %1 = func.call @pick(%2) : (i1) -> !llvm.struct<(i32, i32)>
    llvm.store %1, %p3 : !llvm.struct<(i32, i32)>, !llvm.ptr
    %3 = llvm.load %p3 : !llvm.ptr -> !llvm.struct<(i32, i32)>
    %4 = llvm.extractvalue %3[0] : !llvm.struct<(i32, i32)>
    memref.store %4, %p5[] : memref<i32>
    %6 = memref.load %p5[] : memref<i32>
    %7 = arith.constant 0 : i32
    %5 = arith.cmpi eq, %6, %7 : i32
    memref.store %5, %p6[] : memref<i1>
    %8 = memref.load %p6[] : memref<i1>
    cf.cond_br %8, ^bb2, ^bb3
  ^bb1(%9: i32):
    memref.store %9, %p2[] : memref<i32>
    %10 = memref.load %p2[] : memref<i32>
    func.return %10 : i32
  ^bb2:
    %11 = llvm.load %p3 : !llvm.ptr -> !llvm.struct<(i32, i32)>
    %12 = llvm.extractvalue %11[1] : !llvm.struct<(i32, i32)>
    memref.store %12, %p7[] : memref<i32>
    %13 = memref.load %p7[] : memref<i32>
    memref.store %13, %p1[] : memref<i32>
    %14 = memref.load %p1[] : memref<i32>
    cf.br ^bb1(%14 : i32)
  ^bb3:
    cf.br ^bb4
  ^bb4:
    %15 = arith.constant 0 : i32
    func.return %15 : i32
  ^bb5:
    llvm.unreachable
  }
  func.func @rok_user_main() -> i32 {
    %p0 = memref.alloca() : memref<i32>
    %p1 = memref.alloca() : memref<i32>
    %p2 = memref.alloca() : memref<i32>
    %p3 = memref.alloca() : memref<i32>
    %p4 = memref.alloca() : memref<i32>
    %0 = arith.constant 0 : i32
    memref.store %0, %p0[] : memref<i32>
    %2 = arith.constant 1 : i1
    %1 = func.call @unwrap_or_zero(%2) : (i1) -> i32
    memref.store %1, %p1[] : memref<i32>
    %4 = memref.load %p0[] : memref<i32>
    %5 = memref.load %p1[] : memref<i32>
    %3 = arith.addi %4, %5 : i32
    memref.store %3, %p0[] : memref<i32>
    %7 = arith.constant 0 : i1
    %6 = func.call @unwrap_or_zero(%7) : (i1) -> i32
    memref.store %6, %p2[] : memref<i32>
    %9 = memref.load %p0[] : memref<i32>
    %10 = memref.load %p2[] : memref<i32>
    %8 = arith.addi %9, %10 : i32
    memref.store %8, %p0[] : memref<i32>
    %12 = arith.constant 1 : i1
    %11 = func.call @unwrap_or_zero(%12) : (i1) -> i32
    memref.store %11, %p3[] : memref<i32>
    %14 = memref.load %p0[] : memref<i32>
    %15 = memref.load %p3[] : memref<i32>
    %13 = arith.addi %14, %15 : i32
    memref.store %13, %p0[] : memref<i32>
    %17 = arith.constant 1 : i1
    %16 = func.call @unwrap_or_zero(%17) : (i1) -> i32
    memref.store %16, %p4[] : memref<i32>
    %19 = memref.load %p0[] : memref<i32>
    %20 = memref.load %p4[] : memref<i32>
    %18 = arith.addi %19, %20 : i32
    memref.store %18, %p0[] : memref<i32>
    %21 = memref.load %p0[] : memref<i32>
    func.return %21 : i32
  }
  func.func private @rok_runtime_init() -> ()
  func.func private @rok_runtime_shutdown() -> ()
  func.func @main() -> i32 {
    func.call @rok_runtime_init() : () -> ()
    %0 = func.call @rok_user_main() : () -> i32
    func.call @rok_runtime_shutdown() : () -> ()
    func.return %0 : i32
  }
}
