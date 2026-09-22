// Explicit TypeIDs of an MLIR plugin loaded by rokc.exe. Included by the
// plugin development headers' mlir/Support/TypeID.h before its first
// explicit TypeID (docs/mlir-plugins.md).
//
// An explicit TypeID is the address of `TypeIDResolver<T>::id`, data in
// rokc.exe. A DLL reaches another module's data only through dllimport,
// which MLIR's headers do not declare, so each resolver looks its `id` up
// in rokc.exe's exports by decorated name at first use instead. A type
// rokc.exe does not define (one of the plugin's own) gets a TypeID owned
// by the plugin. Elsewhere plugins bind to rokc's symbols directly.

#ifndef ROK_MLIR_TYPEID_H
#define ROK_MLIR_TYPEID_H

#ifdef _WIN32

#include "llvm/Support/DynamicLibrary.h"

#include <string>

namespace rok_mlir {

// `fn` is `TypeIDResolver<T>::resolveTypeID`'s decorated name.
inline ::mlir::TypeID importTypeID(::llvm::StringRef fn,
                                   const ::mlir::SelfOwningTypeID &own) {
  // ?resolveTypeID@<resolver>SA?AVTypeID@3@XZ
  //   -> ?id@<resolver>0VSelfOwningTypeID@3@A
  ::llvm::StringRef head = "?resolveTypeID@", tail = "SA?AVTypeID@3@XZ";
  if (fn.consume_front(head) && fn.consume_back(tail)) {
    std::string id = "?id@" + fn.str() + "0VSelfOwningTypeID@3@A";
    if (void *p = ::llvm::sys::DynamicLibrary::getPermanentLibrary(nullptr)
                      .getAddressOfSymbol(id.c_str()))
      return ::mlir::TypeID::getFromOpaquePointer(p);
  }
  return own.getTypeID();
}

} // namespace rok_mlir

#undef MLIR_DECLARE_EXPLICIT_SELF_OWNING_TYPE_ID
#define MLIR_DECLARE_EXPLICIT_SELF_OWNING_TYPE_ID(CLASS_NAME)                  \
  namespace mlir {                                                             \
  namespace detail {                                                           \
  template <>                                                                  \
  class TypeIDResolver<CLASS_NAME> {                                           \
  public:                                                                      \
    static TypeID resolveTypeID() {                                            \
      static SelfOwningTypeID own;                                             \
      static TypeID id = ::rok_mlir::importTypeID(__FUNCDNAME__, own);         \
      return id;                                                               \
    }                                                                          \
  };                                                                           \
  } /* namespace detail */                                                     \
  } /* namespace mlir */

#undef MLIR_DEFINE_EXPLICIT_SELF_OWNING_TYPE_ID
#define MLIR_DEFINE_EXPLICIT_SELF_OWNING_TYPE_ID(CLASS_NAME)

#endif // _WIN32

#endif // ROK_MLIR_TYPEID_H
