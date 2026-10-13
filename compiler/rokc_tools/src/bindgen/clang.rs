//! The part of libclang's C API `rokc bindgen` uses, loaded at run time so
//! nothing else needs libclang. Layouts and constants follow
//! clang-c/Index.h's stable ABI.

use std::ffi::{CStr, CString, c_char, c_int, c_longlong, c_uint, c_ulong, c_ulonglong, c_void};
use std::path::Path;

#[repr(C)]
#[derive(Clone, Copy)]
pub struct Cursor {
    pub kind: c_int,
    xdata: c_int,
    data: [*const c_void; 3],
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct Type {
    pub kind: c_int,
    data: [*mut c_void; 2],
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct CxString {
    data: *const c_void,
    flags: c_uint,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct Location {
    ptr: [*const c_void; 2],
    int: c_uint,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct Range {
    ptr: [*const c_void; 2],
    begin: c_uint,
    end: c_uint,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct Token {
    int: [c_uint; 4],
    ptr: *mut c_void,
}

#[repr(C)]
pub struct Unsaved {
    pub name: *const c_char,
    pub contents: *const c_char,
    pub len: c_ulong,
}

pub type Ptr = *mut c_void;
type Visitor = extern "C" fn(Cursor, Cursor, Ptr) -> c_int;

// Cursor kinds.
pub const UNEXPOSED_DECL: c_int = 1;
pub const STRUCT_DECL: c_int = 2;
pub const UNION_DECL: c_int = 3;
pub const ENUM_DECL: c_int = 5;
pub const FIELD_DECL: c_int = 6;
pub const ENUM_CONSTANT_DECL: c_int = 7;
pub const FUNCTION_DECL: c_int = 8;
pub const VAR_DECL: c_int = 9;
pub const TYPEDEF_DECL: c_int = 20;
pub const LINKAGE_SPEC: c_int = 23;
pub const MACRO_DEFINITION: c_int = 501;
pub const MACRO_EXPANSION: c_int = 502;
pub const INCLUSION_DIRECTIVE: c_int = 503;
pub const STATIC_ASSERT: c_int = 602;

// Type kinds.
pub const T_UNEXPOSED: c_int = 1;
pub const T_VOID: c_int = 2;
pub const T_BOOL: c_int = 3;
pub const T_CHAR_U: c_int = 4;
pub const T_UCHAR: c_int = 5;
pub const T_CHAR16: c_int = 6;
pub const T_CHAR32: c_int = 7;
pub const T_USHORT: c_int = 8;
pub const T_UINT: c_int = 9;
pub const T_ULONG: c_int = 10;
pub const T_ULONGLONG: c_int = 11;
pub const T_CHAR_S: c_int = 13;
pub const T_SCHAR: c_int = 14;
pub const T_WCHAR: c_int = 15;
pub const T_SHORT: c_int = 16;
pub const T_INT: c_int = 17;
pub const T_LONG: c_int = 18;
pub const T_LONGLONG: c_int = 19;
pub const T_FLOAT: c_int = 21;
pub const T_DOUBLE: c_int = 22;
pub const T_LONGDOUBLE: c_int = 23;
pub const T_POINTER: c_int = 101;
pub const T_RECORD: c_int = 105;
pub const T_ENUM: c_int = 106;
pub const T_TYPEDEF: c_int = 107;
pub const T_FUNCTION_NO_PROTO: c_int = 110;
pub const T_FUNCTION_PROTO: c_int = 111;
pub const T_CONSTANT_ARRAY: c_int = 112;
pub const T_INCOMPLETE_ARRAY: c_int = 114;
pub const T_ELABORATED: c_int = 119;
pub const T_ATTRIBUTED: c_int = 163;
pub const T_BTF_TAG_ATTRIBUTED: c_int = 178;

pub const CC_DEFAULT: c_int = 0;
pub const CC_C: c_int = 1;
pub const CC_X86_STDCALL: c_int = 2;

pub const SC_STATIC: c_int = 3;
pub const TOKEN_PUNCTUATION: c_int = 0;
pub const TOKEN_KEYWORD: c_int = 1;
pub const EVAL_INT: c_int = 1;
pub const EVAL_FLOAT: c_int = 2;
pub const EVAL_STR: c_int = 4;
const DIAG_ERROR: c_int = 3;

// Translation unit flags: a detailed preprocessing record (macro
// definitions as cursors), function bodies skipped.
pub const TU_FLAGS: c_uint = 0x01 | 0x40;

macro_rules! api {
    ($($name:ident($($arg:ty),*) $(-> $ret:ty)?;)*) => {
        #[allow(non_snake_case)]
        pub struct Api {
            $(pub $name: unsafe extern "C" fn($($arg),*) $(-> $ret)?,)*
        }

        impl Api {
            fn load(lib: &Library) -> Result<Self, String> {
                Ok(Self {
                    // SAFETY: the symbol has this signature in clang-c/Index.h.
                    $($name: unsafe {
                        std::mem::transmute::<Ptr, unsafe extern "C" fn($($arg),*) $(-> $ret)?>(
                            lib.symbol(stringify!($name))?,
                        )
                    },)*
                })
            }
        }
    };
}

api! {
    clang_createIndex(c_int, c_int) -> Ptr;
    clang_disposeTranslationUnit(Ptr);
    clang_parseTranslationUnit2(Ptr, *const c_char, *const *const c_char, c_int, *mut Unsaved, c_uint, c_uint, *mut Ptr) -> c_int;
    clang_getNumDiagnostics(Ptr) -> c_uint;
    clang_getDiagnostic(Ptr, c_uint) -> Ptr;
    clang_getDiagnosticSeverity(Ptr) -> c_int;
    clang_formatDiagnostic(Ptr, c_uint) -> CxString;
    clang_defaultDiagnosticDisplayOptions() -> c_uint;
    clang_disposeDiagnostic(Ptr);
    clang_getCString(CxString) -> *const c_char;
    clang_disposeString(CxString);
    clang_getTranslationUnitCursor(Ptr) -> Cursor;
    clang_getTranslationUnitTargetInfo(Ptr) -> Ptr;
    clang_TargetInfo_getPointerWidth(Ptr) -> c_int;
    clang_TargetInfo_dispose(Ptr);
    clang_visitChildren(Cursor, Visitor, Ptr) -> c_uint;
    clang_getCursorSpelling(Cursor) -> CxString;
    clang_getCursorUSR(Cursor) -> CxString;
    clang_Cursor_getMangling(Cursor) -> CxString;
    clang_getCursorType(Cursor) -> Type;
    clang_getCursorLocation(Cursor) -> Location;
    clang_getCursorExtent(Cursor) -> Range;
    clang_getCursorDefinition(Cursor) -> Cursor;
    clang_Cursor_isNull(Cursor) -> c_int;
    clang_Cursor_isAnonymous(Cursor) -> c_uint;
    clang_Cursor_isAnonymousRecordDecl(Cursor) -> c_uint;
    clang_Type_getOffsetOf(Type, *const c_char) -> c_longlong;
    clang_Cursor_isBitField(Cursor) -> c_uint;
    clang_getFieldDeclBitWidth(Cursor) -> c_int;
    clang_Cursor_getOffsetOfField(Cursor) -> c_longlong;
    clang_Cursor_getStorageClass(Cursor) -> c_int;
    clang_Cursor_isFunctionInlined(Cursor) -> c_uint;
    clang_Cursor_isMacroFunctionLike(Cursor) -> c_uint;
    clang_Cursor_isMacroBuiltin(Cursor) -> c_uint;
    clang_Cursor_getNumArguments(Cursor) -> c_int;
    clang_Cursor_getArgument(Cursor, c_uint) -> Cursor;
    clang_getCursorTLSKind(Cursor) -> c_int;
    clang_isInvalidDeclaration(Cursor) -> c_uint;
    clang_Cursor_Evaluate(Cursor) -> Ptr;
    clang_EvalResult_getKind(Ptr) -> c_int;
    clang_EvalResult_getAsLongLong(Ptr) -> c_longlong;
    clang_EvalResult_getAsUnsigned(Ptr) -> c_ulonglong;
    clang_EvalResult_getAsDouble(Ptr) -> f64;
    clang_EvalResult_getAsStr(Ptr) -> *const c_char;
    clang_EvalResult_dispose(Ptr);
    clang_getEnumDeclIntegerType(Cursor) -> Type;
    clang_getEnumConstantDeclValue(Cursor) -> c_longlong;
    clang_getEnumConstantDeclUnsignedValue(Cursor) -> c_ulonglong;
    clang_getTypedefDeclUnderlyingType(Cursor) -> Type;
    clang_getTypeDeclaration(Type) -> Cursor;
    clang_getCanonicalType(Type) -> Type;
    clang_getPointeeType(Type) -> Type;
    clang_getResultType(Type) -> Type;
    clang_getNumArgTypes(Type) -> c_int;
    clang_getArgType(Type, c_uint) -> Type;
    clang_isFunctionTypeVariadic(Type) -> c_uint;
    clang_getFunctionTypeCallingConv(Type) -> c_int;
    clang_isConstQualifiedType(Type) -> c_uint;
    clang_getArrayElementType(Type) -> Type;
    clang_getArraySize(Type) -> c_longlong;
    clang_Type_getSizeOf(Type) -> c_longlong;
    clang_Type_getAlignOf(Type) -> c_longlong;
    clang_Type_getNamedType(Type) -> Type;
    clang_Type_getModifiedType(Type) -> Type;
    clang_getTypeSpelling(Type) -> CxString;
    clang_Location_isInSystemHeader(Location) -> c_int;
    clang_getFileName(Ptr) -> CxString;
    clang_getFileLocation(Location, *mut Ptr, *mut c_uint, *mut c_uint, *mut c_uint);
    clang_tokenize(Ptr, Range, *mut *mut Token, *mut c_uint);
    clang_getTokenKind(Token) -> c_int;
    clang_getTokenSpelling(Ptr, Token) -> CxString;
    clang_disposeTokens(Ptr, *mut Token, c_uint);
}

/// A loaded libclang. Never unloaded: it lives until the process exits.
pub struct Clang {
    api: Api,
    index: Ptr,
}

/// A parsed translation unit, with its libclang.
pub struct Unit<'a> {
    pub clang: &'a Clang,
    pub tu: Ptr,
}

struct Library(Ptr);

#[cfg(unix)]
impl Library {
    fn open(path: &Path) -> Result<Self, String> {
        unsafe extern "C" {
            fn dlopen(path: *const c_char, flags: c_int) -> Ptr;
            fn dlerror() -> *const c_char;
        }
        const RTLD_NOW: c_int = 2;
        let p = CString::new(path.as_os_str().as_encoded_bytes()).map_err(|e| e.to_string())?;
        // SAFETY: a NUL-terminated path; dlerror's text is copied at once.
        unsafe {
            let h = dlopen(p.as_ptr(), RTLD_NOW);
            if h.is_null() {
                return Err(CStr::from_ptr(dlerror()).to_string_lossy().into_owned());
            }
            Ok(Self(h))
        }
    }

    fn symbol(&self, name: &str) -> Result<Ptr, String> {
        unsafe extern "C" {
            fn dlsym(h: Ptr, name: *const c_char) -> Ptr;
        }
        let n = CString::new(name).expect("a symbol name");
        // SAFETY: a live handle and a NUL-terminated name.
        let p = unsafe { dlsym(self.0, n.as_ptr()) };
        if p.is_null() {
            Err(format!("libclang lacks `{name}`"))
        } else {
            Ok(p)
        }
    }
}

#[cfg(windows)]
impl Library {
    fn open(path: &Path) -> Result<Self, String> {
        use std::os::windows::ffi::OsStrExt;
        unsafe extern "system" {
            fn LoadLibraryW(name: *const u16) -> Ptr;
        }
        let w: Vec<u16> = path.as_os_str().encode_wide().chain([0]).collect();
        // SAFETY: a NUL-terminated wide path.
        let h = unsafe { LoadLibraryW(w.as_ptr()) };
        if h.is_null() {
            Err(std::io::Error::last_os_error().to_string())
        } else {
            Ok(Self(h))
        }
    }

    fn symbol(&self, name: &str) -> Result<Ptr, String> {
        unsafe extern "system" {
            fn GetProcAddress(h: Ptr, name: *const c_char) -> Ptr;
        }
        let n = CString::new(name).expect("a symbol name");
        // SAFETY: a live module handle and a NUL-terminated name.
        let p = unsafe { GetProcAddress(self.0, n.as_ptr()) };
        if p.is_null() {
            Err(format!("libclang lacks `{name}`"))
        } else {
            Ok(p)
        }
    }
}

extern "C" fn push_child(c: Cursor, _parent: Cursor, out: Ptr) -> c_int {
    // SAFETY: `children` passes its `Vec` as the client data.
    unsafe { (*out.cast::<Vec<Cursor>>()).push(c) };
    1 // CXChildVisit_Continue
}

impl Clang {
    pub fn load(path: &Path) -> Result<Self, String> {
        let lib =
            Library::open(path).map_err(|e| format!("cannot load {}: {e}", path.display()))?;
        let api = Api::load(&lib)?;
        // SAFETY: no PCH; diagnostics are read from the unit, not printed.
        let index = unsafe { (api.clang_createIndex)(0, 0) };
        Ok(Self { api, index })
    }

    pub const fn api(&self) -> &Api {
        &self.api
    }

    /// Parse `file` with the compiler `args`, `unsaved` replacing files'
    /// contents as `(path, text)`. `Err` holds the error diagnostics.
    pub fn parse(
        &self,
        file: &str,
        args: &[String],
        unsaved: &[(String, String)],
        errors_fatal: bool,
    ) -> Result<Unit<'_>, String> {
        let c = |s: &str| CString::new(s).map_err(|_| format!("`{s}` contains a NUL byte"));
        let file_c = c(file)?;
        let args_c = args.iter().map(|a| c(a)).collect::<Result<Vec<_>, _>>()?;
        let argv: Vec<*const c_char> = args_c.iter().map(|a| a.as_ptr()).collect();
        let unsaved_c = unsaved
            .iter()
            .map(|(p, t)| Ok((c(p)?, c(t)?)))
            .collect::<Result<Vec<_>, String>>()?;
        let mut files: Vec<Unsaved> = unsaved_c
            .iter()
            .map(|(p, t)| Unsaved {
                name: p.as_ptr(),
                contents: t.as_ptr(),
                len: t.as_bytes().len() as c_ulong,
            })
            .collect();
        let mut tu: Ptr = std::ptr::null_mut();
        // SAFETY: every pointer outlives the call; clang copies what it keeps.
        let code = unsafe {
            (self.api.clang_parseTranslationUnit2)(
                self.index,
                file_c.as_ptr(),
                argv.as_ptr(),
                argv.len() as c_int,
                files.as_mut_ptr(),
                files.len() as c_uint,
                TU_FLAGS,
                &raw mut tu,
            )
        };
        if code != 0 || tu.is_null() {
            return Err(format!("libclang cannot parse {file} (error {code})"));
        }
        let unit = Unit { clang: self, tu };
        if errors_fatal {
            let errors = unit.errors();
            if !errors.is_empty() {
                return Err(errors.join("\n"));
            }
        }
        Ok(unit)
    }

    pub fn string(&self, s: CxString) -> String {
        // SAFETY: `s` came from libclang and is disposed of here, once.
        unsafe {
            let p = (self.api.clang_getCString)(s);
            let out = if p.is_null() {
                String::new()
            } else {
                CStr::from_ptr(p).to_string_lossy().into_owned()
            };
            (self.api.clang_disposeString)(s);
            out
        }
    }

    pub fn children(&self, c: Cursor) -> Vec<Cursor> {
        let mut out: Vec<Cursor> = Vec::new();
        // SAFETY: `push_child` takes the `Vec` it is given for the call.
        unsafe { (self.api.clang_visitChildren)(c, push_child, (&raw mut out).cast()) };
        out
    }

    pub fn spelling(&self, c: Cursor) -> String {
        // SAFETY: a cursor of a live unit.
        self.string(unsafe { (self.api.clang_getCursorSpelling)(c) })
    }

    pub fn usr(&self, c: Cursor) -> String {
        // SAFETY: a cursor of a live unit.
        self.string(unsafe { (self.api.clang_getCursorUSR)(c) })
    }

    pub fn type_spelling(&self, t: Type) -> String {
        // SAFETY: a type of a live unit.
        self.string(unsafe { (self.api.clang_getTypeSpelling)(t) })
    }

    /// `(file, line)` of a cursor's location; file empty for none.
    pub fn file_line(&self, c: Cursor) -> (String, u32) {
        let mut file: Ptr = std::ptr::null_mut();
        let mut line = 0;
        // SAFETY: out-pointers to locals; a file of a live unit.
        unsafe {
            let loc = (self.api.clang_getCursorLocation)(c);
            (self.api.clang_getFileLocation)(
                loc,
                &raw mut file,
                &raw mut line,
                std::ptr::null_mut(),
                std::ptr::null_mut(),
            );
        }
        let name = if file.is_null() {
            String::new()
        } else {
            // SAFETY: a file of a live unit.
            self.string(unsafe { (self.api.clang_getFileName)(file) })
        };
        (name, line)
    }
}

impl Drop for Unit<'_> {
    fn drop(&mut self) {
        // SAFETY: the unit is not used after this.
        unsafe { (self.clang.api.clang_disposeTranslationUnit)(self.tu) };
    }
}

impl Unit<'_> {
    pub fn cursor(&self) -> Cursor {
        // SAFETY: a live unit.
        unsafe { (self.clang.api.clang_getTranslationUnitCursor)(self.tu) }
    }

    pub fn pointer_width(&self) -> u32 {
        // SAFETY: a live unit; the info is disposed of here.
        unsafe {
            let ti = (self.clang.api.clang_getTranslationUnitTargetInfo)(self.tu);
            let w = (self.clang.api.clang_TargetInfo_getPointerWidth)(ti);
            (self.clang.api.clang_TargetInfo_dispose)(ti);
            w as u32
        }
    }

    /// The formatted error diagnostics.
    pub fn errors(&self) -> Vec<String> {
        let api = &self.clang.api;
        let mut out = Vec::new();
        // SAFETY: diagnostics of a live unit, each disposed of once.
        unsafe {
            for i in 0..(api.clang_getNumDiagnostics)(self.tu) {
                let d = (api.clang_getDiagnostic)(self.tu, i);
                if (api.clang_getDiagnosticSeverity)(d) >= DIAG_ERROR {
                    let opts = (api.clang_defaultDiagnosticDisplayOptions)();
                    out.push(self.clang.string((api.clang_formatDiagnostic)(d, opts)));
                }
                (api.clang_disposeDiagnostic)(d);
            }
        }
        out
    }

    /// The tokens of a cursor's extent, as `(kind, spelling)`.
    pub fn tokens(&self, c: Cursor) -> Vec<(c_int, String)> {
        let api = &self.clang.api;
        let mut toks: *mut Token = std::ptr::null_mut();
        let mut n = 0;
        // SAFETY: the token array is read, then disposed of once.
        unsafe {
            (api.clang_tokenize)(
                self.tu,
                (api.clang_getCursorExtent)(c),
                &raw mut toks,
                &raw mut n,
            );
            if toks.is_null() {
                return Vec::new();
            }
            let out = std::slice::from_raw_parts(toks, n as usize)
                .iter()
                .map(|t| {
                    (
                        (api.clang_getTokenKind)(*t),
                        self.clang.string((api.clang_getTokenSpelling)(self.tu, *t)),
                    )
                })
                .collect();
            (api.clang_disposeTokens)(self.tu, toks, n);
            out
        }
    }
}

/// libclang's file name for each host.
pub const LIBRARY: &str = if cfg!(windows) {
    "libclang.dll"
} else if cfg!(target_vendor = "apple") {
    "libclang.dylib"
} else {
    "libclang.so"
};
