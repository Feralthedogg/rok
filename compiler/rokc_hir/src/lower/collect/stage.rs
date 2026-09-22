//! The library's collected stage in a byte form (spec 9.2.16): a build
//! of the same library takes it instead of collecting the library's
//! items again. The library's items go with it; what the tables borrow
//! from them is written as where it sits in them (item, member) and
//! borrowed again from the items read back.

use std::borrow::Cow;
use std::collections::HashMap;

use rokc_ast::{ExternItem, ImplItem, TraitDef, TraitItem};
use rokc_core::codec::{Codec, Dec, Enc};
use rokc_core::{codec_enum, codec_struct};

use super::super::{
    ClosureSink, Impl, Impls, InstanceWarns, MethodOrFn, MethodTarget, ShapeHandler, Tables,
    TypeDefs, TypeNames,
};
use super::{Collected, Intrinsic};
use crate::lower::{AstEnumDef, AstStructDef, Expr, FnDef, Item, Program, Ty};

/// The library's stage of a compile (`HirInput::library`).
pub struct LibraryStage {
    pub(super) c: Collected<'static>,
    pub(super) lib: &'static Program,
    pub(super) type_names: [Vec<String>; 2],
}

impl LibraryStage {
    /// Write the stage; `false` when something it borrows is not in the
    /// library's items (nothing to read back then).
    #[must_use]
    pub fn enc(&self, e: &mut Enc) -> bool {
        let at = Locs::of(self.lib);
        self.lib.enc(e);
        self.type_names.enc(e);
        enc_collected(&self.c, &at, e).is_some()
    }

    /// The stage written by `enc`; its items live as long as the process.
    pub fn dec(d: &mut Dec<'_>) -> Option<Self> {
        let lib: &'static Program = Box::leak(Box::new(Program::dec(d)?));
        let type_names = Codec::dec(d)?;
        let c = dec_collected(lib, d)?;
        Some(Self { c, lib, type_names })
    }
}

/// What a borrowed AST node is.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Kind {
    Fn,
    Struct,
    Enum,
    Trait,
    Ty,
    Expr,
}

/// No member: the item itself.
const WHOLE: u32 = u32::MAX;

/// Where each borrowable node of a program is: (item, member).
struct Locs(HashMap<(Kind, usize), (u32, u32)>);

fn addr<T>(r: &T) -> usize {
    std::ptr::from_ref(r) as usize
}

impl Locs {
    fn of(p: &Program) -> Self {
        let mut m = HashMap::new();
        for (i, item) in (0u32..).zip(&p.items) {
            let mut put = |k: Kind, a: usize, j: u32| {
                m.insert((k, a), (i, j));
            };
            match item {
                Item::Fn(f) => put(Kind::Fn, addr(f), WHOLE),
                Item::Struct(s) => put(Kind::Struct, addr(s), WHOLE),
                Item::Enum(e) => put(Kind::Enum, addr(e), WHOLE),
                Item::Trait(t) => {
                    put(Kind::Trait, addr(t), WHOLE);
                    for (j, ti) in (0u32..).zip(&t.items) {
                        if let TraitItem::Method(f) = ti {
                            put(Kind::Fn, addr(f), j);
                        }
                    }
                }
                Item::Impl(im) => {
                    for (j, ii) in (0u32..).zip(&im.items) {
                        if let ImplItem::Method(f) = ii {
                            put(Kind::Fn, addr(f), j);
                        }
                    }
                }
                Item::Static(s) => {
                    put(Kind::Ty, addr(&s.ty), WHOLE);
                    if let Some(v) = &s.value {
                        put(Kind::Expr, addr(v), WHOLE);
                    }
                }
                Item::Extern(b) => {
                    for (j, xi) in (0u32..).zip(&b.items) {
                        match xi {
                            ExternItem::Fn(f) => put(Kind::Fn, addr(f), j),
                            ExternItem::Static(s) => {
                                put(Kind::Ty, addr(&s.ty), j);
                                if let Some(v) = &s.value {
                                    put(Kind::Expr, addr(v), j);
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        Self(m)
    }

    fn enc<T>(&self, kind: Kind, r: &T, e: &mut Enc) -> Option<()> {
        let &(item, member) = self.0.get(&(kind, addr(r)))?;
        e.u(u64::from(item));
        e.u(u64::from(member));
        Some(())
    }
}

/// A node `Locs` put at (item, member) of `p`.
trait Located: Sized + 'static {
    fn find(item: &'static Item, member: u32) -> Option<&'static Self>;

    fn read(p: &'static Program, d: &mut Dec<'_>) -> Option<&'static Self> {
        let i = usize::try_from(d.u()?).ok()?;
        let j = u32::try_from(d.u()?).ok()?;
        Self::find(p.items.get(i)?, j)
    }
}

impl Located for FnDef {
    fn find(item: &'static Item, j: u32) -> Option<&'static Self> {
        let j_ = j as usize;
        match item {
            Item::Fn(f) if j == WHOLE => Some(f),
            Item::Trait(t) => match t.items.get(j_)? {
                TraitItem::Method(f) => Some(f),
                _ => None,
            },
            Item::Impl(im) => match im.items.get(j_)? {
                ImplItem::Method(f) => Some(f),
                _ => None,
            },
            Item::Extern(b) => match b.items.get(j_)? {
                ExternItem::Fn(f) => Some(f),
                ExternItem::Static(_) => None,
            },
            _ => None,
        }
    }
}

impl Located for AstStructDef {
    fn find(item: &'static Item, j: u32) -> Option<&'static Self> {
        match item {
            Item::Struct(s) if j == WHOLE => Some(s),
            _ => None,
        }
    }
}

impl Located for AstEnumDef {
    fn find(item: &'static Item, j: u32) -> Option<&'static Self> {
        match item {
            Item::Enum(e) if j == WHOLE => Some(e),
            _ => None,
        }
    }
}

impl Located for TraitDef {
    fn find(item: &'static Item, j: u32) -> Option<&'static Self> {
        match item {
            Item::Trait(t) if j == WHOLE => Some(t),
            _ => None,
        }
    }
}

/// A static's declaration at (item, member).
fn static_at(item: &'static Item, j: u32) -> Option<&'static rokc_ast::StaticDef> {
    match item {
        Item::Static(s) if j == WHOLE => Some(s),
        Item::Extern(b) => match b.items.get(j as usize)? {
            ExternItem::Static(s) => Some(s),
            ExternItem::Fn(_) => None,
        },
        _ => None,
    }
}

impl Located for Ty {
    fn find(item: &'static Item, j: u32) -> Option<&'static Self> {
        static_at(item, j).map(|s| &s.ty)
    }
}

impl Located for Expr {
    fn find(item: &'static Item, j: u32) -> Option<&'static Self> {
        static_at(item, j)?.value.as_ref()
    }
}

fn enc_refs<'a, K: Codec + Ord + 'a, T: 'a>(
    m: impl IntoIterator<Item = (&'a K, &'a &'a T)>,
    k: Kind,
    at: &Locs,
    e: &mut Enc,
) -> Option<()> {
    let mut v: Vec<(&K, &&T)> = m.into_iter().collect();
    v.sort_by(|a, b| a.0.cmp(b.0));
    e.u(v.len() as u64);
    for (key, r) in v {
        key.enc(e);
        at.enc(k, *r, e)?;
    }
    Some(())
}

fn dec_refs<K: Codec + Eq + std::hash::Hash, T: Located>(
    p: &'static Program,
    d: &mut Dec<'_>,
) -> Option<HashMap<K, &'static T>> {
    let n = d.u()?;
    let mut m = HashMap::new();
    for _ in 0..n {
        let key = K::dec(d)?;
        m.insert(key, T::read(p, d)?);
    }
    Some(m)
}

fn enc_list<T>(v: &[(impl Codec, &T)], k: Kind, at: &Locs, e: &mut Enc) -> Option<()> {
    e.u(v.len() as u64);
    for (id, r) in v {
        id.enc(e);
        at.enc(k, *r, e)?;
    }
    Some(())
}

fn dec_list<I: Codec, T: Located>(
    p: &'static Program,
    d: &mut Dec<'_>,
) -> Option<Vec<(I, &'static T)>> {
    let n = d.u()?;
    (0..n).map(|_| Some((I::dec(d)?, T::read(p, d)?))).collect()
}

fn enc_collected(c: &Collected<'_>, at: &Locs, e: &mut Enc) -> Option<()> {
    enc_tables(&c.t, at, e)?;
    c.early.enc(e);
    c.pre_diags.enc(e);
    c.reexports.enc(e);
    enc_list(&c.enum_decls, Kind::Enum, at, e)?;
    enc_list(&c.struct_decls, Kind::Struct, at, e)?;
    c.inherent_keys.enc(e);
    c.static_defs.enc(e);
    e.u(c.static_asts.len() as u64);
    for (ty, module, init) in &c.static_asts {
        at.enc(Kind::Ty, *ty, e)?;
        module.enc(e);
        match init {
            None => e.u(0),
            Some(x) => {
                e.u(1);
                at.enc(Kind::Expr, *x, e)?;
            }
        }
    }
    c.lib_decl.enc(e);
    c.link_names.enc(e);
    c.templated.enc(e);
    c.system_fns.enc(e);
    c.no_safepoint.enc(e);
    c.wasm_imports.enc(e);
    c.extern_symbols.enc(e);
    enc_refs(&c.trait_defs, Kind::Trait, at, e)?;
    c.exports.enc(e);
    c.prebuilt.enc(e);
    c.inline_copies.enc(e);
    c.c_defs.enc(e);
    c.diverging.enc(e);
    Some(())
}

fn dec_collected(p: &'static Program, d: &mut Dec<'_>) -> Option<Collected<'static>> {
    let t = dec_tables(p, d)?;
    Some(Collected {
        t,
        early: Codec::dec(d)?,
        pre_diags: Codec::dec(d)?,
        reexports: Codec::dec(d)?,
        enum_decls: dec_list(p, d)?,
        struct_decls: dec_list(p, d)?,
        inherent_keys: Codec::dec(d)?,
        static_defs: Codec::dec(d)?,
        static_asts: {
            let n = d.u()?;
            (0..n)
                .map(|_| {
                    let ty = Ty::read(p, d)?;
                    let module = String::dec(d)?;
                    let init = match d.u()? {
                        0 => None,
                        1 => Some(Expr::read(p, d)?),
                        _ => return None,
                    };
                    Some((ty, module, init))
                })
                .collect::<Option<_>>()?
        },
        lib_decl: Codec::dec(d)?,
        link_names: Codec::dec(d)?,
        templated: Codec::dec(d)?,
        system_fns: Codec::dec(d)?,
        no_safepoint: Codec::dec(d)?,
        wasm_imports: Codec::dec(d)?,
        extern_symbols: Codec::dec(d)?,
        trait_defs: dec_refs(p, d)?,
        exports: Codec::dec(d)?,
        prebuilt: Codec::dec(d)?,
        inline_copies: Codec::dec(d)?,
        c_defs: Codec::dec(d)?,
        diverging: Codec::dec(d)?,
    })
}

// The leaf indexes, `auto_memo`, `bound_methods` / `bound_traits` and
// the root flags are left out: the next stage starts them afresh.
fn enc_tables(t: &Tables<'_>, at: &Locs, e: &mut Enc) -> Option<()> {
    t.fn_table.enc(e);
    t.extern_fns.enc(e);
    t.method_table.enc(e);
    t.key_of.enc(e);
    t.infer_ret.enc(e);
    t.may_diverge.enc(e);
    t.method_info.enc(e);
    let defs = &t.defs;
    defs.structs.enc(e);
    defs.struct_table.enc(e);
    defs.enums.enc(e);
    defs.enum_table.enc(e);
    enc_refs(&defs.generic_structs, Kind::Struct, at, e)?;
    enc_refs(&defs.generic_enums, Kind::Enum, at, e)?;
    defs.defaulted_leaves.enc(e);
    t.consts.enc(e);
    enc_refs(&t.generic_fns, Kind::Fn, at, e)?;
    t.generic_methods.enc(e);
    t.intrinsics.enc(e);
    t.generic_intrinsics.enc(e);
    t.extern_fn_ids.enc(e);
    t.rok_externs.enc(e);
    t.c_variadic.enc(e);
    t.c_defs.enc(e);
    t.stdcall_fns.enc(e);
    t.sink.enc(e);
    t.item_visibility.enc(e);
    t.field_vis.enc(e);
    t.impls.enc(e);
    t.unsafe_fns.enc(e);
    t.neg_auto.enc(e);
    t.trait_info.enc(e);
    t.statics.enc(e);
    t.mut_statics.enc(e);
    t.literal_shapes.enc(e);
    t.names.enc(e);
    e.u(t.decls.len() as u64);
    for d in &t.decls {
        match d {
            MethodOrFn::Fn(f) => {
                e.u(0);
                at.enc(Kind::Fn, *f, e)?;
            }
            MethodOrFn::Method {
                fn_def,
                self_ty,
                module,
                key,
                subst,
            } => {
                match fn_def {
                    Cow::Borrowed(f) => {
                        e.u(1);
                        at.enc(Kind::Fn, *f, e)?;
                    }
                    Cow::Owned(f) => {
                        e.u(2);
                        f.enc(e);
                    }
                }
                self_ty.enc(e);
                module.enc(e);
                key.enc(e);
                subst.enc(e);
            }
        }
    }
    t.non_exhaustive.enc(e);
    Some(())
}

fn dec_tables(p: &'static Program, d: &mut Dec<'_>) -> Option<Tables<'static>> {
    let mut t = Tables::empty();
    t.fn_table = Codec::dec(d)?;
    t.extern_fns = Codec::dec(d)?;
    t.method_table = Codec::dec(d)?;
    t.key_of = Codec::dec(d)?;
    t.infer_ret = Codec::dec(d)?;
    t.may_diverge = Codec::dec(d)?;
    t.method_info = Codec::dec(d)?;
    t.defs = TypeDefs {
        structs: Codec::dec(d)?,
        struct_table: Codec::dec(d)?,
        enums: Codec::dec(d)?,
        enum_table: Codec::dec(d)?,
        generic_structs: dec_refs(p, d)?,
        generic_enums: dec_refs(p, d)?,
        defaulted_leaves: Codec::dec(d)?,
    };
    t.consts = Codec::dec(d)?;
    t.generic_fns = dec_refs(p, d)?;
    t.generic_methods = Codec::dec(d)?;
    t.intrinsics = Codec::dec(d)?;
    t.generic_intrinsics = Codec::dec(d)?;
    t.extern_fn_ids = Codec::dec(d)?;
    t.rok_externs = Codec::dec(d)?;
    t.c_variadic = Codec::dec(d)?;
    t.c_defs = Codec::dec(d)?;
    t.stdcall_fns = Codec::dec(d)?;
    t.sink = Codec::dec(d)?;
    t.item_visibility = Codec::dec(d)?;
    t.field_vis = Codec::dec(d)?;
    t.impls = Codec::dec(d)?;
    t.unsafe_fns = Codec::dec(d)?;
    t.neg_auto = Codec::dec(d)?;
    t.trait_info = Codec::dec(d)?;
    t.statics = Codec::dec(d)?;
    t.mut_statics = Codec::dec(d)?;
    t.literal_shapes = Codec::dec(d)?;
    t.names = Codec::dec(d)?;
    let n = d.u()?;
    t.decls = (0..n)
        .map(|_| {
            let fn_def = match d.u()? {
                0 => return Some(MethodOrFn::Fn(FnDef::read(p, d)?)),
                1 => Cow::Borrowed(FnDef::read(p, d)?),
                2 => Cow::Owned(<FnDef as Codec>::dec(d)?),
                _ => return None,
            };
            Some(MethodOrFn::Method {
                fn_def,
                self_ty: Codec::dec(d)?,
                module: Codec::dec(d)?,
                key: Codec::dec(d)?,
                subst: Codec::dec(d)?,
            })
        })
        .collect::<Option<_>>()?;
    t.non_exhaustive = Codec::dec(d)?;
    Some(t)
}

// The leaf indexes are left out (rebuilt on the first lookup) and so is
// `uses`: the next stage takes the compile's own table.
impl Codec for TypeNames {
    fn enc(&self, e: &mut Enc) {
        self.names.enc(e);
        self.traits.enc(e);
        self.auto_traits.enc(e);
        self.lang.enc(e);
        self.variants.enc(e);
        self.reexports.enc(e);
        self.visibility.enc(e);
        self.mod_vis.enc(e);
        self.diags.enc(e);
        self.generic_aliases.enc(e);
        self.plain_aliases.enc(e);
        self.alias_depth.enc(e);
        self.broken_aliases.enc(e);
        self.alias_uses.enc(e);
        self.unknown_spans.enc(e);
        self.canon_memo.enc(e);
        self.consts.enc(e);
        self.value_reexports.enc(e);
    }
    fn dec(d: &mut Dec<'_>) -> Option<Self> {
        let mut n = Self::empty();
        n.names = Codec::dec(d)?;
        n.traits = Codec::dec(d)?;
        n.auto_traits = Codec::dec(d)?;
        n.lang = Codec::dec(d)?;
        n.variants = Codec::dec(d)?;
        n.reexports = Codec::dec(d)?;
        n.visibility = Codec::dec(d)?;
        n.mod_vis = Codec::dec(d)?;
        n.diags = Codec::dec(d)?;
        n.generic_aliases = Codec::dec(d)?;
        n.plain_aliases = Codec::dec(d)?;
        n.alias_depth = Codec::dec(d)?;
        n.broken_aliases = Codec::dec(d)?;
        n.alias_uses = Codec::dec(d)?;
        n.unknown_spans = Codec::dec(d)?;
        n.canon_memo = Codec::dec(d)?;
        n.consts = Codec::dec(d)?;
        n.value_reexports = Codec::dec(d)?;
        Some(n)
    }
}

codec_struct!(ClosureSink {
    extras,
    ref_out,
    next_id,
    mono_cache,
    mono_sigs,
    mono_depth,
    uninferred,
    any_tags,
    any_dispatch,
    projecting,
    thunks,
    instances,
    instance_warns,
    diagnostics,
    infer_vars,
    infer_depth,
    infer_floor,
    fn_origin,
    track_caller,
    const_lowering,
    const_stack,
    inferred_ret,
    inferred_fns,
    bodies_done,
    sig_pass,
    call_sites,
    recursive_ret,
    tentative_ret,
    params,
    failed,
    bodies,
    assumed,
    const_names,
});
codec_struct!(InstanceWarns { instances, warns });
codec_struct!(Impl {
    trait_key,
    trait_args,
    assoc,
    generics,
    where_clause,
    self_ty,
    module,
    methods,
    consts,
    concrete,
});
codec_struct!(Impls {
    all,
    by_target,
    by_trait
});
codec_struct!(ShapeHandler {
    shape,
    name,
    priority,
    span
});
codec_enum!(MethodTarget {
    Struct(x0),
    Enum(x0),
    Mangled(x0)
});
codec_enum!(Intrinsic {
    Prim(x0),
    Convert,
    BufNew,
    BufGet,
    BufSet,
    BufSame,
    BufErase,
    PtrRead { volatile },
    PtrWrite { volatile },
    SizeOf,
    AlignOf,
    AddrOf,
    DropInPlace,
    Atomic(x0),
    AnyCast,
    MethodTable,
    MlirOp,
    MlirAttr,
});
