module Core_models.Num.Niche_types
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core_models
open FStar.Mul

type t_Nanoseconds = | Nanoseconds : u32 -> t_Nanoseconds

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_13:Core_models.Clone.t_Clone t_Nanoseconds

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_14:Core_models.Marker.t_Copy t_Nanoseconds

val e_: Prims.unit 

val impl_Nanoseconds__new (v_val: u32)
    : Prims.Pure (Core_models.Option.t_Option t_Nanoseconds) Prims.l_True (fun _ -> Prims.l_True)

val impl_Nanoseconds__new_unchecked (v_val: u32)
    : Prims.Pure t_Nanoseconds Prims.l_True (fun _ -> Prims.l_True)

val impl_Nanoseconds__as_inner (self: t_Nanoseconds)
    : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_7:Core_models.Marker.t_StructuralPartialEq t_Nanoseconds

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_8:Core_models.Cmp.t_PartialEq t_Nanoseconds t_Nanoseconds

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_15:Core_models.Cmp.t_Eq t_Nanoseconds

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_10:Core_models.Cmp.t_PartialOrd t_Nanoseconds t_Nanoseconds

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_9:Core_models.Cmp.t_Ord t_Nanoseconds

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_11:Core_models.Hash.t_Hash t_Nanoseconds

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_12:Core_models.Fmt.t_Debug t_Nanoseconds

val impl_Nanoseconds__ZERO: t_Nanoseconds 

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_1:Core_models.Default.t_Default t_Nanoseconds

val f_default__impl_1__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

type t_NonZeroU8Inner = | NonZeroU8Inner : u8 -> t_NonZeroU8Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_86:Core_models.Clone.t_Clone t_NonZeroU8Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_87:Core_models.Marker.t_Copy t_NonZeroU8Inner

val e_ee_1: Prims.unit

val impl_NonZeroU8Inner__new (v_val: u8)
    : Prims.Pure (Core_models.Option.t_Option t_NonZeroU8Inner) Prims.l_True (fun _ -> Prims.l_True)

val impl_NonZeroU8Inner__new_unchecked (v_val: u8)
    : Prims.Pure t_NonZeroU8Inner Prims.l_True (fun _ -> Prims.l_True)

val impl_NonZeroU8Inner__as_inner (self: t_NonZeroU8Inner)
    : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_17:Core_models.Marker.t_StructuralPartialEq t_NonZeroU8Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_18:Core_models.Cmp.t_PartialEq t_NonZeroU8Inner t_NonZeroU8Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_88:Core_models.Cmp.t_Eq t_NonZeroU8Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_20:Core_models.Cmp.t_PartialOrd t_NonZeroU8Inner t_NonZeroU8Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_19:Core_models.Cmp.t_Ord t_NonZeroU8Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_21:Core_models.Hash.t_Hash t_NonZeroU8Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_22:Core_models.Fmt.t_Debug t_NonZeroU8Inner

type t_NonZeroU16Inner = | NonZeroU16Inner : u16 -> t_NonZeroU16Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_89:Core_models.Clone.t_Clone t_NonZeroU16Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_90:Core_models.Marker.t_Copy t_NonZeroU16Inner

val e_ee_2: Prims.unit

val impl_NonZeroU16Inner__new (v_val: u16)
    : Prims.Pure (Core_models.Option.t_Option t_NonZeroU16Inner) Prims.l_True (fun _ -> Prims.l_True)

val impl_NonZeroU16Inner__new_unchecked (v_val: u16)
    : Prims.Pure t_NonZeroU16Inner Prims.l_True (fun _ -> Prims.l_True)

val impl_NonZeroU16Inner__as_inner (self: t_NonZeroU16Inner)
    : Prims.Pure u16 Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_24:Core_models.Marker.t_StructuralPartialEq t_NonZeroU16Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_25:Core_models.Cmp.t_PartialEq t_NonZeroU16Inner t_NonZeroU16Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_91:Core_models.Cmp.t_Eq t_NonZeroU16Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_27:Core_models.Cmp.t_PartialOrd t_NonZeroU16Inner t_NonZeroU16Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_26:Core_models.Cmp.t_Ord t_NonZeroU16Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_28:Core_models.Hash.t_Hash t_NonZeroU16Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_29:Core_models.Fmt.t_Debug t_NonZeroU16Inner

type t_NonZeroU32Inner = | NonZeroU32Inner : u32 -> t_NonZeroU32Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_92:Core_models.Clone.t_Clone t_NonZeroU32Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_93:Core_models.Marker.t_Copy t_NonZeroU32Inner

val e_ee_3: Prims.unit

val impl_NonZeroU32Inner__new (v_val: u32)
    : Prims.Pure (Core_models.Option.t_Option t_NonZeroU32Inner) Prims.l_True (fun _ -> Prims.l_True)

val impl_NonZeroU32Inner__new_unchecked (v_val: u32)
    : Prims.Pure t_NonZeroU32Inner Prims.l_True (fun _ -> Prims.l_True)

val impl_NonZeroU32Inner__as_inner (self: t_NonZeroU32Inner)
    : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_31:Core_models.Marker.t_StructuralPartialEq t_NonZeroU32Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_32:Core_models.Cmp.t_PartialEq t_NonZeroU32Inner t_NonZeroU32Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_94:Core_models.Cmp.t_Eq t_NonZeroU32Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_34:Core_models.Cmp.t_PartialOrd t_NonZeroU32Inner t_NonZeroU32Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_33:Core_models.Cmp.t_Ord t_NonZeroU32Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_35:Core_models.Hash.t_Hash t_NonZeroU32Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_36:Core_models.Fmt.t_Debug t_NonZeroU32Inner

type t_NonZeroU64Inner = | NonZeroU64Inner : u64 -> t_NonZeroU64Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_95:Core_models.Clone.t_Clone t_NonZeroU64Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_96:Core_models.Marker.t_Copy t_NonZeroU64Inner

val e_ee_4: Prims.unit

val impl_NonZeroU64Inner__new (v_val: u64)
    : Prims.Pure (Core_models.Option.t_Option t_NonZeroU64Inner) Prims.l_True (fun _ -> Prims.l_True)

val impl_NonZeroU64Inner__new_unchecked (v_val: u64)
    : Prims.Pure t_NonZeroU64Inner Prims.l_True (fun _ -> Prims.l_True)

val impl_NonZeroU64Inner__as_inner (self: t_NonZeroU64Inner)
    : Prims.Pure u64 Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_38:Core_models.Marker.t_StructuralPartialEq t_NonZeroU64Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_39:Core_models.Cmp.t_PartialEq t_NonZeroU64Inner t_NonZeroU64Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_97:Core_models.Cmp.t_Eq t_NonZeroU64Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_41:Core_models.Cmp.t_PartialOrd t_NonZeroU64Inner t_NonZeroU64Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_40:Core_models.Cmp.t_Ord t_NonZeroU64Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_42:Core_models.Hash.t_Hash t_NonZeroU64Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_43:Core_models.Fmt.t_Debug t_NonZeroU64Inner

type t_NonZeroU128Inner = | NonZeroU128Inner : u128 -> t_NonZeroU128Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_98:Core_models.Clone.t_Clone t_NonZeroU128Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_99:Core_models.Marker.t_Copy t_NonZeroU128Inner

val e_ee_5: Prims.unit

val impl_NonZeroU128Inner__new (v_val: u128)
    : Prims.Pure (Core_models.Option.t_Option t_NonZeroU128Inner) Prims.l_True (fun _ -> Prims.l_True)

val impl_NonZeroU128Inner__new_unchecked (v_val: u128)
    : Prims.Pure t_NonZeroU128Inner Prims.l_True (fun _ -> Prims.l_True)

val impl_NonZeroU128Inner__as_inner (self: t_NonZeroU128Inner)
    : Prims.Pure u128 Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_45:Core_models.Marker.t_StructuralPartialEq t_NonZeroU128Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_46:Core_models.Cmp.t_PartialEq t_NonZeroU128Inner t_NonZeroU128Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_100:Core_models.Cmp.t_Eq t_NonZeroU128Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_48:Core_models.Cmp.t_PartialOrd t_NonZeroU128Inner t_NonZeroU128Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_47:Core_models.Cmp.t_Ord t_NonZeroU128Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_49:Core_models.Hash.t_Hash t_NonZeroU128Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_50:Core_models.Fmt.t_Debug t_NonZeroU128Inner

type t_NonZeroI8Inner = | NonZeroI8Inner : i8 -> t_NonZeroI8Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_101:Core_models.Clone.t_Clone t_NonZeroI8Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_102:Core_models.Marker.t_Copy t_NonZeroI8Inner

val e_ee_6: Prims.unit

val impl_NonZeroI8Inner__new (v_val: i8)
    : Prims.Pure (Core_models.Option.t_Option t_NonZeroI8Inner) Prims.l_True (fun _ -> Prims.l_True)

val impl_NonZeroI8Inner__new_unchecked (v_val: i8)
    : Prims.Pure t_NonZeroI8Inner Prims.l_True (fun _ -> Prims.l_True)

val impl_NonZeroI8Inner__as_inner (self: t_NonZeroI8Inner)
    : Prims.Pure i8 Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_52:Core_models.Marker.t_StructuralPartialEq t_NonZeroI8Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_53:Core_models.Cmp.t_PartialEq t_NonZeroI8Inner t_NonZeroI8Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_103:Core_models.Cmp.t_Eq t_NonZeroI8Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_55:Core_models.Cmp.t_PartialOrd t_NonZeroI8Inner t_NonZeroI8Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_54:Core_models.Cmp.t_Ord t_NonZeroI8Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_56:Core_models.Hash.t_Hash t_NonZeroI8Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_57:Core_models.Fmt.t_Debug t_NonZeroI8Inner

type t_NonZeroI16Inner = | NonZeroI16Inner : i16 -> t_NonZeroI16Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_104:Core_models.Clone.t_Clone t_NonZeroI16Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_105:Core_models.Marker.t_Copy t_NonZeroI16Inner

val e_ee_7: Prims.unit

val impl_NonZeroI16Inner__new (v_val: i16)
    : Prims.Pure (Core_models.Option.t_Option t_NonZeroI16Inner) Prims.l_True (fun _ -> Prims.l_True)

val impl_NonZeroI16Inner__new_unchecked (v_val: i16)
    : Prims.Pure t_NonZeroI16Inner Prims.l_True (fun _ -> Prims.l_True)

val impl_NonZeroI16Inner__as_inner (self: t_NonZeroI16Inner)
    : Prims.Pure i16 Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_59:Core_models.Marker.t_StructuralPartialEq t_NonZeroI16Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_60:Core_models.Cmp.t_PartialEq t_NonZeroI16Inner t_NonZeroI16Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_106:Core_models.Cmp.t_Eq t_NonZeroI16Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_62:Core_models.Cmp.t_PartialOrd t_NonZeroI16Inner t_NonZeroI16Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_61:Core_models.Cmp.t_Ord t_NonZeroI16Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_63:Core_models.Hash.t_Hash t_NonZeroI16Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_64:Core_models.Fmt.t_Debug t_NonZeroI16Inner

type t_NonZeroI32Inner = | NonZeroI32Inner : i32 -> t_NonZeroI32Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_107:Core_models.Clone.t_Clone t_NonZeroI32Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_108:Core_models.Marker.t_Copy t_NonZeroI32Inner

val e_ee_8: Prims.unit

val impl_NonZeroI32Inner__new (v_val: i32)
    : Prims.Pure (Core_models.Option.t_Option t_NonZeroI32Inner) Prims.l_True (fun _ -> Prims.l_True)

val impl_NonZeroI32Inner__new_unchecked (v_val: i32)
    : Prims.Pure t_NonZeroI32Inner Prims.l_True (fun _ -> Prims.l_True)

val impl_NonZeroI32Inner__as_inner (self: t_NonZeroI32Inner)
    : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_66:Core_models.Marker.t_StructuralPartialEq t_NonZeroI32Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_67:Core_models.Cmp.t_PartialEq t_NonZeroI32Inner t_NonZeroI32Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_109:Core_models.Cmp.t_Eq t_NonZeroI32Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_69:Core_models.Cmp.t_PartialOrd t_NonZeroI32Inner t_NonZeroI32Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_68:Core_models.Cmp.t_Ord t_NonZeroI32Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_70:Core_models.Hash.t_Hash t_NonZeroI32Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_71:Core_models.Fmt.t_Debug t_NonZeroI32Inner

type t_NonZeroI64Inner = | NonZeroI64Inner : i64 -> t_NonZeroI64Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_110:Core_models.Clone.t_Clone t_NonZeroI64Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_111:Core_models.Marker.t_Copy t_NonZeroI64Inner

val e_ee_9: Prims.unit

val impl_NonZeroI64Inner__new (v_val: i64)
    : Prims.Pure (Core_models.Option.t_Option t_NonZeroI64Inner) Prims.l_True (fun _ -> Prims.l_True)

val impl_NonZeroI64Inner__new_unchecked (v_val: i64)
    : Prims.Pure t_NonZeroI64Inner Prims.l_True (fun _ -> Prims.l_True)

val impl_NonZeroI64Inner__as_inner (self: t_NonZeroI64Inner)
    : Prims.Pure i64 Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_73:Core_models.Marker.t_StructuralPartialEq t_NonZeroI64Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_74:Core_models.Cmp.t_PartialEq t_NonZeroI64Inner t_NonZeroI64Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_112:Core_models.Cmp.t_Eq t_NonZeroI64Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_76:Core_models.Cmp.t_PartialOrd t_NonZeroI64Inner t_NonZeroI64Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_75:Core_models.Cmp.t_Ord t_NonZeroI64Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_77:Core_models.Hash.t_Hash t_NonZeroI64Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_78:Core_models.Fmt.t_Debug t_NonZeroI64Inner

type t_NonZeroI128Inner = | NonZeroI128Inner : i128 -> t_NonZeroI128Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_113:Core_models.Clone.t_Clone t_NonZeroI128Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_114:Core_models.Marker.t_Copy t_NonZeroI128Inner

val e_ee_10: Prims.unit

val impl_NonZeroI128Inner__new (v_val: i128)
    : Prims.Pure (Core_models.Option.t_Option t_NonZeroI128Inner) Prims.l_True (fun _ -> Prims.l_True)

val impl_NonZeroI128Inner__new_unchecked (v_val: i128)
    : Prims.Pure t_NonZeroI128Inner Prims.l_True (fun _ -> Prims.l_True)

val impl_NonZeroI128Inner__as_inner (self: t_NonZeroI128Inner)
    : Prims.Pure i128 Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_80:Core_models.Marker.t_StructuralPartialEq t_NonZeroI128Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_81:Core_models.Cmp.t_PartialEq t_NonZeroI128Inner t_NonZeroI128Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_115:Core_models.Cmp.t_Eq t_NonZeroI128Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_83:Core_models.Cmp.t_PartialOrd t_NonZeroI128Inner t_NonZeroI128Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_82:Core_models.Cmp.t_Ord t_NonZeroI128Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_84:Core_models.Hash.t_Hash t_NonZeroI128Inner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_85:Core_models.Fmt.t_Debug t_NonZeroI128Inner

type t_UsizeNoHighBit = | UsizeNoHighBit : usize -> t_UsizeNoHighBit

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_137:Core_models.Clone.t_Clone t_UsizeNoHighBit

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_138:Core_models.Marker.t_Copy t_UsizeNoHighBit

val e_ee_11: Prims.unit

val impl_UsizeNoHighBit__new (v_val: usize)
    : Prims.Pure (Core_models.Option.t_Option t_UsizeNoHighBit) Prims.l_True (fun _ -> Prims.l_True)

val impl_UsizeNoHighBit__new_unchecked (v_val: usize)
    : Prims.Pure t_UsizeNoHighBit Prims.l_True (fun _ -> Prims.l_True)

val impl_UsizeNoHighBit__as_inner (self: t_UsizeNoHighBit)
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_117:Core_models.Marker.t_StructuralPartialEq t_UsizeNoHighBit

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_118:Core_models.Cmp.t_PartialEq t_UsizeNoHighBit t_UsizeNoHighBit

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_139:Core_models.Cmp.t_Eq t_UsizeNoHighBit

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_120:Core_models.Cmp.t_PartialOrd t_UsizeNoHighBit t_UsizeNoHighBit

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_119:Core_models.Cmp.t_Ord t_UsizeNoHighBit

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_121:Core_models.Hash.t_Hash t_UsizeNoHighBit

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_122:Core_models.Fmt.t_Debug t_UsizeNoHighBit

type t_NonZeroUsizeInner = | NonZeroUsizeInner : usize -> t_NonZeroUsizeInner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_140:Core_models.Clone.t_Clone t_NonZeroUsizeInner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_141:Core_models.Marker.t_Copy t_NonZeroUsizeInner

val e_ee_12: Prims.unit

val impl_NonZeroUsizeInner__new (v_val: usize)
    : Prims.Pure (Core_models.Option.t_Option t_NonZeroUsizeInner) Prims.l_True (fun _ -> Prims.l_True)

val impl_NonZeroUsizeInner__new_unchecked (v_val: usize)
    : Prims.Pure t_NonZeroUsizeInner Prims.l_True (fun _ -> Prims.l_True)

val impl_NonZeroUsizeInner__as_inner (self: t_NonZeroUsizeInner)
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_124:Core_models.Marker.t_StructuralPartialEq t_NonZeroUsizeInner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_125:Core_models.Cmp.t_PartialEq t_NonZeroUsizeInner t_NonZeroUsizeInner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_142:Core_models.Cmp.t_Eq t_NonZeroUsizeInner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_127:Core_models.Cmp.t_PartialOrd t_NonZeroUsizeInner t_NonZeroUsizeInner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_126:Core_models.Cmp.t_Ord t_NonZeroUsizeInner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_128:Core_models.Hash.t_Hash t_NonZeroUsizeInner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_129:Core_models.Fmt.t_Debug t_NonZeroUsizeInner

type t_NonZeroIsizeInner = | NonZeroIsizeInner : isize -> t_NonZeroIsizeInner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_143:Core_models.Clone.t_Clone t_NonZeroIsizeInner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_144:Core_models.Marker.t_Copy t_NonZeroIsizeInner

val e_ee_13: Prims.unit

val impl_NonZeroIsizeInner__new (v_val: isize)
    : Prims.Pure (Core_models.Option.t_Option t_NonZeroIsizeInner) Prims.l_True (fun _ -> Prims.l_True)

val impl_NonZeroIsizeInner__new_unchecked (v_val: isize)
    : Prims.Pure t_NonZeroIsizeInner Prims.l_True (fun _ -> Prims.l_True)

val impl_NonZeroIsizeInner__as_inner (self: t_NonZeroIsizeInner)
    : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_131:Core_models.Marker.t_StructuralPartialEq t_NonZeroIsizeInner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_132:Core_models.Cmp.t_PartialEq t_NonZeroIsizeInner t_NonZeroIsizeInner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_145:Core_models.Cmp.t_Eq t_NonZeroIsizeInner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_134:Core_models.Cmp.t_PartialOrd t_NonZeroIsizeInner t_NonZeroIsizeInner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_133:Core_models.Cmp.t_Ord t_NonZeroIsizeInner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_135:Core_models.Hash.t_Hash t_NonZeroIsizeInner

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_136:Core_models.Fmt.t_Debug t_NonZeroIsizeInner

type t_U32NotAllOnes = | U32NotAllOnes : u32 -> t_U32NotAllOnes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_174:Core_models.Clone.t_Clone t_U32NotAllOnes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_175:Core_models.Marker.t_Copy t_U32NotAllOnes

val e_ee_14: Prims.unit

val impl_U32NotAllOnes__new (v_val: u32)
    : Prims.Pure (Core_models.Option.t_Option t_U32NotAllOnes) Prims.l_True (fun _ -> Prims.l_True)

val impl_U32NotAllOnes__new_unchecked (v_val: u32)
    : Prims.Pure t_U32NotAllOnes Prims.l_True (fun _ -> Prims.l_True)

val impl_U32NotAllOnes__as_inner (self: t_U32NotAllOnes)
    : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_147:Core_models.Marker.t_StructuralPartialEq t_U32NotAllOnes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_148:Core_models.Cmp.t_PartialEq t_U32NotAllOnes t_U32NotAllOnes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_176:Core_models.Cmp.t_Eq t_U32NotAllOnes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_150:Core_models.Cmp.t_PartialOrd t_U32NotAllOnes t_U32NotAllOnes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_149:Core_models.Cmp.t_Ord t_U32NotAllOnes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_151:Core_models.Hash.t_Hash t_U32NotAllOnes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_152:Core_models.Fmt.t_Debug t_U32NotAllOnes

type t_I32NotAllOnes = | I32NotAllOnes : i32 -> t_I32NotAllOnes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_177:Core_models.Clone.t_Clone t_I32NotAllOnes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_178:Core_models.Marker.t_Copy t_I32NotAllOnes

val e_ee_15: Prims.unit

val impl_I32NotAllOnes__new (v_val: i32)
    : Prims.Pure (Core_models.Option.t_Option t_I32NotAllOnes) Prims.l_True (fun _ -> Prims.l_True)

val impl_I32NotAllOnes__new_unchecked (v_val: i32)
    : Prims.Pure t_I32NotAllOnes Prims.l_True (fun _ -> Prims.l_True)

val impl_I32NotAllOnes__as_inner (self: t_I32NotAllOnes)
    : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_154:Core_models.Marker.t_StructuralPartialEq t_I32NotAllOnes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_155:Core_models.Cmp.t_PartialEq t_I32NotAllOnes t_I32NotAllOnes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_179:Core_models.Cmp.t_Eq t_I32NotAllOnes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_157:Core_models.Cmp.t_PartialOrd t_I32NotAllOnes t_I32NotAllOnes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_156:Core_models.Cmp.t_Ord t_I32NotAllOnes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_158:Core_models.Hash.t_Hash t_I32NotAllOnes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_159:Core_models.Fmt.t_Debug t_I32NotAllOnes

type t_U64NotAllOnes = | U64NotAllOnes : u64 -> t_U64NotAllOnes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_180:Core_models.Clone.t_Clone t_U64NotAllOnes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_181:Core_models.Marker.t_Copy t_U64NotAllOnes

val e_ee_16: Prims.unit

val impl_U64NotAllOnes__new (v_val: u64)
    : Prims.Pure (Core_models.Option.t_Option t_U64NotAllOnes) Prims.l_True (fun _ -> Prims.l_True)

val impl_U64NotAllOnes__new_unchecked (v_val: u64)
    : Prims.Pure t_U64NotAllOnes Prims.l_True (fun _ -> Prims.l_True)

val impl_U64NotAllOnes__as_inner (self: t_U64NotAllOnes)
    : Prims.Pure u64 Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_161:Core_models.Marker.t_StructuralPartialEq t_U64NotAllOnes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_162:Core_models.Cmp.t_PartialEq t_U64NotAllOnes t_U64NotAllOnes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_182:Core_models.Cmp.t_Eq t_U64NotAllOnes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_164:Core_models.Cmp.t_PartialOrd t_U64NotAllOnes t_U64NotAllOnes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_163:Core_models.Cmp.t_Ord t_U64NotAllOnes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_165:Core_models.Hash.t_Hash t_U64NotAllOnes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_166:Core_models.Fmt.t_Debug t_U64NotAllOnes

type t_I64NotAllOnes = | I64NotAllOnes : i64 -> t_I64NotAllOnes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_183:Core_models.Clone.t_Clone t_I64NotAllOnes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_184:Core_models.Marker.t_Copy t_I64NotAllOnes

val e_ee_17: Prims.unit

val impl_I64NotAllOnes__new (v_val: i64)
    : Prims.Pure (Core_models.Option.t_Option t_I64NotAllOnes) Prims.l_True (fun _ -> Prims.l_True)

val impl_I64NotAllOnes__new_unchecked (v_val: i64)
    : Prims.Pure t_I64NotAllOnes Prims.l_True (fun _ -> Prims.l_True)

val impl_I64NotAllOnes__as_inner (self: t_I64NotAllOnes)
    : Prims.Pure i64 Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_168:Core_models.Marker.t_StructuralPartialEq t_I64NotAllOnes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_169:Core_models.Cmp.t_PartialEq t_I64NotAllOnes t_I64NotAllOnes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_185:Core_models.Cmp.t_Eq t_I64NotAllOnes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_171:Core_models.Cmp.t_PartialOrd t_I64NotAllOnes t_I64NotAllOnes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_170:Core_models.Cmp.t_Ord t_I64NotAllOnes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_172:Core_models.Hash.t_Hash t_I64NotAllOnes

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_173:Core_models.Fmt.t_Debug t_I64NotAllOnes

class t_NotAllOnesHelper (v_Self: Type0) = {
  f_Type:Type0;
  f_Type_659097508213326199:Core_models.Marker.t_Sized f_Type
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_NotAllOnesHelper_for_u32: t_NotAllOnesHelper u32 =
  { f_Type = t_U32NotAllOnes; f_Type_659097508213326199 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_NotAllOnesHelper_for_i32: t_NotAllOnesHelper i32 =
  { f_Type = t_I32NotAllOnes; f_Type_659097508213326199 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_NotAllOnesHelper_for_u64: t_NotAllOnesHelper u64 =
  { f_Type = t_U64NotAllOnes; f_Type_659097508213326199 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_NotAllOnesHelper_for_i64: t_NotAllOnesHelper i64 =
  { f_Type = t_I64NotAllOnes; f_Type_659097508213326199 = FStar.Tactics.Typeclasses.solve }
