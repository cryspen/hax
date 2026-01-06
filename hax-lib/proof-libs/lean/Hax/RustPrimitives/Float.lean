import Hax.RustPrimitives.Integers

abbrev f32 := Float32
abbrev f64 := Float

macro "declare_Hax_float_ops" typeName:ident : command =>
  `(
    namespace $typeName

    instance : HaxAdd $typeName where
      add := fun x y => x + y

    instance : HaxSub $typeName where
      sub := fun x y => x - y

    instance : HaxMul $typeName where
      mul := fun x y => x * y

    instance : HaxDiv $typeName where
      div := fun x y => x / y

    end $typeName
  )

declare_Hax_float_ops f32
declare_Hax_float_ops f64
