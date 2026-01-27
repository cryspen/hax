import Hax.Lib
import Hax.Integers.Ops

abbrev f32 := Float32
abbrev f64 := Float

macro "declare_Hax_float_ops" typeName:ident : command =>
  `(
    namespace $typeName

    instance : Core_models.Ops.Arith.Add.AssociatedTypes $typeName $typeName where
      Output := $typeName

    instance : Core_models.Ops.Arith.Sub.AssociatedTypes $typeName $typeName where
      Output := $typeName

    instance : Core_models.Ops.Arith.Mul.AssociatedTypes $typeName $typeName where
      Output := $typeName

    instance : Core_models.Ops.Arith.Div.AssociatedTypes $typeName $typeName where
      Output := $typeName

    instance : Core_models.Ops.Arith.Add $typeName $typeName where
      add := fun x y => x + y

    instance : Core_models.Ops.Arith.Sub $typeName $typeName where
      sub := fun x y => x - y

    instance : Core_models.Ops.Arith.Mul $typeName $typeName where
      mul := fun x y => x * y

    instance : Core_models.Ops.Arith.Div $typeName $typeName where
      div := fun x y => x / y

    end $typeName
  )

declare_Hax_float_ops f32
declare_Hax_float_ops f64
