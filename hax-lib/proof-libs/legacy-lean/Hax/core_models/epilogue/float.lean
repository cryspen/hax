import Hax.core_models.epilogue.num

macro "declare_Hax_float_ops" typeName:ident : command =>
  `(
    namespace $typeName

    instance : core_models.ops.arith.Add.AssociatedTypes $typeName $typeName where
      Output := $typeName

    instance : core_models.ops.arith.Sub.AssociatedTypes $typeName $typeName where
      Output := $typeName

    instance : core_models.ops.arith.Mul.AssociatedTypes $typeName $typeName where
      Output := $typeName

    instance : core_models.ops.arith.Div.AssociatedTypes $typeName $typeName where
      Output := $typeName

    instance : core_models.ops.arith.Add $typeName $typeName where
      add := fun x y => pure (x + y)

    instance : core_models.ops.arith.Sub $typeName $typeName where
      sub := fun x y => pure (x - y)

    instance : core_models.ops.arith.Mul $typeName $typeName where
      mul := fun x y => pure (x * y)

    instance : core_models.ops.arith.Div $typeName $typeName where
      div := fun x y => pure (x / y)

    end $typeName
  )

declare_Hax_float_ops f32
declare_Hax_float_ops f64
