module

public import CORALean.Global.Float.Instances.Flint.Operations.AddDown
public import CORALean.Global.Float.Instances.Flint.Operations.AddUp
public import CORALean.Global.Float.Instances.Flint.Operations.DivDown
public import CORALean.Global.Float.Instances.Flint.Operations.DivUp
public import CORALean.Global.Float.Instances.Flint.Operations.Half
public import CORALean.Global.Float.Instances.Flint.Operations.Le
public import CORALean.Global.Float.Instances.Flint.Operations.Maximum
public import CORALean.Global.Float.Instances.Flint.Operations.Minimum
public import CORALean.Global.Float.Instances.Flint.Operations.MulDown
public import CORALean.Global.Float.Instances.Flint.Operations.MulUp
public import CORALean.Global.Float.Instances.Flint.Operations.Neg

/-!
# The operations of `Flint p`, collected

Six rounded ones, each an `opaque` call into FLINT through `Flint/coralean_flint.c`,
and five exact ones in pure Lean, the comparison `Dyadic.le` itself.
-/
