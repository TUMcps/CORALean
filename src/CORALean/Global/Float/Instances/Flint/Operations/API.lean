module

public import CORALean.Global.Float.Instances.Flint.Operations.AddDown
public import CORALean.Global.Float.Instances.Flint.Operations.AddUp
public import CORALean.Global.Float.Instances.Flint.Operations.DivDown
public import CORALean.Global.Float.Instances.Flint.Operations.DivUp
public import CORALean.Global.Float.Instances.Flint.Operations.Basic
public import CORALean.Global.Float.Instances.Flint.Operations.MulDown
public import CORALean.Global.Float.Instances.Flint.Operations.MulUp

/-!
# The operations of `Flint p`, collected

Six rounded ones, each an `opaque` call into FLINT through `Flint/coralean_flint.c`,
and five exact ones in pure Lean, the comparison `Dyadic.le` itself.
-/
