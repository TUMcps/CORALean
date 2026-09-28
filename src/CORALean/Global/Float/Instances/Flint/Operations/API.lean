import CORALean.Global.Float.Instances.Flint.Operations.AddDown
import CORALean.Global.Float.Instances.Flint.Operations.AddUp
import CORALean.Global.Float.Instances.Flint.Operations.DivDown
import CORALean.Global.Float.Instances.Flint.Operations.DivUp
import CORALean.Global.Float.Instances.Flint.Operations.Half
import CORALean.Global.Float.Instances.Flint.Operations.Le
import CORALean.Global.Float.Instances.Flint.Operations.Maximum
import CORALean.Global.Float.Instances.Flint.Operations.Minimum
import CORALean.Global.Float.Instances.Flint.Operations.MulDown
import CORALean.Global.Float.Instances.Flint.Operations.MulUp
import CORALean.Global.Float.Instances.Flint.Operations.Neg

/-!
# The operations of `Flint p`, collected

Six rounded ones, each an `opaque` call into FLINT through `Flint/coralean_flint.c`,
and five exact ones in pure Lean, the comparison `Dyadic.le` itself.
-/
