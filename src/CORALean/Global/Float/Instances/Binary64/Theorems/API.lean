import CORALean.Global.Float.Instances.Binary64.Theorems.AddDownLeAdd
import CORALean.Global.Float.Instances.Binary64.Theorems.DivDownLeDiv
import CORALean.Global.Float.Instances.Binary64.Theorems.MulDownLeMul

/-!
# What binary64 is proved to do

Three obligations, one per rounded operation, and all three the same argument:
the downward operations are the upward ones between negations, so each is its
upward assumption read through `toReal_neg`. Everything else the class asks for
is assumed in `Axioms`, and `Instances` assembles the two.
-/
