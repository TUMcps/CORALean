module

public import CORALean.Specification.FourValuedSignal.FourValuedSignal
public import CORALean.Specification.FourValuedSignal.Operations.ToKleeneSignal
public import CORALean.Specification.KleeneSignal.Operations.Basic
public import CORALean.Specification.KleeneSignal.Operations.Combine
public import CORALean.Specification.KleeneSignal.Operations.UntilFloat
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# The until of four-valued signals over a float scalar

`sig = until(lhs,interval,rhs)` of `fourValuedSignal.m` with time stamps in `𝕋`, as `until`, with
the Kleene untils of the two refinements taken by `KleeneSignal.untilFloat`, which shifts inward
for `True` and outward for `False`; so a float `True` or `False` is the exact one
(`untilFloat_sound`). `none` is the `toBoolSignal()` error.

## Inputs
* `lhs` – left signal
* `interval` – time interval
* `rhs` – right signal

## Output
* the until signal, or none if CORA throws
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = until(lhs,interval,rhs)` with the Kleene untils of `KleeneSignal.untilFloat`. -/
def FourValuedSignal.untilFloat (lhs : FourValuedSignal 𝕋) (interval : STLInterval 𝕋)
    (rhs : FourValuedSignal 𝕋) : Option (FourValuedSignal 𝕋) :=
  -- 1. minUntil of the refinements with inconclusive mapped to False
  let lhsMinRefinement := lhs.toKleeneSignal Kleene.ff
  let rhsMinRefinement := rhs.toKleeneSignal Kleene.ff
  let minUntil := lhsMinRefinement.untilFloat interval rhsMinRefinement
  -- 2. maxUntil of the refinements with inconclusive mapped to True
  let lhsMaxRefinement := lhs.toKleeneSignal Kleene.tt
  let rhsMaxRefinement := rhs.toKleeneSignal Kleene.tt
  let maxUntil := lhsMaxRefinement.untilFloat interval rhsMaxRefinement
  -- 3. inc = kleeneSignal.combine(@(args) kleene.fromBool(args(1) ~= args(2)),min,max)...
  let inc := (KleeneSignal.combine (fun (args : Fin 2 → Kleene) (_ : Unit) =>
    Kleene.fromBool (decide (args 0 ≠ args 1))) ![minUntil, maxUntil] ()).toBoolSignal?
  inc.map fun inc => ⟨minUntil, inc⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
