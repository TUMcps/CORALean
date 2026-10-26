module

public import CORALean.Specification.KleeneSignal.KleeneSignal
public import CORALean.Specification.KleeneSignal.Operations.ToBoolSignal
public import CORALean.Specification.PointSegmentSignal.Operations.Combine
public import CORALean.Specification.PointSegmentSignal.Operations.UntilFloat
public import CORALean.Specification.STLInterval.Operations.Minus
public import CORALean.Specification.STLInterval.Operations.MinusInward
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# The until of three-valued signals over a float scalar

`sig = until(lhs,interval,rhs)` of `kleeneSignal.m` with time stamps in `𝕋`, as `until`, except
for the rounding of the time shift: the until of the minimal refinements, which says where the
result is `True`, shifts inward (`minusInward`), and that of the maximal refinements, which says
where it is not `False`, outward (`minus`). So a float `True` or `False` is the exact one
(`untilFloat_sound`); CORA rounds both to nearest.

## Inputs
* `lhs` – left signal
* `interval` – time interval
* `rhs` – right signal

## Output
* the until signal
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

/-- `sig = until(lhs,interval,rhs)`, shifted inward for `True` and outward for `False`. -/
def KleeneSignal.untilFloat (lhs : KleeneSignal 𝕋) (interval : STLInterval 𝕋)
    (rhs : KleeneSignal 𝕋) : KleeneSignal 𝕋 :=
  -- 1. minUntil of the refinements with unknown mapped to false, shifted inward
  let lhsMinRefinement := lhs.toBoolSignal false
  let rhsMinRefinement := rhs.toBoolSignal false
  let minUntil := lhsMinRefinement.untilFloat STLInterval.minusInward interval rhsMinRefinement
  -- 2. maxUntil of the refinements with unknown mapped to true, shifted outward
  let lhsMaxRefinement := lhs.toBoolSignal true
  let rhsMaxRefinement := rhs.toBoolSignal true
  let maxUntil := lhsMaxRefinement.untilFloat STLInterval.minus interval rhsMaxRefinement
  -- 3. unk = pointSegmentSignal.combine(@(args) args(1) ~= args(2),minUntil,maxUntil)
  let unk := PointSegmentSignal.combine
    (fun (args : Fin 2 → Bool) (_ : Unit) => decide (args 0 ≠ args 1)) ![minUntil, maxUntil] ()
  ⟨minUntil, unk⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
