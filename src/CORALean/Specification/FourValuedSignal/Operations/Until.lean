module

public import CORALean.Specification.FourValuedSignal.FourValuedSignal
public import CORALean.Specification.FourValuedSignal.Operations.ToKleeneSignal
public import CORALean.Specification.KleeneSignal.Operations.And
public import CORALean.Specification.KleeneSignal.Operations.Basic
public import CORALean.Specification.KleeneSignal.Operations.Combine
public import CORALean.Specification.KleeneSignal.Operations.Or
public import CORALean.Specification.KleeneSignal.Operations.Until
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# The until of four-valued signals

`sig = until(lhs,interval,rhs)` of `fourValuedSignal.m`: the until of the Kleene refinements with
inconclusive mapped to `False` is the Kleene part, and the value is inconclusive where it differs
from that with inconclusive mapped to `True`; `none` is the `toBoolSignal()` error, which
`until_spec` shows does not occur. This is `Λ̃₁ U_I Λ̃₂` of [1, Sec. 4.3 (operators)], the `⊔₂` of
the untils of `⌊Λ̃⌋` and `⌈Λ̃⌉`.
Real-only, a specification: it computes on real time stamps exactly; its rounded refinement,
`True` and `False` only where this is, is `FourValuedSignal.untilFloat`.

## Inputs
* `lhs` – left signal
* `interval` – time interval
* `rhs` – right signal

## Output
* the until signal, or none if CORA throws

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = until(lhs,interval,rhs)`; `none` if `toBoolSignal()` throws. -/
noncomputable def FourValuedSignal.until (lhs : FourValuedSignal ℝ) (interval : STLInterval ℝ)
    (rhs : FourValuedSignal ℝ) : Option (FourValuedSignal ℝ) :=
  -- 1. minUntil of the refinements with inconclusive mapped to False
  let lhsMinRefinement := lhs.toKleeneSignal Kleene.ff
  let rhsMinRefinement := rhs.toKleeneSignal Kleene.ff
  let minUntil := lhsMinRefinement.until interval rhsMinRefinement
  -- 2. maxUntil of the refinements with inconclusive mapped to True
  let lhsMaxRefinement := lhs.toKleeneSignal Kleene.tt
  let rhsMaxRefinement := rhs.toKleeneSignal Kleene.tt
  let maxUntil := lhsMaxRefinement.until interval rhsMaxRefinement
  -- 3. inc = kleeneSignal.combine(@(args) kleene.fromBool(args(1) ~= args(2)),min,max)...
  let inc := (KleeneSignal.combine (fun (args : Fin 2 → Kleene) (_ : Unit) =>
    Kleene.fromBool (decide (args 0 ≠ args 1))) ![minUntil, maxUntil] ()).toBoolSignal?
  inc.map fun inc => ⟨minUntil, inc⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
