module

public import CORALean.Specification.FourValuedSTL.Definitions.Basic
public import Mathlib.Data.NNReal.Defs

@[expose] public section

/-!
# A partial overapproximation extends to a reachable set covering the executions

If `R̃ : T → 2^X` is a partial overapproximation of the reachable set of `H` (every execution
`ξ ∈ E` has `ξ(t) ∈ R̃(t)` on `T`), then `R(t) := R̃(t)` on `T` and `R(t) := R_H(t)` elsewhere
extends `R̃` and covers every execution of `H`: the step of [1, Cor. 1] that "there must exist some
extension of `R̃` covering all executions of the system by definition of the reachable set".

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal


-- =======================================  MAIN THEOREM  ======================================= --

open Classical in
theorem FourValuedSTL.exists_extension {X : Type} (T : Set ℝ≥0) (Rp : ℝ≥0 → Set X)
    (E : Set (ℝ≥0 → X)) (hover : ∀ ξ ∈ E, ∀ t ∈ T, ξ t ∈ Rp t) : -- --- CONCL ---
    ∃ R, FourValuedSTL.Extends R Rp T ∧ ∀ ξ ∈ E, FourValuedSTL.Covers R ξ := by -- --- PROOF ---
  refine ⟨fun t => if t ∈ T then Rp t else FourValuedSTL.reachSet E t, fun t ht => by simp [ht],
    fun ξ hξ t => ?_⟩
  by_cases ht : t ∈ T
  · simpa [ht] using hover ξ hξ t ht
  · show ξ t ∈ (if t ∈ T then Rp t else FourValuedSTL.reachSet E t)
    rw [if_neg ht]
    exact ⟨ξ, hξ, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
