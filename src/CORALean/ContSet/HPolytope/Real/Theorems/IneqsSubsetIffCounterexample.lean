import CORALean.ContSet.HPolytope.Real.Operations.MemIneqsIff
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-!
# `[1, Lemma 1]` fails at an empty inbody

`X = {x₁ ≤ -1, -x₁ ≤ -1, x₂ ≤ 0}` is empty, so it lies in the unit box `Y`. Both are
H-polytopes in the sense of `[1, Def. 1]` (`ker H = {0}`). Yet no `Λ ≥ 0` has `Λ Hx = Hy`:
`Hy`'s row `(0, -1)` would be a nonnegative combination of `(1, 0)`, `(-1, 0)`, `(0, 1)`,
whose second coordinates are `0, 0, 1`. So "only if" needs `X` nonempty
(`ineqs_subset_iff`).

## References

* [1] S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". In
      Proc. of the 58th IEEE Conference on Decision and Control (CDC), pp. 4367-4372, 2019.
      arXiv:1903.05214.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.ineqs_subset_iff_counterexample :
    ∃ (Hx : Mat ℝ 3 2) (hx : Vec ℝ 3) (Hy : Mat ℝ 4 2) (hy : Vec ℝ 4),
      (∀ v, Hx *ᵥ v = 0 → v = 0) ∧ (∀ v, Hy *ᵥ v = 0 → v = 0) ∧
      (HPolytope.ineqs Hx hx).construct ⊆ (HPolytope.ineqs Hy hy).construct ∧
      ¬ ∃ Λ : Mat ℝ 4 3, (∀ i j, 0 ≤ Λ i j) ∧ Λ * Hx = Hy ∧ Λ *ᵥ hx ≤ hy := by -- --- PROOF ---
  refine ⟨!![1, 0; -1, 0; 0, 1], ![-1, -1, 0], !![1, 0; -1, 0; 0, 1; 0, -1], ![1, 1, 1, 1],
    ?_, ?_, ?_, ?_⟩
  -- both have trivial kernel
  · intro v hv
    have h0 := congrFun hv 0
    have h2 := congrFun hv 2
    simp [mulVec, dotProduct, Fin.sum_univ_two] at h0 h2
    funext i; fin_cases i <;> simp [h0, h2]
  · intro v hv
    have h0 := congrFun hv 0
    have h2 := congrFun hv 2
    simp [mulVec, dotProduct, Fin.sum_univ_two] at h0 h2
    funext i; fin_cases i <;> simp [h0, h2]
  -- the inbody is empty: `x₁ ≤ -1` and `x₁ ≥ 1`
  · intro x hx
    rw [HPolytope.mem_ineqs_iff] at hx
    have h0 := hx 0
    have h1 := hx 1
    simp [mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    linarith
  -- `(0, -1)` is no nonnegative combination of the inbody's rows
  · rintro ⟨Λ, hΛ, h1, -⟩
    have h := congrFun (congrFun h1 3) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three] at h
    linarith [hΛ 3 2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
