module

public import CORALean.ContSet.HPolytope.Real.Definitions.AHPolytope
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# An AH-polytope with an injective map, in halfspaces

`[1, Eq. 4]` claims `{x̄ + X x | H x ≤ h} = {y | H X† y ≤ h + H X† x̄}` whenever
`X† X = I`. The right-hand side forgets that `y - x̄` must lie in `range X`: it is a
cylinder along `ker X†` (`ahPolytope_eq_of_leftInverse_counterexample`). Adding that
equality, `(I - X X†)(y - x̄) = 0`, makes it exact — the H-representation the equation
was after, equality rows and all. Only when `X` is square, so that `X X† = I`, is the
printed form right.

## References

* [1] S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". In
      Proc. of the 58th IEEE Conference on Decision and Control (CDC), pp. 4367-4372, 2019.
      arXiv:1903.05214.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.ahPolytope_eq_of_leftInverse {xbar : Vec ℝ n} {X : Mat ℝ n m}
    {Xd : Mat ℝ m n} (hX : Xd * X = 1) {H : Mat ℝ q m} {h : Vec ℝ q} : -- --- STMT ---
    HPolytope.ahPolytope xbar X (HPolytope.ineqs H h)
      = {y | (H * Xd) *ᵥ y ≤ h + (H * Xd) *ᵥ xbar ∧
          (1 - X * Xd) *ᵥ (y - xbar) = 0} := by -- --- PROOF ---
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hXd : Xd *ᵥ (X *ᵥ p) = p := by rw [mulVec_mulVec, hX, one_mulVec]
    refine ⟨fun i => ?_, ?_⟩
    · have := HPolytope.mem_ineqs_iff.mp hp i
      rw [← mulVec_mulVec, ← mulVec_mulVec, mulVec_add, hXd, mulVec_add, Pi.add_apply,
        Pi.add_apply]
      linarith
    · rw [add_sub_cancel_left, sub_mulVec, one_mulVec, ← mulVec_mulVec, hXd, sub_self]
  -- `y - x̄ = X X† (y - x̄)`, so `p = X† (y - x̄)` is a preimage
  · rintro ⟨h1, h2⟩
    have hy : y - xbar = X *ᵥ (Xd *ᵥ (y - xbar)) := by
      rw [sub_mulVec, one_mulVec, sub_eq_zero] at h2
      rw [mulVec_mulVec]
      exact h2
    refine ⟨Xd *ᵥ (y - xbar), HPolytope.mem_ineqs_iff.mpr fun i => ?_, ?_⟩
    · have := h1 i
      rw [mulVec_sub, mulVec_sub, Pi.sub_apply]
      rw [Pi.add_apply, ← mulVec_mulVec, ← mulVec_mulVec] at this
      linarith
    · rw [← hy]
      abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
