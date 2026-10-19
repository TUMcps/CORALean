module

public import CORALean.ContSet.HPolytope.Real.Definitions.AHPolytope
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# The intersection of two AH-polytopes

`[1, Eq. 7]` eliminates `p₂` from `x̄₁ + X₁ p₁ = x̄₂ + X₂ p₂` as
`p₂ = X₂† v + (I - X₂† X₂) w`, `v = X₁ p₁ + x̄₁ - x̄₂`, `w` free. That parametrizes every
solution only when one exists, `v ∈ range X₂`, and the printed `P_∩` has no such row; it
also drops `H₂` from the `w` block and `x̄₁` from the result. With all three restored —
`x̄₁ + (X₁, 0) P_∩`, `H₂ (X₂† v + (I - X₂† X₂) w) ≤ h₂` and the equality
`(I - X₂ X₂†) v = 0` — it is exact, for any `X₂†` with `X₂ X₂† X₂ = X₂` (the Moore-Penrose
inverse among them). Without the equality it fails
(`ahPolytope_inter_eq_counterexample`).

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

variable {n n₁ n₂ q₁ q₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.ahPolytope_inter_eq {x₁ x₂ : Vec ℝ n} {X₁ : Mat ℝ n n₁} {X₂ : Mat ℝ n n₂}
    {H₁ : Mat ℝ q₁ n₁} {h₁ : Vec ℝ q₁} {H₂ : Mat ℝ q₂ n₂} {h₂ : Vec ℝ q₂} {X₂d : Mat ℝ n₂ n}
    (hg : X₂ * X₂d * X₂ = X₂) : -- --- CONCL ---
    HPolytope.ahPolytope x₁ X₁ (HPolytope.ineqs H₁ h₁)
        ∩ HPolytope.ahPolytope x₂ X₂ (HPolytope.ineqs H₂ h₂)
      = {x | ∃ (p₁ : Vec ℝ n₁) (w : Vec ℝ n₂), H₁ *ᵥ p₁ ≤ h₁ ∧
          H₂ *ᵥ (X₂d *ᵥ (X₁ *ᵥ p₁ + x₁ - x₂) + (1 - X₂d * X₂) *ᵥ w) ≤ h₂ ∧
          (1 - X₂ * X₂d) *ᵥ (X₁ *ᵥ p₁ + x₁ - x₂) = 0 ∧
          x = x₁ + X₁ *ᵥ p₁} := by -- --- PROOF ---
  ext x
  constructor
  -- `w = p₂` reproduces `p₂`, and `v = X₂ p₂` is in the range
  · rintro ⟨⟨p₁, hp₁, rfl⟩, p₂, hp₂, he⟩
    have hv : X₁ *ᵥ p₁ + x₁ - x₂ = X₂ *ᵥ p₂ := by rw [add_comm, he]; abel
    refine ⟨p₁, p₂, fun i => HPolytope.mem_ineqs_iff.mp hp₁ i, ?_, ?_, rfl⟩
    · rw [hv, sub_mulVec, one_mulVec, mulVec_mulVec, add_sub_cancel]
      exact fun i => HPolytope.mem_ineqs_iff.mp hp₂ i
    · rw [hv, sub_mulVec, one_mulVec, mulVec_mulVec, hg, sub_self]
  -- the equality row makes `p₂ = X₂† v + (I - X₂† X₂) w` a solution
  · rintro ⟨p₁, w, hp₁, hp₂, hr, rfl⟩
    refine ⟨⟨p₁, HPolytope.mem_ineqs_iff.mpr hp₁, rfl⟩, _, HPolytope.mem_ineqs_iff.mpr hp₂, ?_⟩
    have hrange : X₂ *ᵥ (X₂d *ᵥ (X₁ *ᵥ p₁ + x₁ - x₂)) = X₁ *ᵥ p₁ + x₁ - x₂ := by
      rw [sub_mulVec, one_mulVec, sub_eq_zero] at hr
      rw [mulVec_mulVec, ← hr]
    rw [mulVec_add, hrange, sub_mulVec, one_mulVec, mulVec_sub, mulVec_mulVec,
      ← Matrix.mul_assoc, hg, sub_self, add_zero]
    abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
