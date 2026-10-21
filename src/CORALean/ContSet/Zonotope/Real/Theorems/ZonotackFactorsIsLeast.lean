module

public import CORALean.ContSet.Zonotope.Real.Operations.ZonotackFactors
public import CORALean.ContSet.Zonotope.Real.Theorems.NegSumAbsLeSumMul
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Sign.Basic
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The falsification candidate is the vertex nearest the unsafe halfspace

`ỹ = c_y + G_y β̃` with `β̃ = -sign(a G_y)` (`Zonotope.zonotackFactors`) is a point of `Y`, and
`a ỹ = a c_y - |a G_y| 1` is the least value of `a y` over `Y`: the boundary point [1, Eq. 9]
asks for, on the side of the unsafe set `a y ≤ b`. So if any point of `Y` satisfies the row,
`ỹ` does; with one row (`p = 1`), `ỹ ∈ Y ∩ U` whenever `Y ∩ U ≠ ∅`.

## Inputs
* `Y` – output zonotope
* `a` – normal vector of the unsafe set

## Hypotheses
* none

## Conclusion
* `a ỹ` is the least value of `a y` over `Y`, attained at `ỹ ∈ Y`

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Out of the Shadows: Exploring a Latent Space for
      Neural Network Verification". ICLR, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       21-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The candidate vertex attains the least value of `a y` over `Y`. -/
theorem Zonotope.zonotackFactors_isLeast (Y : Zonotope (Vec ℝ k)) (a : Vec ℝ k) : -- --- CONCL ---
    IsLeast ((fun y => a ⬝ᵥ y) '' Y.construct)
      (a ⬝ᵥ (Y.c + ∑ j, Y.zonotackFactors a j • Y.G j)) := by -- --- PROOF ---
  -- `a ỹ = a c_y - Σ |a G_y(·,j)|`, as `-sign(x) x = -|x|`
  have hval : a ⬝ᵥ (Y.c + ∑ j, Y.zonotackFactors a j • Y.G j) =
      a ⬝ᵥ Y.c - ∑ j, |a ⬝ᵥ Y.G j| := by
    simp only [dotProduct_add, dotProduct_sum, dotProduct_smul, smul_eq_mul,
      Zonotope.zonotackFactors, neg_mul, sign_mul_self, Finset.sum_neg_distrib, sub_eq_add_neg]
  refine ⟨⟨_, ⟨Y.zonotackFactors a, fun j => ?_, rfl⟩, rfl⟩, ?_⟩
  · -- the factors are signs, in `[-1, 1]`
    simp only [Zonotope.zonotackFactors, abs_neg]
    rcases lt_trichotomy (a ⬝ᵥ Y.G j) 0 with h | h | h
    · simp [sign_neg h]
    · simp [h]
    · simp [sign_pos h]
  · rintro _ ⟨y, ⟨β, hβ, rfl⟩, rfl⟩
    rw [hval]
    have hlow := Zonotope.neg_sum_abs_le_sum_mul Finset.univ β (fun j => a ⬝ᵥ Y.G j) hβ
    simp only [dotProduct_add, dotProduct_sum, dotProduct_smul, smul_eq_mul]
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
