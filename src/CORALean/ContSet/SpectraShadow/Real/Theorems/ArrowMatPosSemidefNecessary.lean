module

public import CORALean.ContSet.SpectraShadow.Real.Theorems.ArrowMatQuadForm
public import Mathlib.Analysis.Matrix.Order

@[expose] public section

/-!
# What a positive semidefinite arrowhead matrix needs

For `N ≥ 1`, a positive semidefinite `arrowMat s t w` has `s ≥ 0`, and `w = 0` if `s = 0`: the
diagonal gives the first, and for the second a nonzero `wᵢ` lets the cross term `2 a b wᵢ` beat `t
a²`.

## Inputs
* `s` – real number
* `t` – real number
* `w` – weights of length `N`

## Hypotheses
* `hN` – `0 < N`
* `h` – `(arrowMat s t w)` is positive semidefinite

## Conclusion
* `s` is nonnegative and `w` vanishes when `s = 0`
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix

variable {N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem arrowMat_posSemidef_necessary {s t : ℝ} {w : Vec ℝ N} (hN : 0 < N)
    (h : (arrowMat s t w).PosSemidef) : -- --- CONCL ---
    0 ≤ s ∧ (s = 0 → w = 0) := by -- --- PROOF ---
  have hQ := fun x => h.dotProduct_mulVec_nonneg x
  simp only [star_trivial] at hQ
  -- the form at `(0, e₀)` is `s`
  have hs : 0 ≤ s := by
    have := hQ (Fin.cons 0 (Pi.single ⟨0, hN⟩ 1))
    rw [arrowMat_quadForm] at this
    simpa using this
  refine ⟨hs, fun hs0 => ?_⟩
  funext i
  by_contra hwi
  have hwi' : w i ≠ 0 := hwi
  -- a test vector with `a = 1` and `y = b eᵢ`
  have := hQ (Fin.cons 1 (Pi.single i (-(t + 1) / (2 * w i))))
  rw [arrowMat_quadForm] at this
  simp [hs0] at this
  field_simp at this
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
