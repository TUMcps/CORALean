module

public import CORALean.Global.Tensor
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# An inner box of a preconditioned function gives an inner parallelotope

[1, Sec. II-B]: for `C` nonsingular, an interval vector `z ⊆ range(Cf, x)` gives the skewed
box `{C⁻¹z | z ∈ z} ⊆ range(f, x)`; [1] takes `C` the inverse of the center of the interval
Jacobian. Stated for any set `Z`, as nothing about a box is used.

## Inputs
* `C` – preconditioning matrix
* `f` – map
* `X` – domain
* `Z` – set inside the preconditioned range

## Hypotheses
* `hC` – the preconditioner is invertible
* `hZ` – the set lies in the range of the preconditioned map

## Conclusion
* the image of the set under the inverse lies in the range of the map

## References

* [1] E. Goubault and S. Putot. "Robust Under-Approximations and Application to Reachability of
      Non-Linear Control Systems With Disturbances". IEEE Control Systems Letters, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. II-B]: `Z ⊆ range(Cf, X)` gives `C⁻¹Z ⊆ range(f, X)`. -/
theorem image_inv_subset_range_of_subset_range_mulVec {C : Mat ℝ n n} (hC : IsUnit C.det)
    {f : (Fin m → ℝ) → (Fin n → ℝ)} {X : Set (Fin m → ℝ)} {Z : Set (Fin n → ℝ)}
    (hZ : Z ⊆ (fun x => C *ᵥ f x) '' X) : (C⁻¹ *ᵥ ·) '' Z ⊆ f '' X := by
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨x, hx, rfl⟩ := hZ hz
  exact ⟨x, hx, by
    show f x = C⁻¹ *ᵥ (C *ᵥ f x); rw [mulVec_mulVec, nonsing_inv_mul C hC, one_mulVec]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
