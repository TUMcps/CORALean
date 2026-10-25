module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# A preconditioned inclusion implies the original one

[1, Eq. 3]: for a regular real matrix `C`, `C y ⊆ range(C f, x)` implies
`y ⊆ range(f, x)`. The proof is the paper's: a `y ∈ y` has `C y = C f(x)` for some `x ∈ x`,
and `C` is injective. The converse fails in general, which is why (3) is "more restrictive".

## Inputs
* `f` – map
* `X` – domain
* `Y` – target set
* `C` – preconditioning matrix

## Hypotheses
* `hC` – the preconditioner is regular
* `h` – the preconditioned target lies in the preconditioned range

## Conclusion
* the target set lies in the range of the map

## References

* [1] A. Goldsztejn and L. Jaulin. "Inner approximation of the range of vector-valued functions".
      Reliable Computing, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 3]: `C y ⊆ range(C f, x)` gives `y ⊆ range(f, x)`, for `det C ≠ 0`. -/
theorem subset_image_of_preconditioned_subset {f : (Fin n → ℝ) → (Fin n → ℝ)}
    {X Y : Set (Fin n → ℝ)} (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.det ≠ 0)
    (h : (fun y => C *ᵥ y) '' Y ⊆ (fun x => C *ᵥ f x) '' X) : -- --- CONCL ---
    Y ⊆ f '' X := by -- --- PROOF ---
  intro y hy
  obtain ⟨x, hx, hxy⟩ := h ⟨y, hy, rfl⟩
  have hinj : Function.Injective (fun z => C *ᵥ z) :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det C).mpr (isUnit_iff_ne_zero.mpr hC))
  exact ⟨x, hx, hinj hxy⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
