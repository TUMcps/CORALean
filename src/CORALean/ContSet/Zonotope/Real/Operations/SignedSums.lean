module

public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# `Zonotope.signedSums`

[1, Def. 1]: `Z±(R) = {R σ : σ ∈ {-1, 1}ᵖ}`, the images by `R` of the `2ᵖ` vertices of the
unit cube, for the generators `R` as a family of columns. Centered; the center is added by the
caller (`c + Z±(R)`, [1, Eq. 41]).

## Inputs
* `R` – family of vectors

## Output
* set of all signed sums

## References

* [1] M. Maïga, N. Ramdani, L. Travé-Massuyès and C. Combastel. "A Comprehensive Method for
      Reachability Analysis of Uncertain Nonlinear Hybrid Systems". IEEE Transactions on Automatic
      Control, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Z±(R)`. -/
def Zonotope.signedSums (R : Fin p → Vec ℝ n) : Set (Vec ℝ n) :=
  {x | ∃ σ : Fin p → Bool, x = ∑ j, (if σ j then (1 : ℝ) else -1) • R j}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
