module

public import CORALean.ContSet.Zonotope.Real.Operations.SupportRadius

@[expose] public section

/-!
# The support strip of a zonotope

[1, Def. 8]: the strip `{x | q ≤ cᵀx ≤ r}` between the hyperplanes tangent to the zonotope `Z = p ⊕
H Bᵐ` with normal `c`, `r = max_{x ∈ Z} cᵀx = cᵀp + ‖Hᵀc‖₁` and `q = min_{x ∈ Z} cᵀx = cᵀp -
‖Hᵀc‖₁` ([1, Def. 7]; the values are `support_dotProduct`'s). It is the smallest strip of this
direction that contains `Z`.

## Inputs
* `Z` – zonotope
* `c` – direction

## Output
* strip around the center along `c`

## References

* [1] J. M. Bravo, T. Alamo and E. F. Camacho. "Bounded error identification of systems with
      time-varying parameters". IEEE Transactions on Automatic Control, 2006.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `{x | cᵀp - ‖Hᵀc‖₁ ≤ cᵀx ≤ cᵀp + ‖Hᵀc‖₁}`. -/
def Zonotope.supportStrip (Z : Zonotope (Vec ℝ n)) (c : Vec ℝ n) : Set (Vec ℝ n) :=
  {x | c ⬝ᵥ Z.c - Z.supportRadius c ≤ c ⬝ᵥ x ∧ c ⬝ᵥ x ≤ c ⬝ᵥ Z.c + Z.supportRadius c}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
