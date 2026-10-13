module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# The extent of a zonotope in a direction

[1, Def. 7]: for `Z = p ⊕ H Bᵐ` and `c ∈ ℝⁿ`, the extent of `cᵀx` over `Z` is `cᵀp ± ‖Hᵀc‖₁`, can
be obtained easily"; `supportRadius` is the `‖Hᵀc‖₁ = Σⱼ |cᵀGⱼ|` of it. That this is how far `cᵀx`
reaches on either side of `cᵀp` is `support_dotProduct`.

## References

* [1] J. M. Bravo, T. Alamo and E. F. Camacho. "Bounded error identification of systems with
      time-varying parameters". IEEE Transactions on Automatic Control, 51(7):1144-1150, 2006.
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

/-- `‖Hᵀc‖₁ = Σⱼ |cᵀGⱼ|`. -/
def Zonotope.supportRadius (Z : Zonotope (Vec ℝ n)) (c : Vec ℝ n) : ℝ :=
  ∑ j, |c ⬝ᵥ Z.G j|

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
