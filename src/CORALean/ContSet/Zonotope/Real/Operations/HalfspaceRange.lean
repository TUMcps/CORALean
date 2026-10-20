module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `Zonotope.halfspaceRange`

[1, Sec. 5.2]: where a zonotope lies against a halfspace `H = {x | nᵀx ≤ d}`, read off
the one-dimensional zonotope `(nᵀ ⊗ Z) ⊕ (-d) = ω_c ⊕ ([-1, 1] ⊗ ω⁽¹⁾) ⊕ ... ⊕ ([-1, 1] ⊗ ω⁽ᵖ⁾)`
as the interval `[ω̲, ω̄] = [ω_c - Σᵢ |ω⁽ⁱ⁾|, ω_c + Σᵢ |ω⁽ⁱ⁾|]`, one `let` per printed quantity.
The paper uses it to bound the times a reachable set meets the guard.

## Inputs
* `nv` – halfspace normal
* `d` – halfspace offset
* `Z` – zonotope

## Output
* interval of values over `Z`

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. 5.2]: `[ω̲, ω̄]`, the range of `nᵀx - d` over `Z`. -/
noncomputable def Zonotope.halfspaceRange (nv : Vec ℝ n) (d : ℝ) (Z : Zonotope (Vec ℝ n)) :
    Interval ℝ :=
  let ωc := nv ⬝ᵥ Z.c - d                  -- the center of `(nᵀ ⊗ Z) ⊕ (-d)`
  let ω : Fin Z.h → ℝ := fun i => nv ⬝ᵥ Z.G i  -- its generators
  ⟨ωc - ∑ i, |ω i|, ωc + ∑ i, |ω i|⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
