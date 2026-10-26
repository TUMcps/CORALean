module

public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.Specification.STL.Operations.DepBox

@[expose] public section

/-!
# `interval(Z)` as a zonotope over a float scalar

[1, Alg. 1]'s `interval(Z)` with the center and generators held in `𝕋`: the center of `Z` and the
`n` generators `r_i e_i`, `r_i = Σ_l |G_{i,l}|` rounded up. The error box of `Z` stays as it is, so
the box hull of the float zonotope is the box hull of its nominal part, widened by the box.
Soundness is `STL.depBoxFloat_outer`.

## Inputs
* `Z` – float zonotope

## Output
* the interval hull of the zonotope as a zonotope

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `interval(Z)` of [1, Alg. 1], as a float zonotope with `n` axis-aligned generators. -/
def STL.depBoxFloat (Z : Float.Zonotope (Vec 𝕋 n)) : Float.Zonotope (Vec 𝕋 n) where
  h := n
  -- 3. `interval(Z) = [c − r, c + r]`: the center of `Z` is the center of the box
  c := Z.c
  -- 3. … with `r_i = Σ_l |G_{i,l}|` rounded up, the generator `r_i e_i` along each axis
  G := fun l i => if i = l then sumUp (fun j => absolute (Z.G j l)) else zero
  I_error := Z.I_error

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
