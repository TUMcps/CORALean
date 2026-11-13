module

public import CORALean.HybridDynamics.Operations.ZonoGirardBoxFloat
public import CORALean.HybridDynamics.Operations.OrthDefectFloat
public import CORALean.HybridDynamics.Operations.Basic
public import CORALean.Global.StepOf
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Zonotope.Float.Operations.Plus
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# `Location.zonoGirardMemberFloat`

The member of `guardIntersect_zonoGirard` for one basis `B`: the box `I` of the joined cuts, in the
coordinates `Bᵀ x`, mapped back by `B`. For an orthogonal `B` that is `B zonotope(I)`; a basis
computed in floats is orthogonal only up to rounding, and a state `x` is `B (Bᵀ x)` plus
`(I - B Bᵀ) x`. The second term is added as the box `[-r, r]`, `r_i = Σ_j |I - B Bᵀ|_ij |X|_j`
rounded up, `|I - B Bᵀ|` the larger end of the defect box `[I - B Bᵀ]` in absolute value and `X` the
joined boxes of the reach sets, which holds `x`. Where the defect box is zero, as for the identity,
the term is left out.

## Inputs
* `B` – basis
* `R₀` – initial zonotope
* `Rs` – reach sets
* `nv` – guard normal
* `γ` – guard offset

## Output
* zonotope that holds every state of a reach set on the hyperplane, whatever the basis
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float CORALean.Float.FloatOps Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `B zonotope(I)`, plus the box `[-r, r]` where the defect box is not the zero matrix. -/
def Location.zonoGirardMemberFloat (B : Mat 𝕋 n n) (R₀ : Zonotope (Vec 𝕋 n))
    (Rs : List (Zonotope (Vec 𝕋 n))) (nv : Vec 𝕋 n) (γ : 𝕋) : Zonotope (Vec 𝕋 n) :=
  Location.orthDefectFloat B (Location.joinedBoxFloat R₀ Rs)         -- the defect, for the states
    (Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) B                 -- of the sets' joined boxes
      (Location.zonoGirardBoxFloat B R₀ Rs nv γ).zonotope)           -- `B zonotope(I)`

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
