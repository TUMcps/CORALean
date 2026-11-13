module

public import CORALean.HybridDynamics.Operations.ZonoGirardBoxFloat
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


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The box of `I - B Bᵀ`: the identity minus the product rounded up for the lower end, rounded
down for the upper. -/
@[step_of Location.zonoGirardMemberFloat]
def Location.step_orthDefect (B : Mat 𝕋 n n) : Interval (Mat 𝕋 n n) :=
  let e : Fin n → Fin n → 𝕋 := fun i j => if i = j then one else zero  -- the identity
  ⟨fun i j => subDown (e i j) (dotUp (B i) (B j)),                  -- `B Bᵀ` rounded up
   fun i j => subUp (e i j) (dotDown (B i) (B j))⟩                  -- and down


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `B zonotope(I)`, plus the box `[-r, r]` where the defect box is not the zero matrix. -/
def Location.zonoGirardMemberFloat (B : Mat 𝕋 n n) (R₀ : Zonotope (Vec 𝕋 n))
    (Rs : List (Zonotope (Vec 𝕋 n))) (nv : Vec 𝕋 n) (γ : 𝕋) : Zonotope (Vec 𝕋 n) :=
  let main := Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) B
    (Location.zonoGirardBoxFloat B R₀ Rs nv γ).zonotope              -- `B zonotope(I)`
  let E := Location.step_orthDefect B                                -- `[I - B Bᵀ]`
  let X := (Rs.map Zonotope.interval).foldl Interval.or R₀.interval  -- the sets' boxes, joined
  let mag := fun (a b : 𝕋) => maximum (absolute a) (absolute b)      -- largest absolute value
  let r : Vec 𝕋 n := fun i => sumUp fun j =>                         -- bound of `(I - B Bᵀ) x`
    mulUp (mag (E.inf i j) (E.sup i j)) (mag (X.inf j) (X.sup j))
  let isZero := (List.finRange n).all fun i => (List.finRange n).all fun j =>
    FloatOps.le (E.sup i j) FloatOps.zero && FloatOps.le FloatOps.zero (E.inf i j)
  if isZero then main
  else main.plus (Interval.zonotope (⟨-r, r⟩ : Interval (Vec 𝕋 n)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
