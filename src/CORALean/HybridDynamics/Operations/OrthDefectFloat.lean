module

public import CORALean.Global.StepOf
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Zonotope.Float.Operations.Plus
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `Location.orthDefectFloat`

The correction that makes a basis `B` computed in floats safe where `B Bᵀ = 1` was assumed. A state
`x` is `B (Bᵀ x) + (I - B Bᵀ) x`; a set `Z` that holds `B (Bᵀ x)` is widened by the box `[-r, r]`,
`r_i = Σ_j |I - B Bᵀ|_ij |X|_j` rounded up, `|I - B Bᵀ|` the larger end of the defect box
`[I - B Bᵀ]` in absolute value and `X` a box that holds `x`. Where the defect box is exactly the
zero matrix, as for the identity, `Z` is returned unchanged.

## Inputs
* `B` – basis
* `X` – box that holds the states
* `Z` – zonotope that holds `B (Bᵀ x)`

## Output
* zonotope that holds `x`
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
@[step_of Location.orthDefectFloat]
def Location.step_orthDefect (B : Mat 𝕋 n n) : Interval (Mat 𝕋 n n) :=
  let e : Fin n → Fin n → 𝕋 := fun i j => if i = j then one else zero  -- the identity
  ⟨fun i j => subDown (e i j) (dotUp (B i) (B j)),                  -- `B Bᵀ` rounded up
   fun i j => subUp (e i j) (dotDown (B i) (B j))⟩                  -- and down


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Z`, plus the box `[-r, r]` where the defect box is not the zero matrix. -/
def Location.orthDefectFloat (B : Mat 𝕋 n n) (X : Interval (Vec 𝕋 n)) (Z : Zonotope (Vec 𝕋 n)) :
    Zonotope (Vec 𝕋 n) :=
  let E := Location.step_orthDefect B                                -- `[I - B Bᵀ]`
  let mag := fun (a b : 𝕋) => maximum (absolute a) (absolute b)      -- largest absolute value
  let r : Vec 𝕋 n := fun i => sumUp fun j =>                         -- bound of `(I - B Bᵀ) x`
    mulUp (mag (E.inf i j) (E.sup i j)) (mag (X.inf j) (X.sup j))
  let isZero := (List.finRange n).all fun i => (List.finRange n).all fun j =>
    FloatOps.le (E.sup i j) FloatOps.zero && FloatOps.le FloatOps.zero (E.inf i j)
  if isZero then Z
  else Z.plus (Interval.zonotope (⟨-r, r⟩ : Interval (Vec 𝕋 n)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
