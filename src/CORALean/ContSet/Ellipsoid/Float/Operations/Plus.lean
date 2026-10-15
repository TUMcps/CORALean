module

public import CORALean.ContSet.Ellipsoid.Float.Operations.CenterResidual
public import CORALean.ContSet.Ellipsoid.Float.Operations.BoxRadius
public import CORALean.ContSet.Ellipsoid.Float.Operations.Inflate
public import CORALean.ContSet.Ellipsoid.Float.Operations.IsPsd
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.MatPlus
public import CORALean.ContSet.Interval.Float.Operations.Smul

@[expose] public section

/-!
# `Ellipsoid.plus`

The Minkowski sum of two ellipsoids is not an ellipsoid, so this encloses it and carries the free
parameter every enclosure of it does: the shape `s₁² Q₁ + s₂² Q₂` at two scalings with
`1/s₁² + 1/s₂² ≤ 1`, which Kurzhanski and Varaiya's `l` meets with equality (`√(1+1/l)`,
`√(1+l)`). The pair is a hypothesis the caller discharges, an unverified routine proposing it.

The shape is computed as an interval matrix and stored rounded upward (`inflate`), the center's
rounding paid into the box. An operand whose `Q` `isPsd` cannot certify enters not through its
shape but through its box `q ± √diag(Q)` (`boxRadius`), which holds its nominal part whatever `Q`
is; the scaled sum would not, a refused `Q` being free to cancel the other.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.plus (s₁ s₂ : 𝕋) (E₁ E₂ : Ellipsoid 𝕋 n) : Ellipsoid 𝕋 n :=
  -- the operands whose shape is certified enter as `s² Q`, the others as their box
  let c₁ : Bool := Ellipsoid.isPsd E₁.Q
  let c₂ : Bool := Ellipsoid.isPsd E₂.Q
  let X₁ : Interval (Mat 𝕋 n n) := if c₁ then
      Interval.smul (mulDown s₁ s₁) (mulUp s₁ s₁) (Interval.point E₁.Q)
    else Interval.point fun _ _ => zero
  let X₂ : Interval (Mat 𝕋 n n) := if c₂ then
      Interval.smul (mulDown s₂ s₂) (mulUp s₂ s₂) (Interval.point E₂.Q)
    else Interval.point fun _ _ => zero
  let B₁ : Interval (Vec 𝕋 n) := if c₁ then Interval.origin n
    else Interval.symmetric (Ellipsoid.boxRadius 64 E₁)
  let B₂ : Interval (Vec 𝕋 n) := if c₂ then Interval.origin n
    else Interval.symmetric (Ellipsoid.boxRadius 64 E₂)
  -- `s₁² Q₁ + s₂² Q₂`, entrywise between two roundings, stored rounded upward
  { Q := Ellipsoid.inflate (Interval.matPlus X₁ X₂)
    q := fun i => addDown (E₁.q i) (E₂.q i)
    I_error := (((E₁.I_error.plus E₂.I_error).plus (Ellipsoid.centerResidual E₁.q E₂.q)).plus
      B₁).plus B₂ }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
