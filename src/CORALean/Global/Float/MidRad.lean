module

public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# A float with a bound on its distance from the real number it stands for

CORA computes in doubles and keeps no record of what rounding costs. `MidRad` keeps the value it
computes, `v`, rounded the way CORA rounds at round-to-nearest (`mulDown`, `addDown`, which are
that at the dtype `nearest`), and beside it a radius `r` rounded up, so that a real number `x` the
value stands for is within `r` of `v` (`MidRad.Encloses`). A product or sum adds the radii it
inherits and its own rounding (`mulUp - mulDown`), so a chain of operations ends with the value
CORA computes and a sound bound on its error (`PolyZonotope.evalPowers_outer` proves the step).
-/

-- Authors:       Claude Opus 5.5
-- Written:       16-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋]


-- ========================================  MAIN TYPE  ========================================= --

/-- A computed value `v` and a radius `r` around it. -/
structure MidRad (𝕋 : Type) where
  v : 𝕋
  r : 𝕋

/-- A float as it is, of radius zero. -/
def MidRad.exact (x : 𝕋) : MidRad 𝕋 := ⟨x, zero⟩

/-- The sum: the values added as CORA adds them, the radii and the rounding added upward. -/
def MidRad.add (a b : MidRad 𝕋) : MidRad 𝕋 :=
  ⟨addDown a.v b.v, addUp (addUp a.r b.r) (subUp (addUp a.v b.v) (addDown a.v b.v))⟩

/-- The product: `|a.v| b.r + |b.v| a.r + a.r b.r` and the rounding, all upward. -/
def MidRad.mul (a b : MidRad 𝕋) : MidRad 𝕋 :=
  ⟨mulDown a.v b.v, addUp (addUp (mulUp (absolute a.v) b.r) (mulUp (absolute b.v) a.r))
    (addUp (mulUp a.r b.r) (subUp (mulUp a.v b.v) (mulDown a.v b.v)))⟩

variable [SoundFloatArithmetic 𝕋]

/-- The real number `x` is within the radius of the value. A structure, so that unification
never unfolds it into the arithmetic of a long run. -/
structure MidRad.Encloses (b : MidRad 𝕋) (x : ℝ) : Prop where
  abs_sub_le : |x - toReal b.v| ≤ toReal b.r

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
