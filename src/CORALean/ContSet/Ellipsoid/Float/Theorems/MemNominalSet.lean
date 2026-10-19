module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.MemConstructIff
public import CORALean.ContSet.Ellipsoid.Float.Theorems.Basic

@[expose] public section

/-!
# The points of the nominal part

`q + G u` for `u` in the unit ball, `G` the square root of the nominal shape matrix: `Q` read as
reals where it is positive semi-definite, `0` where CORA's constructor refuses it, and the center
the stored one either way (`nominal_q`).

## Inputs
* `E` – ellipsoid
* `x` – point

## Hypotheses
* none

## Conclusion
* `x` is in the nominal part iff it is the center plus a shape image of the unit ball
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.mem_nominalSet_iff [SoundFloatArithmetic 𝕋] {E : Ellipsoid 𝕋 n}
    {x : Vec ℝ n} :
    x ∈ InflatedContSet.nominalSet E ↔ ∃ u : Vec ℝ n, ‖u‖₂ ≤ 1 ∧
      x = toRealVec E.q + (InflatedContSet.nominal E).ellipsoid.G *ᵥ u := by
  rw [← E.nominal_q]
  exact CORALean.Real.Ellipsoid.mem_construct_iff

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
