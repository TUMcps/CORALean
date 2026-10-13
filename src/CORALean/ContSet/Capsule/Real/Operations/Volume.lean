import CORALean.ContSet.Capsule.Real.Capsule
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# `Capsule.volume`

CORA's `@capsule/volume_`: the volume of a ball of radius `r` plus that of the cylinder it sweeps
along the segment, the `(n-1)`-ball of radius `r` times the segment's length `2‖g‖`,

    π^(n/2) / Γ(n/2 + 1) r^n + π^((n-1)/2) / Γ((n-1)/2 + 1) r^(n-1) · 2‖g‖,

and `0` for an empty capsule (`r < 0`) or for `n = 0`. The Lebesgue measure of a zero-dimensional
space is `1`, not CORA's `0`, so `volume_eq` is stated for `n > 0`. The norm is written out as
`Real.sqrt`, as in `Capsule.construct`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Capsule.volume (C : Capsule n) : ENNReal :=
  if n = 0 ∨ C.r < 0 then 0
  else
    let Vball := Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2 + 1) * C.r ^ n   -- volBall
    let Vball' := Real.pi ^ (((n : ℝ) - 1) / 2) / Real.Gamma (((n : ℝ) - 1) / 2 + 1)
      * C.r ^ (n - 1)                                                              -- volBall_minus1
    let Vcyl := Vball' * (2 * Real.sqrt (∑ i, C.g i ^ 2))                           -- volCylinder
    ENNReal.ofReal (Vball + Vcyl)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
