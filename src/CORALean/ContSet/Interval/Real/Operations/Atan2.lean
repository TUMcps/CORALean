module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

@[expose] public section

/-!
# `Interval.atan2`, as CORA computes it

`@interval/atan2.m`: the hull of `atan2` at the four corners `(inf, inf)`, `(inf, sup)`,
`(sup, inf)`, `(sup, sup)` of the two operands, coordinate by coordinate. `atan2 y x` is the
argument of `x + i y`, in `(-π, π]`.

This is **not an enclosure** across the branch cut, the negative real axis, where `atan2` jumps
from `π` to `-π + ε`: see `Interval.atan2_cora_counterexample`. Formalized as CORA computes it,
for that reason; no enclosure theorem is claimed.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `atan2(I1, I2)`: `I1` the `y` operand, `I2` the `x` operand. -/
noncomputable def Interval.atan2 (I₁ I₂ : Interval (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i =>
    min (min (Complex.arg ⟨I₂.inf i, I₁.inf i⟩) (Complex.arg ⟨I₂.sup i, I₁.inf i⟩))
      (min (Complex.arg ⟨I₂.inf i, I₁.sup i⟩) (Complex.arg ⟨I₂.sup i, I₁.sup i⟩))
  sup := fun i =>
    max (max (Complex.arg ⟨I₂.inf i, I₁.inf i⟩) (Complex.arg ⟨I₂.sup i, I₁.inf i⟩))
      (max (Complex.arg ⟨I₂.inf i, I₁.sup i⟩) (Complex.arg ⟨I₂.sup i, I₁.sup i⟩))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
