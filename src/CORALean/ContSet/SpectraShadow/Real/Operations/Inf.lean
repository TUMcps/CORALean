import CORALean.ContSet.SpectraShadow.Real.SpectraShadow

/-!
# `SpectraShadow.Inf`

CORA's `spectraShadow.Inf(n)`: the inequality `1 ⪰ 0` on a `1 × 1` matrix, which every
coefficient meets, over `n` free coefficients that carry the unit vectors (CORA's `[1 0 … 0]`).
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `spectraShadow.Inf(n)`: the `1 × 1` inequality `1 ⪰ 0` over `n` free coefficients. -/
def SpectraShadow.Inf (n : ℕ) : SpectraShadow (Vec ℝ n) :=
  ⟨1, n, !![1], fun _ => 0, 0, fun i => Pi.single i (1 : ℝ)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
