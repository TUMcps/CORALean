module

public import CORALean.ContSet.SpectraShadow.Real.SpectraShadow

@[expose] public section

/-!
# `SpectraShadow.empty`

CORA's `spectraShadow.empty(n)`: the inequality `-1 ⪰ 0` on a `1 × 1` matrix, which no
coefficient meets, over `n` free coefficients that carry the unit vectors (CORA's `[-1 0 … 0]`).

## Inputs
* `n` – natural number

## Output
* `spectraShadow.empty(n)`: the `1 × 1` inequality `-1 ⪰ 0` over `n` free coefficients
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `spectraShadow.empty(n)`: the `1 × 1` inequality `-1 ⪰ 0` over `n` free coefficients. -/
def SpectraShadow.empty (n : ℕ) : SpectraShadow (Vec ℝ n) :=
  ⟨1, n, !![-1], fun _ => 0, 0, fun i => Pi.single i (1 : ℝ)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
