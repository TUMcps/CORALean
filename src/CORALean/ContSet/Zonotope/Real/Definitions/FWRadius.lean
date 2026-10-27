module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# The F_W-radius of a zonotope

[1, Def. 4]: for `W = Wᵀ ≻ 0`, `ℓ_{F,W} = ‖⟨p, H⟩‖_{F,W} = ‖H‖_{F,W} = √tr(Hᵀ W H)`, the
weighted Frobenius norm of the generator matrix, `√Σⱼ gⱼᵀ W gⱼ` over the generators `gⱼ`. It
ignores the center. [2, Def. 2] defines the same radius, `‖⟨c, R⟩‖_{F,W} = ‖R‖_{F,W} = √tr(Rᵀ W R)`
for `W = Wᵀ ≻ 0`, and [2, Def. 3] the F-radius `‖R‖_F` as its value at `W = I`, which is
`fwRadius 1`.

## Inputs
* `W` – weight matrix
* `Z` – zonotope

## Output
* weighted Frobenius radius of the generators

## References

* [1] [Y. Wang, V. Puig and G. Cembrano. "Set-membership approach and Kalman observer based on
      zonotopes for discrete-time descriptor systems". Automatica,
      2018.](../../../../../../references/2018/wang-automatica-descriptor-observer.md)
* [2] [C. Combastel. "Zonotopes and Kalman observers: Gain optimality under distinct uncertainty
      paradigms and robust convergence". Automatica,
      2015.](../../../../../../references/2015/combastel-automatica-zonotopes-kalman.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `√Σⱼ gⱼᵀ W gⱼ`. -/
noncomputable def Zonotope.fwRadius (W : Mat ℝ n n) (Z : Zonotope (Vec ℝ n)) : ℝ :=
  Real.sqrt (∑ j, Z.G j ⬝ᵥ (W *ᵥ Z.G j))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
