module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# The F_W-radius of a zonotope

[1, Def. 4]: for `W = Wᵀ ≻ 0`, `ℓ_{F,W} = ‖⟨p, H⟩‖_{F,W} = ‖H‖_{F,W} = √tr(Hᵀ W H)`, the
weighted Frobenius norm of the generator matrix, `√Σⱼ gⱼᵀ W gⱼ` over the generators `gⱼ`. It
ignores the center. At `W = I` it is the F-radius of Combastel's zonotopic Kalman filter.

## References

* [1] Y. Wang, V. Puig and G. Cembrano. "Set-membership approach and Kalman observer based on
      zonotopes for discrete-time descriptor systems". Automatica, 93:435-443, 2018.
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
