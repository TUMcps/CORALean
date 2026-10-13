import CORALean.ContSet.Zonotope.Float.Theorems.MinnormBall
import CORALean.ContSet.Zonotope.Real.Theorems.MinnormBallSubset

/-!
# The computed `minnorm` bounds the exact one

When the stored generators span the space, the exact `Zonotope.minnorm` of the zonotope they
describe is the radius of a ball inside it (`Zonotope.minnorm_ball_subset`), so the float
`Zonotope.minnorm`, which bounds the radius of every such ball (`minnorm_ball`), is at least the
exact value. The value is the nominal zonotope's, as CORA's `minnorm` reads `Z.c` and `Z.G` only.

Source: [1].

## References

* [1] `contSet/@zonotope/minnorm.m`, CORA (Sep. 2025).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.minnorm_le (p : ℕ) (Z : Zonotope (Vec 𝕋 (n + 1))) (U : 𝕋)
    (hU : Z.minnorm p = some U)
    (hspan : Submodule.span ℝ (Set.range (nominal Z).G) = ⊤) :
    (nominal Z).minnorm ≤ toReal U := by -- --- PROOF ---
  -- the exact value is nonnegative, as an infimum of nonnegative offsets
  have hnn : 0 ≤ (nominal Z).minnorm := Real.sInf_nonneg (by
    rintro _ ⟨S, -, rfl⟩
    exact CORALean.Real.Zonotope.minnormOffset_nonneg (nominal Z) S)
  -- its ball lies in the zonotope, so the bound applies
  exact Zonotope.minnorm_ball p Z U hU _ hnn fun y hy =>
    CORALean.Real.Zonotope.minnorm_ball_subset (nominal Z) hspan y hy

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
