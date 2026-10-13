import CORALean.ContSet.HPolytope.Float.Operations.MinkDiffOf
import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

/-!
# The float certified Minkowski difference is inside the exact one

The exact layer's argument, with one rounding to account for: a point `x` of the
result and any `y` of the subtrahend give `A (x + y) ≤ (b ⊖ u) + u ≤ b`, the
stored bound having been rounded downward. Equality rows need the subtrahend in
their kernel, as over ℝ.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.minkDiffOf_inner (P : HPolytope 𝕋 (Vec 𝕋 n)) (T : Set (Vec ℝ n))
    (u : ∀ i, FloatBound 𝕋 T (rowLin P.A i))
    (hker : ∀ i, ∀ y ∈ T, (toRealMat P.Ae *ᵥ y) i = 0) :
    (P.minkDiffOf T u).construct ⊆ minkowskiDiff P.construct T := by -- --- PROOF ---
  intro x hx y hy
  obtain ⟨hle, heq⟩ := HPolytope.mem_construct_iff.mp hx
  refine HPolytope.mem_construct_iff.mpr ⟨fun i => ?_, fun i => ?_⟩
  · have h1 : (toRealMat P.A *ᵥ x) i ≤ toReal (subDown (P.b i) (u i).val) := hle i
    have h2 : (toRealMat P.A *ᵥ y) i ≤ toReal (u i).val := (u i).le y hy
    have h3 := subDown_le_sub (P.b i) (u i).val
    rw [mulVec_add, Pi.add_apply]
    linarith
  · rw [mulVec_add, Pi.add_apply, hker i y hy, add_zero]
    exact heq i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
