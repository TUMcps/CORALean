module

public import CORALean.ContSet.HPolytope.Float.Operations.MinkDiffOf
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

@[expose] public section

/-!
# The float certified Minkowski difference is inside the exact one

The exact layer's argument, with one rounding to account for: a point `x` of the
result and any `y` of the subtrahend give `A (x + y) ≤ (b ⊖ u) + u ≤ b`, the
stored bound having been rounded downward. Equality rows need the subtrahend in
their kernel, as over ℝ. The error box rides along: a point of the result is a point of the
nominal result plus a box point, and the nominal one shifted by the subtrahend is a nominal
point of `P`.

## Inputs
* `P` – H-polytope
* `T` – set of points

## Hypotheses
* `u` – a float bound of `T` along each row
* `hker` – every point of `T` is in the kernel of the equality rows

## Conclusion
* the float certified Minkowski difference is inside the exact one
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.minkDiffOf_inner (P : HPolytope 𝕋 (Vec 𝕋 n)) (T : Set (Vec ℝ n))
    (u : ∀ i, FloatBound 𝕋 T (rowLin P.A i))
    (hker : ∀ i, ∀ y ∈ T, (toRealMat P.Ae *ᵥ y) i = 0) :
    (P.minkDiffOf T u).construct ⊆ minkowskiDiff P.construct T := by -- --- PROOF ---
  intro x hx y hy
  obtain ⟨z, hz, e, he, rfl⟩ := Set.mem_add.mp hx
  obtain ⟨hle, heq⟩ := HPolytope.mem_nominal_iff.mp hz
  refine Set.mem_add.mpr ⟨z + y, HPolytope.mem_nominal_iff.mpr ⟨fun i => ?_, fun i => ?_⟩, e, he,
    add_right_comm _ _ _⟩
  · have h1 : (toRealMat P.A *ᵥ z) i
        ≤ toReal (subDown (P.b i) (u i).val) + |toReal (P.b_error i)| := hle i
    have h2 : (toRealMat P.A *ᵥ y) i ≤ toReal (u i).val := (u i).le y hy
    have h3 := subDown_le_sub (P.b i) (u i).val
    rw [mulVec_add, Pi.add_apply]
    linarith
  · rw [mulVec_add, Pi.add_apply, hker i y hy, add_zero]
    exact heq i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
