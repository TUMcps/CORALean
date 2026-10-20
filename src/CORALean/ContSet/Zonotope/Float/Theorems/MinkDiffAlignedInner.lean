module

public import CORALean.ContSet.Zonotope.Float.Operations.MinkDiffAligned
public import CORALean.ContSet.Zonotope.Float.Theorems.ContainsZonotopeSound
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter

@[expose] public section

/-!
# The float `minkDiffAligned` is an inner approximation

A returned zonotope `D` passed `containsZonotope` on `D + Z₂` against `Z₁`: the float sum
encloses `D + Z₂` (`plus_outer`), and the check puts that sum inside `Z₁`
(`containsZonotope_sound`). So every point of `D` has all of `Z₂` added into `Z₁`, which is
membership in the Minkowski difference. No alignment is assumed: the check, not [1, Prop. 5],
carries the guarantee, so this is the inner half of `Real.Zonotope.minkDiffAligned_exact` and
no claim that the float result is the whole difference.

## Inputs
* `Z₁` – minuend zonotope
* `Z₂` – subtrahend zonotope
* `ρ` – generator shrink factor
* `H` – candidate right inverse

## Hypotheses
* `hh` – equal generator counts

## Conclusion
* every returned zonotope is inside the Minkowski difference

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.minkDiffAligned_inner {Z₁ Z₂ : Zonotope (Vec 𝕋 n)} {hh : Z₁.h = Z₂.h} {ρ : 𝕋}
    {H : Mat 𝕋 Z₁.h n} : -- --- CONCL ---
    ∀ D ∈ Z₁.minkDiffAligned Z₂ hh ρ H,
      D.construct ⊆ minkowskiDiff Z₁.construct Z₂.construct := by -- --- PROOF ---
  intro D (h : Z₁.minkDiffAligned Z₂ hh ρ H = some D)
  unfold Zonotope.minkDiffAligned at h
  dsimp only at h
  split_ifs at h with hc
  cases h
  intro x hx y hy
  exact Zonotope.containsZonotope_sound hc
    (Zonotope.plus_outer _ _ (Set.add_mem_add hx hy))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
