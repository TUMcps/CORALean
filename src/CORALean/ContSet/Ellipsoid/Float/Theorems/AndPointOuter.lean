module

public import CORALean.ContSet.Ellipsoid.Float.Operations.AndPoint
public import CORALean.ContSet.Ellipsoid.Float.Theorems.ContainsPointSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.ExcludesPointSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.OfPointExact
public import CORALean.ContSet.OptEmpty.Theorems.Basic

@[expose] public section

/-!
# `and_` of a float ellipsoid and a point encloses the intersection

Outer: `E ∩ {p}` lies in what `Ellipsoid.andPoint` denotes, at every certificate. The point
branches denote `{p}`, which holds `E ∩ {p}`; the empty branch is taken only when `excludesPoint`
has proved `p ∉ E`, so `E ∩ {p}` is empty there. Exact on the two certified branches, as over ℝ
(`Real.Ellipsoid.andPoint_exact`): a certified `p ∈ E` makes `{p} = E ∩ {p}`; only the undecided
branch may return the point for an `E` that misses it.

## Inputs
* `E` – ellipsoid
* `p` – point
* `w` – solve of `Q w = p - q`
* `a` – separating direction
* `s` – length bounding `√(aᵀ Q a)`

## Hypotheses
* none

## Conclusion
* the intersection of `E` with the point lies in the result
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.andPoint_outer (E : Ellipsoid 𝕋 n) (p w : Vec 𝕋 n)
    (a : Vec 𝕋 n) (s : 𝕋) : -- --- CONCL ---
    E.construct ∩ {toRealVec p} ⊆ ContSet.construct (E.andPoint p w a s) := by -- --- PROOF ---
  -- the point ellipsoid holds every point of `E ∩ {p}`
  have hpt : E.construct ∩ {toRealVec p}
      ⊆ ContSet.construct (OptEmpty.of (Ellipsoid.ofPoint p) : OptEmpty (Ellipsoid 𝕋 n)) := by
    rw [OptEmpty.construct_of]
    change _ ⊆ (Ellipsoid.ofPoint p).construct
    rw [Ellipsoid.ofPoint_exact]
    exact Set.inter_subset_right
  unfold Ellipsoid.andPoint
  split_ifs with h₁ h₂
  · exact hpt
  · -- certified outside: the intersection is empty
    rintro x ⟨hx, rfl⟩
    exact absurd hx (Ellipsoid.excludesPoint_sound h₂)
  · exact hpt

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
