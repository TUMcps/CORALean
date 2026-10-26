module

public import CORALean.ContSet.Ellipsoid.Float.Operations.AndPoint
public import CORALean.ContSet.Ellipsoid.Float.Theorems.ContainsPointSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.ExcludesPointSound
public import CORALean.ContSet.Ellipsoid.Float.Operations.OfPoint
public import CORALean.ContSet.Ellipsoid.Real.Theorems.OfPointMemIff
public import CORALean.ContSet.Interval.Float.Theorems.OriginExact
public import CORALean.ContSet.Ellipsoid.Real.Theorems.OfShapeEq
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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
open Pointwise

/-- `Ellipsoid.ofPoint` is exactly the point. -/
private theorem Ellipsoid.aux_ofPoint_exact (p : Vec 𝕋 n) : -- --- CONCL ---
    (Ellipsoid.ofPoint p).construct = {toRealVec p} := by -- --- PROOF ---
  have hQ : toRealMat (fun _ _ : Fin n => (zero : 𝕋)) = 0 :=
    funext fun _ => funext fun _ => toReal_zero
  have h : (InflatedContSet.nominal (Ellipsoid.ofPoint p)).ellipsoid
      = Real.Ellipsoid.ofPoint (toRealVec p) := by
    show Real.Ellipsoid.ofShape (toRealMat (fun _ _ : Fin n => (zero : 𝕋))) (toRealVec p) = _
    rw [hQ, Real.Ellipsoid.ofShape_eq .zero]
    rfl
  have hN : InflatedContSet.nominalSet (Ellipsoid.ofPoint p) = {toRealVec p} := by
    show (InflatedContSet.nominal (Ellipsoid.ofPoint p)).ellipsoid.construct = _
    rw [h]
    exact Set.ext fun x =>
      (Real.Ellipsoid.mem_ofPoint_iff (toRealVec p) x).trans Set.mem_singleton_iff.symm
  have hE : (Ellipsoid.ofPoint p).I_error.construct = {0} := Interval.origin_exact n
  show InflatedContSet.nominalSet (Ellipsoid.ofPoint p) + (Ellipsoid.ofPoint p).I_error.construct =
      _
  rw [hN, hE, Set.singleton_add_singleton, add_zero]

end


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.andPoint_outer (E : Ellipsoid 𝕋 n) (p w : Vec 𝕋 n)
    (a : Vec 𝕋 n) (s : 𝕋) : -- --- CONCL ---
    E.construct ∩ {toRealVec p} ⊆ ContSet.construct (E.andPoint p w a s) := by -- --- PROOF ---
  -- the point ellipsoid holds every point of `E ∩ {p}`
  have hpt : E.construct ∩ {toRealVec p}
      ⊆ ContSet.construct (OptEmpty.of (Ellipsoid.ofPoint p) : OptEmpty (Ellipsoid 𝕋 n)) := by
    rw [OptEmpty.construct_of]
    change _ ⊆ (Ellipsoid.ofPoint p).construct
    rw [Ellipsoid.aux_ofPoint_exact]
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
