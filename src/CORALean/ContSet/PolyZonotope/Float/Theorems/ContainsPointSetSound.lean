import CORALean.ContSet.PolyZonotope.Float.Operations.ContainsPointSet
import CORALean.ContSet.PolyZonotope.Float.Theorems.SplitGenCover
import CORALean.ContSet.PolyZonotope.Float.Theorems.ZonotopeCoraContains
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceGirardOuter
import CORALean.ContSet.HPolytope.Float.Theorems.ExcludesPointSound

/-!
# `containsPointSet` never rejects a point set the polynomial zonotope contains

As over ℝ: every point is in some piece (`splitGen_cover`), whose zonotope
(`zonotopeCora_contains`), reduced (`reduceGirard_outer`), lies in its polytope
(`hPolytope_contains`), which therefore cannot certify the point outside
(`excludesPoint_sound`). Contrapositively, `false` proves that some point is outside the set.
The converse fails and is not claimed: `true` says only that no enclosure excludes any point.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Every point of the set is in some piece after any number of rounds. -/
theorem PolyZonotope.aux_splitMany_cover (pZ : PolyZonotope (Vec 𝕋 n)) (k : ℕ) :
    ∀ x ∈ pZ.construct, ∃ q ∈ pZ.splitMany k, x ∈ q.construct := by -- --- PROOF ---
  induction k with
  | zero => exact fun x hx => ⟨pZ, List.mem_singleton_self _, hx⟩
  | succ k ih =>
    intro x hx
    obtain ⟨q, hq, hxq⟩ := ih x hx
    rcases PolyZonotope.splitGen_cover q hxq with h | h
    · exact ⟨q.splitGen.1, List.mem_flatMap.mpr ⟨q, hq, by simp⟩, h⟩
    · exact ⟨q.splitGen.2, List.mem_flatMap.mpr ⟨q, hq, by simp⟩, h⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.containsPointSet_sound (pZ : PolyZonotope (Vec 𝕋 n)) {N : ℕ}
    (points : Fin N → Vec 𝕋 n) (splits order : ℕ) (dirs : Zonotope (Vec 𝕋 n) → Σ m, Mat 𝕋 m n)
    (h : ∀ i, toRealVec (points i) ∈ pZ.construct) :
    pZ.containsPointSet points splits order dirs = true := by -- --- PROOF ---
  unfold PolyZonotope.containsPointSet
  refine List.all_eq_true.mpr fun i _ => List.any_eq_true.mpr ?_
  -- the point is in some piece, whose reduced zonotope's polytope contains it
  obtain ⟨q, hq, hxq⟩ := PolyZonotope.aux_splitMany_cover pZ splits _ (h i)
  refine ⟨_, List.mem_append_left _ (List.mem_map.mpr ⟨q, hq, rfl⟩), ?_⟩
  have hP := Zonotope.hPolytope_contains (q.zonotopeCora.reduceGirard order)
    (dirs (q.zonotopeCora.reduceGirard order)).2
    (Zonotope.reduceGirard_outer _ order (PolyZonotope.zonotopeCora_contains q hxq))
  cases hex : HPolytope.excludesPoint _ (points i) with
  | false => rfl
  | true => exact absurd hP (HPolytope.excludesPoint_sound _ _ hex)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
