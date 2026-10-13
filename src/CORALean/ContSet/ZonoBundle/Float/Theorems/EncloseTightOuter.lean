import CORALean.ContSet.ZonoBundle.Float.Operations.EncloseTight
import CORALean.ContSet.ZonoBundle.Float.Theorems.IntervalAllContains
import CORALean.ContSet.ZonoBundle.Float.Theorems.MtimesOuter
import CORALean.ContSet.ZonoBundle.Float.Theorems.ParallelotopeContains
import CORALean.ContSet.ZonoBundle.Float.Theorems.Convex
import CORALean.ContSet.Interval.Float.Theorems.OrOuter
import CORALean.ContSet.Interval.Float.Theorems.AbsLeMagnitude

/-!
# `ZonoBundle.encloseTight` encloses the convex hull of the two bundles

Each member holds both bundles: a point of either has its image under the member's inverse in
the hull of the two mapped boxes and its coordinates within the hull of the two boxes, which is
what `parallelotope_contains` asks. The result is convex, so it holds the convex hull. Unlike the
exact layer, nothing is assumed of `W` or `U`, and the bundles may be empty.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.encloseTight_outer (zB₁ zB₂ : ZonoBundle (Vec 𝕋 n)) (hk₁ : 0 < zB₁.k)
    (hk₂ : 0 < zB₂.k) (W : Fin r → Mat 𝕋 n n) (U : Mat 𝕋 n n) :
    convexHull ℝ (zB₁.construct ∪ zB₂.construct)
      ⊆ (zB₁.encloseTight zB₂ hk₁ hk₂ W U).construct := by -- --- PROOF ---
  refine convexHull_min ?_ (ZonoBundle.convex_construct _)
  intro x hx
  -- the two facts every member needs, at any candidate inverse `H`
  have hbox : ∀ H : Mat 𝕋 n n, toRealMat H *ᵥ x ∈
      (((zB₁.mtimes H).intervalAll hk₁).or ((zB₂.mtimes H).intervalAll hk₂)).construct := by
    intro H
    refine Interval.or_outer _ _ ?_
    rcases hx with h | h
    · exact Or.inl
        (ZonoBundle.intervalAll_contains (zB₁.mtimes H) hk₁
          (ZonoBundle.mtimes_outer H _ ⟨x, h, rfl⟩))
    · exact Or.inr
        (ZonoBundle.intervalAll_contains (zB₂.mtimes H) hk₂
          (ZonoBundle.mtimes_outer H _ ⟨x, h, rfl⟩))
  have hreach : x ∈ ((zB₁.intervalAll hk₁).or (zB₂.intervalAll hk₂)).construct := by
    refine Interval.or_outer _ _ ?_
    rcases hx with h | h
    · exact Or.inl (ZonoBundle.intervalAll_contains _ hk₁ h)
    · exact Or.inr (ZonoBundle.intervalAll_contains _ hk₂ h)
  have hm : ∀ j, |x j| ≤ toReal (maximumOver
      ((zB₁.intervalAll hk₁).or (zB₂.intervalAll hk₂)).magnitude) := fun j =>
    le_trans (Interval.abs_le_magnitude hreach j) (le_maximumOver _ j)
  -- the transformations' members, then the Stursberg one
  refine Set.mem_iInter.mpr fun i => ?_
  refine Fin.lastCases ?_ (fun i => ?_) i
  · show x ∈ Zonotope.construct (Fin.snoc (α := fun _ => Zonotope (Vec 𝕋 n)) _ _ (Fin.last r))
    rw [Fin.snoc_last]
    exact ZonoBundle.parallelotope_contains _ _ _ _ (hbox _) hm
  · show x ∈ Zonotope.construct (Fin.snoc (α := fun _ => Zonotope (Vec 𝕋 n)) _ _ (Fin.castSucc i))
    rw [Fin.snoc_castSucc]
    exact ZonoBundle.parallelotope_contains _ _ _ _ (hbox _) hm

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
