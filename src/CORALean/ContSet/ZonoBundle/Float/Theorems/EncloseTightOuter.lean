module

public import CORALean.ContSet.ZonoBundle.Float.Theorems.ConstructEqIInter
public import CORALean.ContSet.ZonoBundle.Float.Operations.EncloseTight
public import CORALean.ContSet.ZonoBundle.Float.Theorems.IntervalAllContains
public import CORALean.ContSet.ZonoBundle.Float.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter
public import CORALean.ContSet.SetIntersection.Theorems.MemberwiseOuter
public import CORALean.ContSet.ZonoBundle.Float.Theorems.ParallelotopeContains
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContSet.SetIntersection.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.OrOuter
public import CORALean.ContSet.Interval.Float.Theorems.AbsLeMagnitude

@[expose] public section

/-!
# `ZonoBundle.encloseTight` encloses the convex hull of the two bundles

Each member holds both bundles: a point of either has its image under the member's inverse in
the hull of the two mapped boxes and its coordinates within the hull of the two boxes, which is
what `parallelotope_contains` asks. The result is convex, so it holds the convex hull. Unlike the
exact layer, nothing is assumed of `W` or `U`, and the bundles may be empty.

## Inputs
* `zB₁` – first bundle
* `zB₂` – second bundle
* `W` – transformation matrices
* `U` – extra transformation matrix

## Hypotheses
* `hk₁` – first bundle has a member
* `hk₂` – second bundle has a member

## Conclusion
* the convex hull of the union is contained in the result
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.encloseTight_outer (zB₁ zB₂ : ZonoBundle (Vec 𝕋 n)) (hk₁ : 0 < zB₁.k)
    (hk₂ : 0 < zB₂.k) (W : Fin r → Mat 𝕋 n n) (U : Mat 𝕋 n n) :
    convexHull ℝ (zB₁.construct ∪ zB₂.construct)
      ⊆ (zB₁.encloseTight zB₂ hk₁ hk₂ W U).construct := by -- --- PROOF ---
  -- the bundle is convex, so the hull of the union is inside once the union is
  refine convexHull_min ?_ (SetIntersection.convex_construct _)
  intro x hx
  -- the two facts every member needs, at any candidate inverse `H`
  have hbox : ∀ H : Mat 𝕋 n n, toRealMat H *ᵥ x ∈
      (((zB₁.mtimes H).intervalAll hk₁).or ((zB₂.mtimes H).intervalAll hk₂)).construct := by
    intro H
    refine Interval.or_outer _ _ ?_
    -- `H x` lies in the mapped bundle of whichever operand holds `x`, so in its box
    rcases hx with h | h
    · exact Or.inl
        (ZonoBundle.intervalAll_contains (zB₁.mtimes H) hk₁
          (SetIntersection.memberwise_outer (Set.image (toRealMat H *ᵥ ·)) Set.monotone_image
            (fun i => ⟨i, Zonotope.mtimes_outer H (zB₁.Z i)⟩) ⟨x, h, rfl⟩))
    · exact Or.inr
        (ZonoBundle.intervalAll_contains (zB₂.mtimes H) hk₂
          (SetIntersection.memberwise_outer (Set.image (toRealMat H *ᵥ ·)) Set.monotone_image
            (fun i => ⟨i, Zonotope.mtimes_outer H (zB₂.Z i)⟩) ⟨x, h, rfl⟩))
  have hreach : x ∈ ((zB₁.intervalAll hk₁).or (zB₂.intervalAll hk₂)).construct := by
    refine Interval.or_outer _ _ ?_
    rcases hx with h | h
    · exact Or.inl (ZonoBundle.intervalAll_contains _ hk₁ h)
    · exact Or.inr (ZonoBundle.intervalAll_contains _ hk₂ h)
  have hm : ∀ j, |x j| ≤ toReal (maximumOver
      ((zB₁.intervalAll hk₁).or (zB₂.intervalAll hk₂)).magnitude) := fun j =>
    le_trans (Interval.abs_le_magnitude hreach j) (le_maximumOver _ j)
  -- the transformations' members, then the Stursberg one
  rw [ZonoBundle.construct_eq_iInter]
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
