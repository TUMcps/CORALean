import CORALean.ContSet.HPolytope.Real.Operations.BasicPoint
import CORALean.ContSet.HPolytope.Real.Theorems.ExtremePoints
import CORALean.ContSet.Conversion.Real.HPolytope_to_Interval
import CORALean.ContSet.Conversion.Real.Interval_to_VPolytope
import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
import CORALean.ContSet.VPolytope.Real.Theorems.IsBounded

/-!
# Halfspaces to vertices

Two routes, and they trade opposite exponentials.

`vPolytope` is the real conversion and is **exact**. A bounded polytope is the
closure of the hull of its extreme points, and at an extreme point no direction
is free, so the rows tight there admit exactly one solution — which means every
extreme point is named by its own tight set. Enumerating the subsets of rows
therefore reaches all of them. Costs `2^m`, and needs the polytope nonempty, for
the same reason CORA needs a feasible point: a subset of rows that names nothing
usable has to fall back on something inside.

`vPolytopeBox` goes through a box instead — `2n` linear programs, then `2ⁿ`
corners. Never tight unless the polytope was a box, but polynomial in the number
of rows, which is the case that matters when a step has accumulated many.

Neither enumerates facets: nothing here identifies *which* subsets give
vertices, which is a question of cost the enclosure does not depend on.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open scoped Classical

variable {n : ℕ} {P : HPolytope (Vec ℝ n)}

/-- Bounded because something bounded contains it, which is what an enclosure
already computed says. -/
theorem HPolytope.isCompact_of_subset {W : VPolytope (Vec ℝ n)} (h : P.construct ⊆ W.construct) :
    IsCompact P.construct :=
  Metric.isCompact_of_isClosed_isBounded P.isClosed_construct (W.isBounded_construct.subset h)

/-- The soundness half of vertex enumeration: a list holding every point the
rows pin down encloses the polytope. An implementation must then show it found
those points, never that its search was exhaustive in any other sense. -/
theorem HPolytope.subset_of_pinned (hc : IsCompact P.construct) (W : VPolytope (Vec ℝ n))
    (hW : ∀ x ∈ P.construct,
        (∀ d : Vec ℝ n, (∀ i, P.A i x = P.b i → P.A i d = 0) → (∀ i, P.Ae i d = 0) → d = 0) →
        x ∈ Set.range W.V) :
    P.construct ⊆ W.construct := by
  have hext : P.construct.extremePoints ℝ ⊆ Set.range W.V := fun x hx =>
    hW x hx.1 fun _ h₁ h₂ => P.eq_zero_of_extremePoint hx h₁ h₂
  have hclosed : IsClosed (convexHull ℝ (Set.range W.V)) :=
    (Set.Finite.isCompact_convexHull ℝ (Set.finite_range W.V)).isClosed
  calc P.construct = closure (convexHull ℝ (P.construct.extremePoints ℝ)) :=
        (closure_convexHull_extremePoints hc P.convex_construct).symm
    _ ⊆ closure (convexHull ℝ (Set.range W.V)) := closure_mono (convexHull_mono hext)
    _ = convexHull ℝ (Set.range W.V) := hclosed.closure_eq
    _ = W.construct := W.construct_eq_convexHull.symm

/-- One candidate per subset of the inequality rows, kept when feasible and
replaced by a point of the polytope when not — so every vertex listed is a point
of the polytope, which is what makes the conversion exact. -/
noncomputable def HPolytope.vPolytope (P : HPolytope (Vec ℝ n)) (hne : P.construct.Nonempty) :
    VPolytope (Vec ℝ n) where
  k := 2 ^ P.m
  V := fun l =>
    if P.basicPoint (signEquiv P.m l) ∈ P.construct then P.basicPoint (signEquiv P.m l)
    else hne.choose

theorem HPolytope.vPolytope_subset (P : HPolytope (Vec ℝ n)) (hne : P.construct.Nonempty) :
    (P.vPolytope hne).construct ⊆ P.construct := by
  rw [VPolytope.construct_eq_convexHull]
  refine convexHull_min ?_ P.convex_construct
  rintro _ ⟨l, rfl⟩
  show (if P.basicPoint (signEquiv P.m l) ∈ P.construct then P.basicPoint (signEquiv P.m l)
    else hne.choose) ∈ P.construct
  split
  · assumption
  · exact hne.choose_spec

-- the other way: `subset_of_pinned` asks only that every extreme point be listed
theorem HPolytope.subset_vPolytope (P : HPolytope (Vec ℝ n)) (hc : IsCompact P.construct)
    (hne : P.construct.Nonempty) : P.construct ⊆ (P.vPolytope hne).construct := by
  refine HPolytope.subset_of_pinned hc _ fun x hx hpin => ?_
  refine ⟨(signEquiv P.m).symm (P.tightAt x), ?_⟩
  show (if P.basicPoint (signEquiv P.m ((signEquiv P.m).symm (P.tightAt x))) ∈ P.construct then
      P.basicPoint (signEquiv P.m ((signEquiv P.m).symm (P.tightAt x))) else hne.choose) = x
  rw [Equiv.apply_symm_apply, P.basicPoint_tightAt hx hpin, if_pos hx]

theorem HPolytope.vPolytope_exact (P : HPolytope (Vec ℝ n)) (hc : IsCompact P.construct)
    (hne : P.construct.Nonempty) : (P.vPolytope hne).construct = P.construct :=
  Set.Subset.antisymm (P.vPolytope_subset hne) (P.subset_vPolytope hc hne)

/-- The cheap route: a box from `2n` certificates, then its corners. -/
noncomputable def HPolytope.vPolytopeBox
    (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) : VPolytope (Vec ℝ n) :=
  Interval.vPolytope (HPolytope.interval up lo)

theorem HPolytope.subset_vPolytopeBox
    (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) :
    P.construct ⊆ (HPolytope.vPolytopeBox up lo).construct :=
  subset_trans (HPolytope.interval_outer up lo) (Interval.subset_vPolytope _)

end CORALean.Real
