import CORALean.ContSet.HPolytope.Real.Operations.IntervalOf
import CORALean.ContSet.VPolytope.Real.Theorems.OfIntervalOuter
import CORALean.ContSet.HPolytope.Real.Theorems.CertifiedOuter

/-!
# Halfspaces to vertices

The expensive direction, and the one no cheap certificate exists for: to say
that a halfspace description sits inside a given hull, one would have to know
that hull's facets, which is the conversion again.

So it goes through a box — `2n` linear programs, then `2ⁿ` corners. Sound,
never tight unless the polytope was a box, and exponential in the dimension
either way, which vertex enumeration also is.

The rows themselves are never enumerated. That is the part left out, and it is
an algorithm with its own correctness proof rather than a definition; a caller
who has one can hand its vertices to `VPolytope` directly and prove the
enclosure with `subset_toH` in the other direction.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ} {P : HPolytope (Vec ℝ n)}

noncomputable def HPolytope.toV (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) : VPolytope (Vec ℝ n) :=
  VPolytope.ofInterval (HPolytope.intervalOf up lo)

theorem HPolytope.subset_toV (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) :
    P.construct ⊆ (HPolytope.toV up lo).construct :=
  subset_trans (HPolytope.intervalOf_outer up lo) (VPolytope.subset_ofInterval _)

end CORALean.Real
