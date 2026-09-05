import CORALean.ContSet.Ellipsoid.Real.Theorems.SupportBoundAttained
import CORALean.ContSet.Interval.Real.Operations.OfBounds
import CORALean.ContSet.Interval.Real.Operations.SubsetOfBounds

/-!
# An ellipsoid as a box

CORA's `interval(ellipsoid)`, and the conversion the support function was
written for: `Interval.ofBounds` wants `2n` certificates, an ellipsoid produces
each of them in closed form, and the enclosure proof is `subset_ofBounds` and
nothing else. No linear program, unlike a halfspace description, and no
directions for the caller to choose, unlike everything that goes out through
`ofBounds` the other way.

The box is *tight*, not merely sound: the support value is attained, so every
one of its `2n` faces touches the ellipsoid. `interval_attained` says so, and it
is the one place the difference between `SupportBound` and the support function
itself is visible.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

noncomputable def Ellipsoid.interval (E : Ellipsoid n) : Interval (Vec ℝ n) :=
  Interval.ofBounds (fun j => E.supportBound (LinearMap.proj j))
    (fun j => E.supportBound (-LinearMap.proj j))

theorem Ellipsoid.interval_outer (E : Ellipsoid n) : E.construct ⊆ E.interval.construct :=
  Interval.subset_ofBounds _ _

/-- Each upper face is touched, so no smaller box encloses the ellipsoid. The
lower faces are the same statement against `-eⱼ`. -/
theorem Ellipsoid.interval_attained (E : Ellipsoid n) (j : Fin n) :
    ∃ x ∈ E.construct, x j = E.interval.sup j := by
  obtain ⟨x, hx, hcx⟩ := E.supportBound_attained (LinearMap.proj j)
  exact ⟨x, hx, hcx⟩

end CORALean.Real
