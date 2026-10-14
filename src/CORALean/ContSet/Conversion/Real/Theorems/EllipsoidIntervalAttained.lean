module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.SupportBoundAttained
public import CORALean.ContSet.Interval.Real.Operations.OfBounds
public import CORALean.ContSet.Interval.Real.Operations.SubsetOfBounds
public import CORALean.ContSet.Conversion.Real.Operations.Ellipsoid_to_Interval

@[expose] public section

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

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Each upper face is touched, so no smaller box encloses the ellipsoid. The
lower faces are the same statement against `-eⱼ`. -/
theorem Ellipsoid.interval_attained (E : Ellipsoid n) (j : Fin n) :
    ∃ x ∈ E.construct, x j = E.interval.sup j := by
  obtain ⟨x, hx, hcx⟩ := E.supportBound_attained (LinearMap.proj j)
  exact ⟨x, hx, hcx⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
