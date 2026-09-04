import CORALean.ContSet.Ellipsoid.Real.Theorems.SupportBoundAttained

/-!
# The support bound is the maximum, not merely an upper bound

`SupportBound` carries only an inequality; together with a point attaining it
that inequality becomes a maximum. This is the form a conversion reads, since it
is what says an interval hull taken off these bounds touches the ellipsoid.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

-- attained, so the bound is the maximum rather than merely an upper bound
theorem Ellipsoid.isGreatest_support (E : Ellipsoid n) (c : Vec ℝ n →ₗ[ℝ] ℝ) :
    IsGreatest (c '' E.construct) (E.supportBound c).val := by
  obtain ⟨x, hx, hcx⟩ := E.supportBound_attained c
  refine ⟨⟨x, hx, hcx⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact (E.supportBound c).le y hy

end CORALean.Real
