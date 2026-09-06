import CORALean.Specification.Specification
import CORALean.Global.LinProg.LinProg

/-!
# A direction certifies that an unsafe set is avoided

Checking `Disjoint O U` by inspecting the two sets is a feasibility problem;
producing one direction along which they do not overlap turns it into two bounds
that `Global.LinProg` already knows how to obtain and to compose. The bound on
`U` runs against `-c`, a linear program bounding only from above, exactly as
`Interval.ofBounds` takes its lower bounds.

The certificate is one-sided by nature: a separating direction proves
disjointness, and failing to find one proves nothing, the sets possibly being
disjoint without a hyperplane between them when neither is convex.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type} [AddCommGroup α] [Module ℝ α] {O U : Set α} {c : α →ₗ[ℝ] ℝ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `O` does not reach as far along `c` as `U` has to come back, so no point is
in both. -/
theorem aux_disjoint_of_separating (u : SupportBound O c) (v : SupportBound U (-c))
    (h : u.val + v.val < 0) : Disjoint O U := by -- --- PROOF ---
  rw [Set.disjoint_left]
  intro x hO hU
  have h₁ : c x ≤ u.val := u.le x hO
  have h₂ := v.le x hU
  rw [LinearMap.neg_apply] at h₂
  linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem Specification.holds_unsafeSet_of_separating (u : SupportBound O c)
    (v : SupportBound U (-c)) (h : u.val + v.val < 0) :
    (Specification.unsafeSet U).Holds O :=
  aux_disjoint_of_separating u v h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
