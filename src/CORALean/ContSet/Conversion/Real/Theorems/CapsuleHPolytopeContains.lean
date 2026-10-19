module

public import CORALean.ContSet.Conversion.Real.Theorems.CapsuleHPolytopeExact

@[expose] public section

/-!
# A capsule lies in its halfspace description

Every branch of CORA's `@capsule/polytope.m`: the branches that return before `'outer'` are
exact (`Capsule.hPolytope_exact`), and `'outer'` bounds each row by the capsule's support value
in that row's direction (`Capsule.supportBound`), which holds for whatever basis the rows come
from.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.hPolytope_contains (C : Capsule n) :
    C.construct ⊆ C.hPolytope.construct := by -- --- PROOF ---
  cases n with
  | zero => exact (C.hPolytope_exact (Or.inl (Nat.zero_le 1))).symm.subset
  | succ m =>
    by_cases hex : m + 1 ≤ 1 ∨ C.r ≤ 0
    · exact (C.hPolytope_exact hex).symm.subset
    -- `'outer'`: each row at the capsule's support value along it
    push Not at hex
    obtain ⟨hm, hr⟩ := hex
    have hstep : C.hPolytope = C.hPolytopeOuter := by
      show (if C.r < 0 then _ else if m = 0 then _ else if C.g = 0 ∧ C.r = 0 then _
        else if C.r = 0 then _ else _ : HPolytope (Vec ℝ (m + 1))) = _
      rw [if_neg (not_lt.mpr hr.le), if_neg (by omega), if_neg (fun h => hr.ne' h.2),
        if_neg hr.ne']
    rw [hstep]
    intro x hx
    exact ⟨fun i => (C.supportBound _).le x hx, fun i => i.elim0⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
