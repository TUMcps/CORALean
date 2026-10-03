import CORALean.ContSet.Capsule.Real.Operations.Isequal

/-!
# Equal fields denote equal sets

Sound, not exact: two capsules with `r < 0` are both `∅` whatever their other fields, so the
converse fails. CORA's own emptiness test (`representsa_(C,'emptySet')`) does not see `r < 0`
either, and answers by the fields.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Capsules with equal fields denote the same set. -/
theorem Capsule.isequal_construct {C S : Capsule n} (h : C.isequal S) :
    C.construct = S.construct := by
  obtain ⟨hc, hg, hr⟩ := h
  cases C
  cases S
  simp_all

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
