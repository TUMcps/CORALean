module

public import CORALean.Specification.OnlineAnalyzerNode.Operations.SetPropagated

@[expose] public section

/-!
# When `setPropagated` throws

`setPropagated(obj,parent,int)` throws exactly when the parent is no parent, or the new interval
is smaller than the old one: the old one contains it and they are not equal.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {A : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineAnalyzerNode.setPropagated_eq_none_iff (eps : ℝ) (n : OnlineAnalyzerNode A)
    (parent : ℕ) (int : STLInterval) : -- --- CONCL ---
    n.setPropagated eps parent int = none ↔ (n.prop[n.parents.idxOf parent]? = none ∨
      ∃ old, n.prop[n.parents.idxOf parent]? = some old ∧
        (¬ STLInterval.isequal eps old int ∧
          STLInterval.contains_ eps old int)) := by -- --- PROOF ---
  unfold OnlineAnalyzerNode.setPropagated
  dsimp only
  rcases h : n.prop[n.parents.idxOf parent]? with _ | old
  · simp
  · by_cases hb : ¬ STLInterval.isequal eps old int ∧ STLInterval.contains_ eps old int
    · simp [hb]
    · simp only [hb, if_false]
      split_ifs <;> simp [hb]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
