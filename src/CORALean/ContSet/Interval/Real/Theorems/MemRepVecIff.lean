module

public import CORALean.ContSet.Interval.Real.Operations.Basic

@[expose] public section

/-!
# A point of a repeated box

A point lies in `I.repVec a` iff each of its `a` blocks lies in `I`, block `j` being the entries
`finProdFinEquiv (j, k)`, as `repVec` lays the copies out.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point of the repeated box is one whose every block lies in the box. -/
theorem Interval.mem_repVec_iff (a : ℕ) (I : Interval (Vec ℝ n)) (x : Vec ℝ (a * n)) :
    x ∈ (I.repVec a).construct
      ↔ ∀ j, (fun k => x (finProdFinEquiv (j, k))) ∈ I.construct := by -- --- PROOF ---
  constructor
  · intro hx j k
    have h : I.inf (finProdFinEquiv.symm (finProdFinEquiv (j, k))).2 ≤ x (finProdFinEquiv (j, k))
        ∧ x (finProdFinEquiv (j, k)) ≤ I.sup (finProdFinEquiv.symm (finProdFinEquiv (j, k))).2 :=
      hx _
    rw [Equiv.symm_apply_apply] at h
    exact h
  · intro hx i
    obtain ⟨⟨j, k⟩, rfl⟩ := finProdFinEquiv.surjective i
    show I.inf (finProdFinEquiv.symm (finProdFinEquiv (j, k))).2 ≤ x (finProdFinEquiv (j, k))
      ∧ x (finProdFinEquiv (j, k)) ≤ I.sup (finProdFinEquiv.symm (finProdFinEquiv (j, k))).2
    rw [Equiv.symm_apply_apply]
    exact hx j k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
