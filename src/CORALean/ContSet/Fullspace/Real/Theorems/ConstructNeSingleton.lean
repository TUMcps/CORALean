import CORALean.ContSet.Fullspace.Real.Fullspace

/-!
# The full space is not a point

`representsa_(fs,'point')` and `'origin'` are `false` for `fullspace`, at positive
dimension (`R^0` is a point, and CORA's `representsa_emptyObject` answers before this).
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Fullspace.construct_ne_singleton (hn : 0 < n) (F : Fullspace n) (v : Vec ℝ n) :
    F.construct ≠ {v} := by -- --- PROOF ---
  intro h
  have h1 : (v + Pi.single ⟨0, hn⟩ 1 : Vec ℝ n) ∈ F.construct := Set.mem_univ _
  rw [h] at h1
  have h2 := congrFun (Set.mem_singleton_iff.mp h1) ⟨0, hn⟩
  simp at h2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
