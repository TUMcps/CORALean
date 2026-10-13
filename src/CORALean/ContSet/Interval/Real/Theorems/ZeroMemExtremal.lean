module

public import CORALean.ContSet.Interval.Real.Theorems.ExtremalLoIsLeast
public import CORALean.ContSet.Interval.Real.Theorems.ExtremalHiIsGreatest

@[expose] public section

/-!
# A solution passes the extremal test

[1, Sec. 3 (necessary condition)]: with `g̲(x) ≤ f(x, y) ≤ g̅(x)` for all `y ∈ [Y]`, the test
`0 ∈ [g̲(x), g̅(x)]` is a necessary condition for `x` to satisfy `f(x, y) = 0`. Stated for the
extremal functions of `Interval.extremalLo`/`extremalHi`: if some coefficient vector of `C`
makes `Σᵢ cᵢ hᵢ(x)` vanish, as `cᵢ = fᵢ(y)` does at a solution, then `g̲(x) ≤ 0 ≤ g̅(x)`.

## References

* [1] G. Trombettoni, Y. Papegay, G. Chabert and O. Pourtallier. "A Box-Consistency Contractor
      Based on Extremal Functions". In Proc. of the 16th International Conference on Principles
      and Practice of Constraint Programming (CP 2010), LNCS 6308, pp. 491-498, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.zero_mem_extremal {C : Interval (Vec ℝ m)} {h : Vec ℝ m} {c : Vec ℝ m}
    (hc : c ∈ C.construct) (h0 : ∑ i, c i * h i = 0) :
    C.extremalLo h ≤ 0 ∧ 0 ≤ C.extremalHi h := by
  -- `C` holds `c`, so it is nonempty, and the two extremal values bracket `Σᵢ cᵢ hᵢ = 0`
  have hC : C.IsNonempty := fun i => le_trans (hc i).1 (hc i).2
  exact ⟨h0 ▸ (C.extremalLo_isLeast hC h).2 ⟨c, hc, rfl⟩,
    h0 ▸ (C.extremalHi_isGreatest hC h).2 ⟨c, hc, rfl⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
