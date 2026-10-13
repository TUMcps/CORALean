module

public import CORALean.ContDynamics.NonlinearSysDT.Definitions.ConsistentSet

@[expose] public section

/-!
# The consistent set lies in the intersection of the component sets

[1, Sec. 5]: "`X_{y_k} ⊆ ⋂ᵢ X_{y_k}(i)`", which is "clear": a noise `v` with `y = g(x, v)` gives
`y_i = g_i(x, v)` for every component `i` at once. The intersection of the component sets is what
the strips of [1, Property 1] bound, one per output.

## References

* [1] T. Alamo, J. M. Bravo and E. F. Camacho. "Guaranteed state estimation by zonotopes".
      Automatica, 41(6):1035-1043, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearSysDT.consistentSet_subset_iInter {n nv p : ℕ}
    (g : Vec ℝ n → Vec ℝ nv → Vec ℝ p) (V : Set (Vec ℝ nv)) (y : Vec ℝ p) :
    NonlinearSysDT.consistentSet g V y ⊆ ⋂ i, NonlinearSysDT.consistentSetComp g V y i := by
  rintro x ⟨v, hv, hy⟩
  -- the same noise works for every component
  exact Set.mem_iInter.mpr fun i => ⟨v, hv, by rw [hy]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
