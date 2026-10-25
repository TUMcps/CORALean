module

public import CORALean.ContSet.LevelSet.Real.Definitions.RangeBound

@[expose] public section

/-!
# A set whose range bound excludes zero misses the guard

[1, Sec. 4.1]: with `[l, u] = bound(g, R(τ_j))` for the guard `G = {x | g(x) = 0}`, the set
"potentially intersects the guard set if `l ≤ 0 ∧ u ≥ 0`" — read as the test it is used for:
if that fails, `R(τ_j) ∩ G = ∅`. Nothing about `g` is needed.

## Inputs
* `g` – guard function
* `R` – set
* `l` – lower bound
* `u` – upper bound

## Hypotheses
* `hb` – `[l, u]` bounds `g` on `R`
* `h` – `0` is outside `[l, u]`

## Conclusion
* `R` misses the guard `g = 0`

## References

* [1] N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear Guard
      Sets". Proceedings of the 23rd International Conference on Hybrid Systems: Computation and
      Control, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem inter_guard_eq_empty_of_rangeBound (g : Vec ℝ n → ℝ) (R : Set (Vec ℝ n)) (l u : ℝ)
    (hb : IsRangeBound g R l u) (h : ¬(l ≤ 0 ∧ 0 ≤ u)) : -- --- CONCL ---
    R ∩ {x | g x = 0} = ∅ := by -- --- PROOF ---
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hx hg
  have := hb x hx
  rw [hg] at this
  exact h this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
