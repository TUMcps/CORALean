module

public import CORALean.ContSet.LevelSet.Real.Definitions.RangeBound

@[expose] public section

/-!
# A set whose range bound is positive in one constraint has left the invariant

[1, Sec. 4.1]: with `[lᵢ, uᵢ] = bound(s₍ᵢ₎, R(t_k))` for the invariant `S = {x | s(x) ≤ 0_w}`,
"the reachable set is located outside the invariant set if `∀ i : lᵢ > 0`". One positive
`lᵢ` already suffices, and that is what is proved. [1]'s `∀ i` implies it once `w ≥ 1`; at
`w = 0` the invariant is the whole space and the printed test passes vacuously, so [1]'s
reading needs at least one constraint.

## Inputs
* `s` – invariant functions
* `R` – set
* `l` – lower bounds
* `u` – upper bounds
* `i` – row index

## Hypotheses
* `hb` – `[l, u]` bounds each row on `R`
* `hl` – `0 < l i`

## Conclusion
* `R` misses the invariant

## References

* [1] N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear
      Guard Sets". In Proc. of the 23rd ACM International Conference on Hybrid Systems:
      Computation and Control (HSCC), 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n w : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem inter_invariant_eq_empty_of_rangeBound (s : Vec ℝ n → Vec ℝ w) (R : Set (Vec ℝ n))
    (l u : Vec ℝ w) (hb : ∀ i, IsRangeBound (fun x => s x i) R (l i) (u i)) (i : Fin w)
    (hl : 0 < l i) : R ∩ {x | ∀ j, s x j ≤ 0} = ∅ := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hx hS
  exact absurd (lt_of_lt_of_le hl (hb i x hx).1) (not_lt.mpr (hS i))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
