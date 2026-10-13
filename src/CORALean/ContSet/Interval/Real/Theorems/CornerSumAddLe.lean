import CORALean.ContSet.Conversion.Real.Interval_to_VPolytope
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Raising a label raises the vertex sum

On the box `[0, b₁] × … × [0, bₙ]`, `b ≥ 0`, a vertex `w` raising every coordinate `l` raises and
one more, `m`, has `Σᵢ wᵢ ≥ Σᵢ lᵢ + bₘ`: the step behind [1, Lemma 6.1], where every vertex of an
s-face but the lowest raises a coordinate `k > j` and so passes `α < b_{j+1} + Σ_{i≤j} vᵢ`.

## References

* [1] C. Lara, J. J. Flores and F. Calderon. "On the Hyperbox – Hyperplane Intersection
      Problem". INFOCOMP Journal of Computer Science, 8(4):21-27, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.corner_sum_add_le {b : Vec ℝ n} (hb0 : ∀ i, 0 ≤ b i) {l w : Fin n → Bool}
    {m : Fin n} (hlw : ∀ i, l i = true → w i = true) (hlm : l m = false) (hwm : w m = true) :
    ∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner l i + b m ≤
      ∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner w i := by -- --- PROOF ---
  have hsum : ∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner l i + b m =
      ∑ i, ((⟨0, b⟩ : Interval (Vec ℝ n)).corner l i + if i = m then b m else 0) := by
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq']; simp
  rw [hsum]
  -- coordinatewise: at `m` both are `bₘ`, elsewhere a raised label of `l` is one of `w`
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Interval.corner]
  by_cases him : i = m
  · subst him; simp [hlm, hwm]
  · cases hli : l i
    · cases hwi : w i <;> simp [him, hb0 i]
    · simp [him, hlw i hli]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
