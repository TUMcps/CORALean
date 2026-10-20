module

public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-!
# Raising one label adds its bound

On the box `[0, b₁] × … × [0, bₙ]`, raising coordinate `m` of a vertex at `0` there adds `bₘ` to
its sum: the vertex `(…, b_{k+1}, …)` that line 6 of [1, Alg. 2] rejects is `w` with one more
coordinate raised, `Σᵢ wᵢ + b_{k+1} > α` — the right half of [1, Lemma 6.1]'s condition.

## Inputs
* `b` – upper bound vector
* `l` – corner labels
* `m` – raised coordinate

## Hypotheses
* `hlm` – `l` is unset at `m`

## Conclusion
* raising the label adds the bound to the corner sum

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

theorem Interval.corner_sum_update {b : Vec ℝ n} {l : Fin n → Bool} {m : Fin n}
    (hlm : l m = false) : -- --- CONCL ---
    ∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner (Function.update l m true) i =
      ∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner l i + b m := by -- --- PROOF ---
  have hsum : ∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner l i + b m =
      ∑ i, ((⟨0, b⟩ : Interval (Vec ℝ n)).corner l i + if i = m then b m else 0) := by
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq']; simp
  rw [hsum]
  -- coordinatewise: only `m` changes, from `0` to `bₘ`
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Interval.corner]
  by_cases him : i = m
  · subst him; simp [hlm]
  · simp [him]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
