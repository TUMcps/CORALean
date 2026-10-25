module

public import CORALean.ContSet.Interval.Real.Definitions.BoxPlane
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-!
# Where an edge meets the hyperplane

[1, Eq. 4]: the edge `e_uv(t) = v + t(u - v)`, [1, Eq. 3], meets `Σᵢ xᵢ = α` exactly at
`t⋆ = (α - Σᵢ vᵢ)/Σᵢ(uᵢ - vᵢ)`, and for `t⋆ ∈ [0, 1]` the edge holds that intersection. For two
adjacent vertices of a box the denominator is the edge's length `bⱼ - aⱼ`, nonzero for a box
with positive side lengths, which the division needs and the paper takes for granted.

## Inputs
* `v` – edge start
* `u` – edge end
* `α` – level of the hyperplane
* `t` – edge parameter

## Hypotheses
* `hden` – coordinate sums of the endpoints differ

## Conclusion
* the edge point lies in the hyperplane iff `t` takes the crossing value

## References

* [1] C. Lara, J. J. Flores and F. Calderon. "On the Hyperbox – Hyperplane Intersection Problem".
      INFOCOMP Journal of Computer Science, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.edge_mem_hyperplane_iff {v u : Vec ℝ n} {α t : ℝ}
    (hden : ∑ i, (u i - v i) ≠ 0) : -- --- CONCL ---
    v + t • (u - v) ∈ Interval.hyperplane 1 α ↔
      t = (α - ∑ i, v i) / ∑ i, (u i - v i) := by -- --- PROOF ---
  -- the sum along the edge is affine in `t`
  have hsum : ∑ i, (1 : Vec ℝ n) i * (v + t • (u - v)) i =
      ∑ i, v i + t * ∑ i, (u i - v i) := by
    simp only [Pi.one_apply, one_mul, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      Finset.sum_add_distrib, Finset.mul_sum]
  show ∑ i, (1 : Vec ℝ n) i * (v + t • (u - v)) i = α ↔ _
  rw [hsum, eq_div_iff hden]
  constructor <;> intro h <;> linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
