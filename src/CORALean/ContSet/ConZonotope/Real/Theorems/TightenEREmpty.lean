module

public import CORALean.ContSet.ConZonotope.Real.Theorems.TightenEROuter
public import CORALean.ContSet.ConZonotope.Real.Theorems.MemOfMatIff

@[expose] public section

/-!
# The emptiness test of `ConZonotope.tightenER`

[1, Alg. 1 (R)] and [2, Alg. 1]: "if `E ∩ R = ∅`, then `Z_c = ∅`", detected without a linear
program, "`E ∩ R = ∅` if `ξ^U_j < ρ^L_j` or `ξ^L_j > ρ^U_j` for any `j`" ([1]); [2] adds that
the test may be made in any iteration. Every point of `Z_c` has a coefficient vector in
`B∞(A, b)`, which `tightenER_outer` places in both `E_j` and `R_j`, so the two cannot be
disjoint while `Z_c` has a point.

## Inputs
* `nc` – number of constraints
* `ng` – number of generators
* `c` – center
* `G` – generators
* `A` – constraint matrix
* `b` – constraint offset
* `k` – number of extra passes
* `j` – coefficient index

## Hypotheses
* `hj` – the two bounds on that coefficient do not overlap

## Conclusion
* the constrained zonotope is empty

## References

* [1] [V. Raghuraman and J. P. Koeln. "Set operations and order reductions for constrained
      zonotopes". Automatica,
      2022.](../../../../../../references/2022/raghuraman-koeln-constrained-zonotopes.md)
* [2] [J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes: A new
      tool for set-based estimation and fault detection". Automatica,
      2016.](../../../../../../references/2016/scott-automatica-constrained-zonotopes.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1 (R)], [2, Alg. 1]: `E_j ∩ R_j = ∅` for some `j`, after any number of passes,
proves `Z_c = ∅`. -/
theorem ConZonotope.tightenER_empty {nc ng : ℕ} (c : α) (G : Fin ng → α) (A : Mat ℝ nc ng)
    (b : Vec ℝ nc) (k : ℕ) (j : Fin ng)
    (hj : ((ConZonotope.tightenER A b k).1.sup j : EReal) < (ConZonotope.tightenER A b k).2.1 j ∨
      (ConZonotope.tightenER A b k).2.2 j < ((ConZonotope.tightenER A b k).1.inf j : EReal))
    : -- --- CONCL ---
    (ConZonotope.ofMat c G A b).construct = ∅ := by -- --- PROOF ---
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  obtain ⟨β, hbox, heq, -⟩ := ConZonotope.mem_ofMat_iff.mp hx
  obtain ⟨hE, hR⟩ := ConZonotope.tightenER_outer A b k hbox heq
  -- `β_j` sits in both intervals, so neither strict separation can hold
  have hEj := hE j
  rcases hj with h | h
  · exact absurd (lt_of_lt_of_le h (hR j).1) (not_lt.mpr (EReal.coe_le_coe_iff.mpr hEj.2))
  · exact absurd (lt_of_le_of_lt (hR j).2 h) (not_lt.mpr (EReal.coe_le_coe_iff.mpr hEj.1))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
