import CORALean.ContSet.HPolytope.Real.Theorems.ReduceOverDomainRows
import CORALean.ContSet.HPolytope.Real.Theorems.NormalizeRowsExact

/-!
# `HPolytope.reduceOverDomain` of the other type lies in `P` over the domain

For the type that takes the infimum: every point of the domain satisfying the reduced halfspace
satisfies every normalized row `i`, `a_i' x ≤ A_reduced' x + sup (A - A_reduced)' * dom`, and
the infimum of `b` is below `b_i`. Only for a `P` without equality constraints, which
`reduceOverDomain` does not read. An inner approximation over the domain.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.reduceOverDomain_inner (P : HPolytope (Vec ℝ n)) (hme : P.me = 0)
    (dom : Interval (Vec ℝ n)) :
    (P.reduceOverDomain dom false).construct ∩ dom.construct ⊆
      P.construct ∩ dom.construct := by -- --- PROOF ---
  -- every normalized row is below the reduced one plus the supremum, and `inf b` is below `b_i`
  rintro x ⟨hxR, hxd⟩
  refine ⟨?_, hxd⟩
  rw [← HPolytope.normalizeRows_exact]
  have hempty : IsEmpty (Fin P.me) := by rw [hme]; infer_instance
  refine ⟨fun i => ?_, fun i => (hempty.false i).elim⟩
  have hrows := (HPolytope.reduceOverDomain_rows P dom hxd i).2
  have hbi : ⨅ k, P.normalizeRows.b k ≤ P.normalizeRows.b i :=
    ciInf_le (f := P.normalizeRows.b) (Set.finite_range _).bddBelow i
  linarith [hxR.1 (0 : Fin 1)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
