module

public import CORALean.ContSet.HPolytope.Real.Theorems.ReduceOverDomainRows
public import CORALean.ContSet.HPolytope.Real.Theorems.NormalizeRowsExact

@[expose] public section

/-!
# `HPolytope.reduceOverDomain` encloses `P` over the domain

For type `'outer'`: every point of the domain in `P` satisfies the single reduced halfspace.
Any normalized row `i` gives `A_reduced' x ≤ b_i - (a_i - A_reduced)' x`, and `b_i` is at most the
supremum of `b`, `(a_i - A_reduced)' x` at least the infimum of `(A - A_reduced)' * dom`.
Needs a row to read from. An outer approximation over the domain, not the set `P` itself.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.reduceOverDomain_outer (P : HPolytope (Vec ℝ n)) (hm : 0 < P.m)
    (dom : Interval (Vec ℝ n)) :
    P.construct ∩ dom.construct ⊆
      (P.reduceOverDomain dom true).construct ∩ dom.construct := by -- --- PROOF ---
  -- the point satisfies the first normalized row, and that row is below the supremum of `b`
  rintro x ⟨hxP, hxd⟩
  refine ⟨⟨fun i => ?_, fun i => Fin.elim0 i⟩, hxd⟩
  have hxn : x ∈ P.normalizeRows.construct := by rw [HPolytope.normalizeRows_exact]; exact hxP
  have hrows := (HPolytope.reduceOverDomain_rows P dom hxd ⟨0, hm⟩).1
  have hbi : P.normalizeRows.b ⟨0, hm⟩ ≤ ⨆ k, P.normalizeRows.b k :=
    le_ciSup (f := P.normalizeRows.b) (Set.finite_range _).bddAbove ⟨0, hm⟩
  have hi : i = (0 : Fin 1) := Fin.fin_one_eq_zero i
  have h0 : P.normalizeRows.A ⟨0, hm⟩ x ≤ P.normalizeRows.b ⟨0, hm⟩ := hxn.1 ⟨0, hm⟩
  have h2 := le_trans hrows (le_trans h0 hbi)
  have key : (P.reduceOverDomain dom true).A (0 : Fin 1) x ≤
      (P.reduceOverDomain dom true).b (0 : Fin 1) := by linarith
  rw [hi]
  exact key

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
