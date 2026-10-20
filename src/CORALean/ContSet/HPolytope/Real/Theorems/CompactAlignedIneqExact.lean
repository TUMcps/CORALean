module

public import CORALean.ContSet.HPolytope.Real.Operations.CompactAlignedIneq
public import CORALean.ContSet.HPolytope.Real.Theorems.NormalizeRowsExact
public import CORALean.ContSet.HPolytope.Real.Theorems.RestrictConstruct

@[expose] public section

/-!
# `compactAlignedIneq` denotes the same set, exactly

Rows with the same normal vector `a` say `aᵀx ≤ b` for several `b`, which is the smallest one.

## Inputs
* `P` – H-polytope

## Hypotheses
* none

## Conclusion
* `compactAlignedIneq` denotes the same set, exactly
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.compactAlignedIneq_exact (P : HPolytope (Vec ℝ n)) : -- --- CONCL ---
    P.compactAlignedIneq.construct = P.construct := by -- --- PROOF ---
  rw [← P.normalizeRows_exact]
  unfold HPolytope.compactAlignedIneq
  generalize P.normalizeRows = Q
  simp only [HPolytope.restrict_construct, Finset.mem_filter, Finset.mem_univ, true_and]
  ext x
  simp only [Set.mem_setOf_eq, HPolytope.construct]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, fun r => h2 r trivial⟩
    -- the row of `i`'s class that is smallest in `(b, index)` is kept, and bounds `i`
    obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image
      (Finset.univ.filter fun j => Q.A j = Q.A i) (fun j => toLex (Q.b j, j))
      ⟨i, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hmin
    have hkeep : ∀ k, Q.A k = Q.A j → toLex (Q.b j, j) ≤ toLex (Q.b k, k) :=
      fun k hk => hmin k (hk.trans hj)
    have hle := hmin i rfl
    have hbi : Q.b j ≤ Q.b i := by
      rcases Prod.Lex.le_iff.mp hle with h | ⟨h, _⟩
      · exact h.le
      · exact h.le
    calc Q.A i x = Q.A j x := by rw [hj]
      _ ≤ Q.b j := h1 j hkeep
      _ ≤ Q.b i := hbi
  · rintro ⟨h1, h2⟩
    exact ⟨fun i _ => h1 i, fun r _ => h2 r⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
