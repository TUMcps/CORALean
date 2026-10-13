module

public import CORALean.ContSet.ConZonotope.Real.Operations.MemOfMatIff
public import CORALean.Global.DropIdx

@[expose] public section

/-!
# Dropping a zero column and a zero row

A generator column that is zero in both `G` and `A`, and a constraint row that is zero in `A` and
`b`, change nothing in `ofMat`'s set: the column's coefficient is free and the row is `0 = 0`.
This is the "removing these columns and rows" of [1, Sec. 4.2].

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- A zero generator column `j` and a zero constraint row `r` can be dropped from `ofMat`. -/
theorem ConZonotope.mem_ofMat_drop_iff {α : Type} [AddCommGroup α] [Module ℝ α] {q h : ℕ}
    (c : α) (G : Fin h → α) (A : Mat ℝ q h) (b : Vec ℝ q) (r : Fin q) (j : Fin h)
    (hG : G j = 0) (hA : ∀ i, A i j = 0) (hr : ∀ l, A r l = 0) (hb : b r = 0) (x : α) :
    x ∈ (ConZonotope.ofMat c G A b).construct ↔
      x ∈ (ConZonotope.ofMat c (G ∘ dropIdx j)
        (fun i k => A (dropIdx r i) (dropIdx j k)) (b ∘ dropIdx r)).construct := by -- --- PROOF ---
  rw [ConZonotope.mem_ofMat_iff, ConZonotope.mem_ofMat_iff]
  constructor
  · rintro ⟨β, hβ, hAβ, hx⟩
    refine ⟨β ∘ dropIdx j, fun k => hβ _, fun i => ?_, ?_⟩
    · -- row `dropIdx r i`, with the zero term at `j` split off
      have := hAβ (dropIdx r i)
      rw [Matrix.mulVec_apply_eq_sum, sum_dropIdx j (fun l => A (dropIdx r i) l * β l),
        hA, zero_mul, zero_add] at this
      simpa [Matrix.mulVec_apply_eq_sum] using this
    · rw [hx, sum_dropIdx j (fun l => β l • G l), hG, smul_zero, zero_add]
      rfl
  · rintro ⟨β', hβ', hAβ', hx⟩
    -- extend `β'` by zero at `j`
    refine ⟨insertIdx j 0 β', ?_, ?_, ?_⟩
    · rw [forall_dropIdx_iff j]
      exact ⟨by simp, fun k => by simpa using hβ' k⟩
    · rw [forall_dropIdx_iff r]
      refine ⟨by simp [Matrix.mulVec_apply_eq_sum, hr, hb], fun k => ?_⟩
      have := hAβ' k
      rw [Matrix.mulVec_apply_eq_sum,
        sum_dropIdx j (fun l => A (dropIdx r k) l * insertIdx j 0 β' l)]
      simpa [Matrix.mulVec_apply_eq_sum] using this
    · rw [hx, sum_dropIdx j (fun l => insertIdx j 0 β' l • G l)]
      simp [hG]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
