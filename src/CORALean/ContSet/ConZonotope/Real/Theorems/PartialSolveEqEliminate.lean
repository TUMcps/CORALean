module

public import CORALean.ContSet.ConZonotope.Real.Operations.Eliminate
public import CORALean.ContSet.ConZonotope.Real.Theorems.PartialSolveZeroCol
public import CORALean.ContSet.ConZonotope.Real.Theorems.PartialSolveZeroRow
public import CORALean.ContSet.ConZonotope.Real.Theorems.MemOfMatIff
public import CORALean.Global.DropIdx

@[expose] public section

/-!
# Partial solve, then drop, is `eliminate`

[1, Sec. 4.2]: removing the zero column and row of the partial-solve `Z̃` leaves one constraint
and one generator fewer, which is `ConZonotope.eliminate`, defined from the same `Λ_G` and `Λ_A`
in closed form. The two have the same set; their `ofMat` systems differ by the dropped index.

## Inputs
* `n` – dimension
* `q` – number of constraints
* `h` – number of generators
* `c` – center
* `G` – generators
* `A` – constraint matrix
* `b` – constraint offset
* `r` – constraint row to solve
* `j` – coefficient to eliminate

## Hypotheses
* `hAj` – pivot entry nonzero

## Conclusion
* the partial solve denotes the same set as eliminate

## References

* [1] [J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes: A new
      tool for set-based estimation and fault detection". Automatica,
      2016.](../../../../../../references/2016/scott-automatica-constrained-zonotopes.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A zero generator column `j` and a zero constraint row `r` can be dropped from `ofMat`. -/
private theorem ConZonotope.aux_mem_ofMat_drop_iff {α : Type} [AddCommGroup α] [Module ℝ α]
    {q h : ℕ} (c : α) (G : Fin h → α) (A : Mat ℝ q h) (b : Vec ℝ q) (r : Fin q) (j : Fin h)
    (hG : G j = 0) (hA : ∀ i, A i j = 0) (hr : ∀ l, A r l = 0) (hb : b r = 0)
    (x : α) : -- --- CONCL ---
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


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.2]: dropping the zero column and row of the partial-solve `Z̃` is `eliminate`. -/
theorem ConZonotope.partialSolve_eq_eliminate {n q h : ℕ} (c : Vec ℝ n)
    (G : Fin h → Vec ℝ n) (A : Mat ℝ q h) (b : Vec ℝ q) (r : Fin q) (j : Fin h)
    (hAj : A r j ≠ 0) : -- --- CONCL ---
    (ConZonotope.partialSolve c G A b r j).construct
      = (ConZonotope.eliminate c G A b r j).construct := by -- --- PROOF ---
  obtain ⟨hG, hA⟩ := ConZonotope.partialSolve_zero_col G A r j hAj
  obtain ⟨hr, hb⟩ := ConZonotope.partialSolve_zero_row A b r j hAj
  ext x
  unfold ConZonotope.partialSolve ConZonotope.constraintReduce
  rw [ConZonotope.aux_mem_ofMat_drop_iff _ _ _ _ r j hG hA hr hb]
  unfold ConZonotope.eliminate
  -- the dropped system is `eliminate`'s, entry for entry
  have hc : c + ConZonotope.partialSolveΛG G A r j *ᵥ b = c + b r • ((A r j)⁻¹ • G j) := by
    rw [ConZonotope.partialSolveΛG_mulVec]
  have hG' : (fun l => G l - ConZonotope.partialSolveΛG G A r j *ᵥ fun k => A k l)
      = fun l => G l - A r l • ((A r j)⁻¹ • G j) := by
    funext l; rw [ConZonotope.partialSolveΛG_mulVec]
  have hA' : A - ConZonotope.partialSolveΛA A r j * A
      = fun i l => A i l - A i j * (A r j)⁻¹ * A r l := by
    funext i l; rw [Matrix.sub_apply, ConZonotope.partialSolveΛA_mul]
  have hb' : b - ConZonotope.partialSolveΛA A r j *ᵥ b
      = fun i => b i - A i j * (A r j)⁻¹ * b r := by
    funext i; rw [Pi.sub_apply, ConZonotope.partialSolveΛA_mulVec]
  rw [hc, hG', hA', hb']

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
