module

public import CORALean.ContSet.ConZonotope.Real.Operations.PartialSolve
public import CORALean.ContSet.ConZonotope.Real.Theorems.MemOfMatIff
public import CORALean.ContSet.ConZonotope.Real.Theorems.PartialSolveLamAMulVec
public import CORALean.ContSet.ConZonotope.Real.Theorems.PartialSolveLamGMulVec
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# The partial-solve `Z̃` is `Z` without `|ξ_j| ≤ 1`

[1, Sec. 4.2 (choice of j)]: eliminating `ξ_j` by row `r` of `Aξ = b` (eqs. 28-29) keeps that row
implicitly, "however, the ability to enforce the bound `|ξ_j| < 1` has been lost", so
`Z̃ = {Gξ + c : Aξ = b, |ξ_i| ≤ 1, ∀ i ≠ j}`, and this is an equality.

From a coefficient vector `β` of `Z̃`, `ξ = β + s·e_j`, with `s` the slack row `r` leaves,
satisfies every row of `Aξ = b` and gives the same point. Back from `ξ`, `β = ξ - ξ_j·e_j` is a
coefficient vector of `Z̃`. Column `j` of `Z̃`'s system is zero, so `β_j` does not matter.

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
* the partial solve is the set without the bound on that coefficient

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Row `i` of `Z̃`'s system at `β`, written out in `A`, `b` and row `r`. -/
theorem ConZonotope.aux_partialSolve_row {q h : ℕ} (A : Mat ℝ q h) (b : Vec ℝ q) (r : Fin q)
    (j : Fin h) (β : Vec ℝ h) (i : Fin q) : -- --- CONCL ---
    ((A - ConZonotope.partialSolveΛA A r j * A) *ᵥ β) i
        = (b - ConZonotope.partialSolveΛA A r j *ᵥ b) i ↔
      (A *ᵥ β) i - A i j * (A r j)⁻¹ * (A *ᵥ β) r
        = b i - A i j * (A r j)⁻¹ * b r := by -- --- PROOF ---
  rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, Pi.sub_apply, Pi.sub_apply,
    ConZonotope.partialSolveΛA_mulVec, ConZonotope.partialSolveΛA_mulVec]

/-- `Z̃`'s point at `β`, written out in `c`, `G` and row `r`. -/
theorem ConZonotope.aux_partialSolve_point {n q h : ℕ} (c : Vec ℝ n) (G : Fin h → Vec ℝ n)
    (A : Mat ℝ q h) (b : Vec ℝ q) (r : Fin q) (j : Fin h) (β : Vec ℝ h) : -- --- CONCL ---
    c + ConZonotope.partialSolveΛG G A r j *ᵥ b
        + ∑ l, β l • (G l - ConZonotope.partialSolveΛG G A r j *ᵥ fun k => A k l)
      = c + ∑ l, β l • G l + ((A r j)⁻¹ * (b r - (A *ᵥ β) r)) • G j := by -- --- PROOF ---
  simp only [ConZonotope.partialSolveΛG_mulVec, smul_sub, Finset.sum_sub_distrib, smul_smul,
    Matrix.mulVec, dotProduct, Finset.sum_smul, mul_sub, sub_smul,
    Finset.mul_sum]
  have : ∀ l, β l * (A r l * (A r j)⁻¹) = (A r j)⁻¹ * (A r l * β l) := fun l => by ring
  simp only [this, mul_comm (b r) (A r j)⁻¹]
  abel


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.2 (choice of j)]: at `a_rj ≠ 0`, `Z̃ = {Gξ + c : Aξ = b, |ξ_i| ≤ 1, ∀ i ≠ j}`. -/
theorem ConZonotope.partialSolve_construct_eq {n q h : ℕ} (c : Vec ℝ n) (G : Fin h → Vec ℝ n)
    (A : Mat ℝ q h) (b : Vec ℝ q) (r : Fin q) (j : Fin h) (hAj : A r j ≠ 0) : -- --- CONCL ---
    (ConZonotope.partialSolve c G A b r j).construct
      = {x | ∃ ξ : Vec ℝ h, (∀ i, i ≠ j → |ξ i| ≤ 1) ∧ (∀ i, (A *ᵥ ξ) i = b i) ∧
          x = c + ∑ k, ξ k • G k} := by -- --- PROOF ---
  ext x
  unfold ConZonotope.partialSolve ConZonotope.constraintReduce
  rw [ConZonotope.mem_ofMat_iff, Set.mem_setOf_eq]
  -- `e_j` and what `A` and the generators make of it
  have hAe : ∀ i, (A *ᵥ (Pi.single j 1 : Vec ℝ h)) i = A i j := fun i => by
    simp [Matrix.mulVec_single]
  have hGe : ∑ k, (Pi.single j 1 : Vec ℝ h) k • G k = G j := by
    simp [Pi.single_apply]
  constructor
  · rintro ⟨β, hβ, hA, rfl⟩
    -- the slack row `r` leaves, put back on `ξ_j`
    set s := (A r j)⁻¹ * (b r - (A *ᵥ β) r) with hs
    refine ⟨β + s • Pi.single j 1, fun i hi => ?_, fun i => ?_, ?_⟩
    · simpa [Pi.single_apply, hi] using hβ i
    · have hi := (ConZonotope.aux_partialSolve_row A b r j β i).mp (hA i)
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, hAe, smul_eq_mul,
        hs]
      linear_combination hi
    · rw [ConZonotope.aux_partialSolve_point, ← hs]
      have hsum : ∑ k, (β + s • Pi.single j 1 : Vec ℝ h) k • G k = ∑ k, β k • G k + s • G j := by
        simp only [Pi.add_apply, Pi.smul_apply, add_smul, Finset.sum_add_distrib, smul_eq_mul,
          mul_smul, ← Finset.smul_sum, hGe]
      rw [hsum, add_assoc]
  · rintro ⟨ξ, hξ, hA, rfl⟩
    -- drop `ξ_j`: `Z̃`'s column `j` is zero, so `β_j = 0` loses nothing
    have ha : (A r j)⁻¹ * A r j = 1 := inv_mul_cancel₀ hAj
    have hrow : ∀ i, (A *ᵥ (ξ - ξ j • Pi.single j 1)) i = b i - ξ j * A i j := fun i => by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, hAe, smul_eq_mul,
        hA]
    refine ⟨ξ - ξ j • Pi.single j 1, fun i => ?_, fun i => ?_, ?_⟩
    · rcases eq_or_ne i j with rfl | hi
      · simp
      · simpa [Pi.single_apply, hi] using hξ i hi
    · rw [ConZonotope.aux_partialSolve_row, hrow, hrow]
      linear_combination (A i j * ξ j) * ha
    · rw [ConZonotope.aux_partialSolve_point, hrow]
      have hco : (A r j)⁻¹ * (b r - (b r - ξ j * A r j)) = ξ j := by
        rw [sub_sub_cancel, mul_comm (ξ j), ← mul_assoc, ha, one_mul]
      have hsum : ∑ k, (ξ - ξ j • Pi.single j 1 : Vec ℝ h) k • G k
          = ∑ k, ξ k • G k - ξ j • G j := by
        simp only [Pi.sub_apply, Pi.smul_apply, sub_smul, Finset.sum_sub_distrib, smul_eq_mul,
          mul_smul, ← Finset.smul_sum, hGe]
      rw [hco, hsum]
      abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
