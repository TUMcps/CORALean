module

public import CORALean.ContDynamics.LinearSys.Krylov.Operations.Arnoldi

@[expose] public section

/-!
# The Arnoldi relation

What [1, Alg. 1] computes, column by column: `C v(k) = Σ_{i≤k} h_{i,k} v(i) + h_{k+1,k} v(k+1)`,
`C V_ξ = V_{ξ+1} H̄_ξ` read one column at a time — the identity behind [1]'s approximation (1).
The sweep leaves `w = C v(k) - Σ h_{i,k} v(i)` whatever the earlier vectors are, and line 12
divides it by `h_{k+1,k} = ‖w‖`; at a happy breakdown `‖w‖ = 0` makes `w = 0`, so the relation
holds for every column. That the `v(i)` are orthonormal, which makes `H` the projection of `C`,
is not shown here.

## Inputs
* `C` – matrix
* `v` – start vector
* `k` – step index

## Hypotheses
* none

## Conclusion
* the matrix maps the step's Arnoldi vector to its orthogonal expansion

## References

* [1] M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the Krylov
      Subspace". IEEE Transactions on Automatic Control, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   11-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- After `j` sweeps, `w` has lost exactly its components along `v(1), …, v(j)`. -/
private theorem Krylov.aux_gramSchmidtStep_eq (w : Vec ℝ n) (V : ℕ → Vec ℝ n)
    (j : ℕ) : -- --- CONCL ---
    (Krylov.gramSchmidtStep w V j).1
      = w - ∑ i ∈ Finset.range j, (Krylov.gramSchmidtStep w V j).2 i • V i := by -- --- PROOF ---
  induction j with
  | zero => simp [Krylov.gramSchmidtStep]
  | succ j ih =>
    simp only [Krylov.gramSchmidtStep]
    rw [Finset.sum_range_succ, Function.update_self]
    have hold : ∀ i ∈ Finset.range j, Function.update (Krylov.gramSchmidtStep w V j).2 j
        ((Krylov.gramSchmidtStep w V j).1 ⬝ᵥ V j) i • V i
          = (Krylov.gramSchmidtStep w V j).2 i • V i := by
      intro i hi
      rw [Function.update_of_ne (Finset.mem_range.mp hi).ne]
    rw [Finset.sum_congr rfl hold]
    generalize (Krylov.gramSchmidtStep w V j).1 ⬝ᵥ V j = d
    rw [ih]
    abel


/-- `‖w‖ (‖w‖⁻¹ w) = w`, also at `w = 0`, where line 12 divides by zero. -/
private theorem Krylov.aux_norm₂_smul_inv_smul (w : Vec ℝ n) : -- --- CONCL ---
    ‖w‖₂ • (‖w‖₂⁻¹ • w) = w := by -- --- PROOF ---
  rcases eq_or_ne ‖w‖₂ 0 with h | h
  · funext j
    have hj := abs_le_norm₂ w j
    rw [h] at hj ⊢
    simp only [zero_smul, Pi.zero_apply]
    exact (abs_nonpos_iff.mp hj).symm
  · rw [smul_smul, mul_inv_cancel₀ h, one_smul]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Krylov.arnoldi_relation (C : Mat ℝ n n) (v : Vec ℝ n) (k : ℕ) : -- --- CONCL ---
    C *ᵥ (Krylov.arnoldi C v (k + 1)).1 k
      = ∑ i ∈ Finset.range (k + 1),
          (Krylov.arnoldi C v (k + 1)).2 i k • (Krylov.arnoldi C v (k + 1)).1 i
        + (Krylov.arnoldi C v (k + 1)).2 (k + 1) k
          • (Krylov.arnoldi C v (k + 1)).1 (k + 1) := by -- --- PROOF ---
  set V := (Krylov.arnoldi C v k).1 with hV
  set swept := Krylov.gramSchmidtStep (C *ᵥ V k) V (k + 1) with hswept
  -- the new column of `H`, and the vectors up to `v(k+1)` as they were
  have hH : ∀ i, (Krylov.arnoldi C v (k + 1)).2 i k
      = if i ≤ k then swept.2 i else if i = k + 1 then ‖swept.1‖₂ else 0 := by
    intro i
    simp only [Krylov.arnoldi, if_true]
    rfl
  have hVold : ∀ i ≤ k, (Krylov.arnoldi C v (k + 1)).1 i = V i := by
    intro i hi
    simp only [Krylov.arnoldi]
    rw [Function.update_of_ne (by omega)]
  have hVnew : (Krylov.arnoldi C v (k + 1)).1 (k + 1) = ‖swept.1‖₂⁻¹ • swept.1 := by
    simp only [Krylov.arnoldi, Function.update_self]
    rfl
  have hh : (Krylov.arnoldi C v (k + 1)).2 (k + 1) k = ‖swept.1‖₂ := by
    rw [hH, if_neg (by omega), if_pos rfl]
  -- `h_{k+1,k} v(k+1)` is the swept `w`, and the sweep took off `Σ h_{i,k} v(i)`
  rw [hh, hVnew, Krylov.aux_norm₂_smul_inv_smul, hVold k le_rfl, hswept,
    Krylov.aux_gramSchmidtStep_eq]
  have hcol : ∀ i ∈ Finset.range (k + 1), (Krylov.arnoldi C v (k + 1)).2 i k
      • (Krylov.arnoldi C v (k + 1)).1 i = swept.2 i • V i := by
    intro i hi
    have hi' : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [hH, if_pos hi', hVold i hi']
  rw [Finset.sum_congr rfl hcol]
  abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
