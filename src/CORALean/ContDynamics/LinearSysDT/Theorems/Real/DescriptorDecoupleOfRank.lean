module

public import CORALean.ContDynamics.LinearSysDT.Definitions.HasDescriptorDecoupleRank
public import CORALean.Global.RankOneKroneckerGe

@[expose] public section

/-!
# The rank condition decouples the unknown input

[1, Eq. 6]: if the rank condition of Eq. 5 (`LinearSysDT.HasDescriptorDecoupleRank`) holds, there
are `T`, `N` with `TE + NC = I` (6a) and `TD_d = 0` (6b). With `M = [E D_d; C 0]`, `X = [T N]` and
`J = [I 0]` they are `X M = J`, i.e. `Mᵀ Xᵀ = Jᵀ`, and `vec (Mᵀ Xᵀ) = (I ⊗ Mᵀ) vec Xᵀ`. The rank
condition says the row `vec(Jᵀ)ᵀ` adds nothing to `I ⊗ M`, whose rank is at least `n_x · rank M`
(`rank_one_kronecker_ge`) and at most that of the stacked matrix: so `vec Jᵀ` is in the column space
of `I ⊗ Mᵀ`, which is a solution `Xᵀ`.

## Inputs
* `E` – descriptor matrix
* `Dd` – unknown input matrix
* `C` – output matrix

## Hypotheses
* `h` – the rank condition holds

## Conclusion
* decoupling matrices exist

## References

* [1] Y. Wang, V. Puig and G. Cembrano. "Set-membership approach and Kalman observer based on
      zonotopes for discrete-time descriptor systems". Automatica, 2018.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Kronecker

variable {nx ny nd : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.descriptorDecouple_of_rank (E : Mat ℝ nx nx) (Dd : Mat ℝ nx nd)
    (C : Mat ℝ ny nx) (h : LinearSysDT.HasDescriptorDecoupleRank E Dd C) : -- --- CONCL ---
    ∃ (T : Mat ℝ nx nx) (N : Mat ℝ nx ny), T * E + N * C = 1 ∧ T * Dd = 0 := by -- --- PROOF ---
  unfold LinearSysDT.HasDescriptorDecoupleRank at h
  simp only at h
  set M : Matrix (Fin nx ⊕ Fin ny) (Fin nx ⊕ Fin nd) ℝ := fromBlocks E Dd C 0 with hM
  set J : Matrix (Fin nx ⊕ Fin nd) (Fin nx) ℝ := fromRows 1 0 with hJ
  set K : Matrix (Fin nx × (Fin nx ⊕ Fin ny)) (Fin nx × (Fin nx ⊕ Fin nd)) ℝ :=
    (1 : Matrix (Fin nx) (Fin nx) ℝ) ⊗ₖ M with hK
  -- the added row adds no rank: it is in the row space of `I ⊗ M`
  have hge : nx * M.rank ≤ K.rank := by
    simpa using rank_one_kronecker_ge (ι := Fin nx) M
  set K' := fromRows K (Matrix.replicateRow Unit (vec J)) with hK'
  have hle : K.rank ≤ K'.rank := by
    have : K = K'.submatrix Sum.inl id := by
      ext i j; simp [hK']
    calc K.rank = (K'.submatrix Sum.inl id).rank := by rw [← this]
      _ ≤ K'.rank := Matrix.rank_submatrix_le _ _ _
  -- so the row `vec J` is in the row space of `I ⊗ M`
  have hrow : (vec J : Fin nx × (Fin nx ⊕ Fin nd) → ℝ) ∈ Submodule.span ℝ (Set.range K.row) := by
    have h1 : Submodule.span ℝ (Set.range K.row) ≤ Submodule.span ℝ (Set.range K'.row) :=
      Submodule.span_mono (by
        rintro _ ⟨i, rfl⟩
        exact ⟨Sum.inl i, by ext j; simp [hK']⟩)
    have h2 : Module.finrank ℝ (Submodule.span ℝ (Set.range K.row)) =
        Module.finrank ℝ (Submodule.span ℝ (Set.range K'.row)) := by
      rw [← Matrix.rank_eq_finrank_span_row, ← Matrix.rank_eq_finrank_span_row]
      exact le_antisymm hle (h ▸ hge)
    have h3 := Submodule.eq_of_le_of_finrank_eq h1 h2
    have h4 : (vec J : Fin nx × (Fin nx ⊕ Fin nd) → ℝ) ∈ Submodule.span ℝ (Set.range K'.row) :=
      Submodule.subset_span ⟨Sum.inr (), by ext j; simp [hK']⟩
    rwa [← h3] at h4
  -- a combination `y` of the rows with `yᵀ K = vec J`, and `y = vec Z`
  obtain ⟨y, hy⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hrow
  obtain ⟨Z, hZ⟩ := (Matrix.vec_bijective (m := Fin nx ⊕ Fin ny) (n := Fin nx)
    (R := ℝ)).2 y
  -- `Kᵀ y = vec J`, and `Kᵀ = I ⊗ Mᵀ`, so `vec (Mᵀ Z) = vec J`
  have hKy : Kᵀ *ᵥ y = vec J := by
    ext j
    have := congrFun hy j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.row] at this
    rw [mulVec_transpose]
    simpa [vecMul, dotProduct, mul_comm] using this
  have hKT : Kᵀ = (1 : Matrix (Fin nx) (Fin nx) ℝ) ⊗ₖ Mᵀ := by
    rw [hK]
    exact ((kroneckerMap_transpose _ _ _).symm.trans (by rw [transpose_one]))
  have hZJ : Mᵀ * Z = J := by
    refine Matrix.vec_inj.mp ?_
    rw [vec_mul_eq_mulVec, hZ, ← hKT, hKy]
  -- `X = Zᵀ = [T N]` solves `X M = [I 0]`
  have hXM : Zᵀ * M = fromCols 1 0 := by
    have := congrArg Matrix.transpose hZJ
    rw [transpose_mul, transpose_transpose, hJ, transpose_fromRows, transpose_one,
      transpose_zero] at this
    exact this
  rw [← fromCols_toCols Zᵀ, hM, fromCols_mul_fromBlocks] at hXM
  obtain ⟨h1, h2⟩ := fromCols_inj hXM
  refine ⟨Zᵀ.toCols₁, Zᵀ.toCols₂, by simpa using h1, by simpa using h2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
