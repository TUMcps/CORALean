import CORALean.ContDynamics.LinearSys.MatExp.ExpRemainderMat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeNorm
import CORALean.Global.Err

/-!
# `ε_H([t_i,t_i+Δt_i])`, eq. (21), and the two correction interval matrices it is built from

[1]'s eq. (21): `ε_H([t_i,t_{i+1}]) = err(e^{At_i} F_x(Δt_i,η_i) X_0 ⊕ e^{At_i} F_u(Δt_i,η_i) c_u)`,
the error of the homogeneous solution over the `i`-th step — `err` of `HR^+([0,Δt])`, eq. (19)'s
widening `F_x(Δt,η)X_0 ⊕ F_u(Δt,η)c_u`, carried to `t_i` by `e^{At_i}` as eq. (2) requires.
`err` is `r(box(·))` of [1, Prop. 1], the Euclidean radius at the origin.

`F_x` and `F_u` are eq. (17)-(18) as printed: a Minkowski sum over `k` of the scalar interval
`[(k^{-k/(k-1)} − k^{-1/(k-1)})Δt^k, 0]` times the matrix `A^k/k!` (for `F_u`, `A^{k-1}/k!` and
`k` up to `η+1`), plus the interval matrix `E(Δt,η)` of eq. (15)-(16) (for `F_u`, `E(Δt,η)Δt`).
`MatExp.corrCoeff k` is that coefficient, `aux_corrCoeff_eq` showing it equal to the printed
form at every `k ≥ 2`. An interval matrix acts on a set as the set of its members' images.

`MatExp.correctionMatrix` is not this `F_x`: it is CORA's enclosure, with `E` the uniform box of
the operator-norm bound rather than eq. (15)-(16)'s entrywise one, and there is no `F_u` beside it.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A member of `⊕ₖ [a_k, 0] B_k` is entrywise within `Σₖ |a_k| |(B_k)_{ij}|` of `0`. -/
theorem aux_abs_entry_le_of_mem_sum (s : Finset ℕ) (a : ℕ → ℝ) (B : ℕ → Mat ℝ n n)
    {M : Mat ℝ n n} (hM : M ∈ ∑ k ∈ s, (fun r : ℝ => r • B k) '' Set.Icc (a k) 0) (i j : Fin n) :
    |M i j| ≤ ∑ k ∈ s, |a k| * |B k i j| := by -- --- PROOF ---
  obtain ⟨g, hg, rfl⟩ := (Set.mem_finsetSum s _ M).mp hM
  rw [Matrix.sum_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  obtain ⟨r, ⟨hr1, hr2⟩, hrk⟩ := hg hk
  have hgk : g k i j = r * B k i j := by rw [← hrk]; rfl
  -- a point of `[a_k, 0]` is no larger in magnitude than `a_k`
  have hr : |r| ≤ |a k| := by
    rw [abs_of_nonpos hr2, abs_of_nonpos (hr1.trans hr2)]
    linarith
  rw [hgk, abs_mul]
  exact mul_le_mul_of_nonneg_right hr (abs_nonneg _)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1]'s eq. (17): `F_x(Δt,η) = ⊕_{k=2}^η [(k^{-k/(k-1)} − k^{-1/(k-1)})Δt^k, 0] A^k/k! ⊕ E(Δt,η)`,
as the set of matrices it contains. -/
noncomputable def MatExp.stateCorrectionSet (A : Mat ℝ n n) (Δt : ℝ) (η : ℕ) :
    Set (Mat ℝ n n) :=
  (∑ k ∈ Finset.Icc 2 η, (fun r : ℝ => r • (((Nat.factorial k : ℝ))⁻¹ • A ^ k)) ''
      Set.Icc (MatExp.corrCoeff k * Δt ^ k) 0)
    + MatExp.expRemainderInterval A Δt η

/-- [1]'s eq. (18):
`F_u(Δt,η) = ⊕_{k=2}^{η+1} [(k^{-k/(k-1)} − k^{-1/(k-1)})Δt^k, 0] A^{k-1}/k! ⊕ E(Δt,η)Δt`,
as the set of matrices it contains. -/
noncomputable def MatExp.inputCorrectionSet (A : Mat ℝ n n) (Δt : ℝ) (η : ℕ) :
    Set (Mat ℝ n n) :=
  (∑ k ∈ Finset.Icc 2 (η + 1), (fun r : ℝ => r • (((Nat.factorial k : ℝ))⁻¹ • A ^ (k - 1))) ''
      Set.Icc (MatExp.corrCoeff k * Δt ^ k) 0)
    + Δt • MatExp.expRemainderInterval A Δt η

/-- `e^{At_i} F_x(Δt,η) X_0 ⊕ e^{At_i} F_u(Δt,η) c_u`, the set eq. (21) takes `err` of: eq. (19)'s
`HR^+([0,Δt])` carried to the `i`-th step. -/
noncomputable def MatExp.homogeneousRemainderSet (A : Mat ℝ n n) (ti : ℝ) (X₀ : Set (Vec ℝ n))
    (cu : Vec ℝ n) (Δt : ℝ) (η : ℕ) : Set (Vec ℝ n) :=
  (fun x => (exp (ti • A)).mulVec x) ''
      Set.image2 (fun M x => M.mulVec x) (MatExp.stateCorrectionSet A Δt η) X₀
    + (fun x => (exp (ti • A)).mulVec x) ''
      ((fun M : Mat ℝ n n => M.mulVec cu) '' MatExp.inputCorrectionSet A Δt η)

/-- [1]'s eq. (21): `ε_H([t_i,t_i+Δt]) := err(e^{At_i} F_x(Δt,η) X_0 ⊕ e^{At_i} F_u(Δt,η) c_u)`. -/
noncomputable def MatExp.homogeneousRemainderError (A : Mat ℝ n n) (ti : ℝ) (X₀ : Set (Vec ℝ n))
    (cu : Vec ℝ n) (Δt : ℝ) (η : ℕ) : ℝ :=
  err (MatExp.homogeneousRemainderSet A ti X₀ cu Δt η)

/-- A member of `F_x(Δt,η)` is entrywise within its Taylor terms' reach plus `‖E(Δt,η)‖`. -/
theorem MatExp.abs_entry_le_of_mem_stateCorrectionSet {A : Mat ℝ n n} {Δt : ℝ} {η : ℕ}
    {M : Mat ℝ n n} (hM : M ∈ MatExp.stateCorrectionSet A Δt η) (i j : Fin n) :
    |M i j| ≤ (∑ k ∈ Finset.Icc 2 η, |MatExp.corrCoeff k * Δt ^ k|
        * |((((Nat.factorial k : ℝ))⁻¹ • A ^ k) : Mat ℝ n n) i j|)
      + ‖MatExp.expRemainderMat A Δt η‖ := by -- --- PROOF ---
  obtain ⟨Ms, hMs, ME, hME, rfl⟩ := Set.mem_add.mp hM
  have hs := aux_abs_entry_le_of_mem_sum (Finset.Icc 2 η) (fun k => MatExp.corrCoeff k * Δt ^ k)
    (fun k => ((Nat.factorial k : ℝ))⁻¹ • A ^ k) hMs i j
  -- the remainder block's entry is under `E`'s, hence under its norm
  have hE : |ME i j| ≤ ‖MatExp.expRemainderMat A Δt η‖ :=
    ((hME i j).trans (le_abs_self _)).trans (abs_entry_le_norm _ i j)
  rw [Matrix.add_apply]
  exact (abs_add_le _ _).trans (add_le_add hs hE)

/-- A member of `F_u(Δt,η)` is entrywise within its Taylor terms' reach plus `|Δt|·‖E(Δt,η)‖`. -/
theorem MatExp.abs_entry_le_of_mem_inputCorrectionSet {A : Mat ℝ n n} {Δt : ℝ} {η : ℕ}
    {M : Mat ℝ n n} (hM : M ∈ MatExp.inputCorrectionSet A Δt η) (i j : Fin n) :
    |M i j| ≤ (∑ k ∈ Finset.Icc 2 (η + 1), |MatExp.corrCoeff k * Δt ^ k|
        * |((((Nat.factorial k : ℝ))⁻¹ • A ^ (k - 1)) : Mat ℝ n n) i j|)
      + |Δt| * ‖MatExp.expRemainderMat A Δt η‖ := by -- --- PROOF ---
  obtain ⟨Ms, hMs, _, ⟨ME, hME, rfl⟩, rfl⟩ := Set.mem_add.mp hM
  have hs := aux_abs_entry_le_of_mem_sum (Finset.Icc 2 (η + 1))
    (fun k => MatExp.corrCoeff k * Δt ^ k) (fun k => ((Nat.factorial k : ℝ))⁻¹ • A ^ (k - 1))
    hMs i j
  -- the scaled remainder block's entry is `|Δt|` times one under `E`'s norm
  have hE : |(Δt • ME) i j| ≤ |Δt| * ‖MatExp.expRemainderMat A Δt η‖ := by
    rw [Matrix.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (((hME i j).trans (le_abs_self _)).trans (abs_entry_le_norm _ i j)) (abs_nonneg _)
  rw [Matrix.add_apply]
  exact (abs_add_le _ _).trans (add_le_add hs hE)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
