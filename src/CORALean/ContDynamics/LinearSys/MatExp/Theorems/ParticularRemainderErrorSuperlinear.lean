module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ParticularRemainderError
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IsBoundedParticularRemainderSet
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SuperlinearDecreaseExpRemainderMat

@[expose] public section

/-!
# `Thm. 2`: `ε_P` of eq. (22) decreases superlinearly

[1, Thm. 2]: `∀φ∈(0,1): ε_P([t_i,t_i+φΔt_i]) ≤ φ ε_P([t_i,t_i+Δt_i])`, with
`ε_P = err(e^{At_i} E(Δt_i,η_i) Δt_i U)` of eq. (22) — at the `i`-th step, and at `err` itself.

[1]'s proof, followed: it suffices that `PR^+([t_i,t_i+φΔt_i]) ⊆ φ PR^+([t_i,t_i+Δt_i])`, and
`Lemma 1` (`superlinearDecrease_expRemainderMat`) writes a member `M` of `E(φΔt,η)` as `φ M'`
with `M'` in `E(Δt,η)`. Then `e^{At_i} M (φΔt u) = φ · e^{At_i} (φM') (Δt u)`, and `φM'` is
still in `E(Δt,η)`, the interval matrix being symmetric about `0` and `φ ≤ 1` — the second
factor `φ` [1] absorbs with its closing `φ ∈ (0,1)` step. `err` is monotone and scales with a
non-negative factor (`err_mono`, `err_smul_of_nonneg`), which is [1]'s "it suffices to show
that the enclosing radius decreases superlinearly".

`0 ≤ Δt` is a step length's sign, and `U` bounded is what makes `err` the enclosing radius
rather than a junk value; [1]'s `U` is a zonotope. [1] states `Thm. 2` as an instance of
`Def. 1`, whose displayed inequality is the statement here.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `E_abs(Δt,η)` is entrywise non-negative at every step `Δt ≥ 0`, every term of its series
being so. -/
theorem aux_expRemainderMat_entry_nonneg (A : Mat ℝ n n) {Δt : ℝ} (hΔt : 0 ≤ Δt) (η : ℕ)
    (j k : Fin n) : 0 ≤ MatExp.expRemainderMat A Δt η j k := by
  refine (MatExp.hasSum_expRemainderMat_entry A Δt η j k).nonneg fun i => ?_
  have hP : 0 ≤ ((MatExp.absMat A) ^ (i + (η + 1))) j k :=
    (abs_nonneg _).trans (abs_pow_entry_le_absMat_pow_entry A (i + (η + 1)) j k)
  positivity

/-- `e^{At_i} E(φΔt,η) φΔt U ⊆ φ · e^{At_i} E(Δt,η) Δt U`, [1]'s set inclusion. -/
theorem aux_particularRemainderSet_subset (A : Mat ℝ n n) (ti : ℝ) (U : Set (Vec ℝ n)) (η : ℕ)
    {Δt : ℝ} (hΔt : 0 ≤ Δt) {φ : ℝ} (hφ : φ ∈ Set.Ioo (0 : ℝ) 1) :
    MatExp.particularRemainderSet A ti U (φ * Δt) η
      ⊆ φ • MatExp.particularRemainderSet A ti U Δt η := by -- --- PROOF ---
  rintro _ ⟨_, ⟨M, hM, _, ⟨u, hu, rfl⟩, rfl⟩, rfl⟩
  -- `M` lies in `E(φΔt,η)`, which `Lemma 1` puts inside `φ E(Δt,η)`
  have hMmem : M ∈ MatExp.expRemainderInterval A (φ * Δt) η :=
    fun j k => (hM j k).trans_eq
      (abs_of_nonneg (aux_expRemainderMat_entry_nonneg A (mul_nonneg hφ.1.le hΔt) η j k))
  obtain ⟨M', hM', rfl⟩ := MatExp.superlinearDecrease_expRemainderMat A η hΔt φ hφ hMmem
  -- `φ M'` is again in `E(Δt,η)`, and the remaining `φ` comes out of the linear maps
  have hφM' : ∀ j k, |(φ • M') j k| ≤ |MatExp.expRemainderMat A Δt η j k| := by
    intro j k
    rw [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hφ.1,
      abs_of_nonneg (aux_expRemainderMat_entry_nonneg A hΔt η j k)]
    exact (mul_le_of_le_one_left (abs_nonneg _) hφ.2.le).trans (hM' j k)
  refine ⟨(exp (ti • A)).mulVec ((φ • M').mulVec (Δt • u)),
    ⟨_, ⟨φ • M', hφM', _, Set.smul_mem_smul_set hu, rfl⟩, rfl⟩, ?_⟩
  simp only [mul_smul, Matrix.mulVec_smul]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 2]: `ε_P([t_i,t_i+φΔt]) ≤ φ ε_P([t_i,t_i+Δt])` for every `φ ∈ (0,1)`, with
`ε_P = err(e^{At_i} E(Δt,η) Δt U)` of eq. (22), at every step start `t_i`, order `η` and step
`Δt ≥ 0`. -/
theorem MatExp.particularRemainderError_superlinear (A : Mat ℝ n n) (ti : ℝ)
    {U : Set (Vec ℝ n)} (hU : Bornology.IsBounded U) (η : ℕ) {Δt : ℝ} (hΔt : 0 ≤ Δt) :
    ∀ φ ∈ Set.Ioo (0 : ℝ) 1, MatExp.particularRemainderError A ti U (φ * Δt) η
      ≤ φ * MatExp.particularRemainderError A ti U Δt η := by -- --- PROOF ---
  intro φ hφ
  rcases (MatExp.particularRemainderSet A ti U (φ * Δt) η).eq_empty_or_nonempty with he | hne
  -- an empty set has the empty box, whose farthest corner is the origin
  · have h0 : err (∅ : Set (Vec ℝ n)) = 0 := by
      simp only [err, Set.image_empty, Real.sSup_empty, Real.sInf_empty, abs_zero, max_self]
      exact norm₂_zero
    rw [MatExp.particularRemainderError, he, h0]
    exact mul_nonneg hφ.1.le (err_nonneg _)
  · calc MatExp.particularRemainderError A ti U (φ * Δt) η
        ≤ err (φ • MatExp.particularRemainderSet A ti U Δt η) :=
          err_mono hne ((MatExp.isBounded_particularRemainderSet A ti hU Δt η).smul₀ φ)
            (aux_particularRemainderSet_subset A ti U η hΔt hφ)
      _ = φ * MatExp.particularRemainderError A ti U Δt η := err_smul_of_nonneg hφ.1.le _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
