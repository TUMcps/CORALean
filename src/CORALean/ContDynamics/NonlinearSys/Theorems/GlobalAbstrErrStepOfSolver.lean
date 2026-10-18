module

public import CORALean.ContDynamics.NonlinearSys.Theorems.GlobalAbstrErrEqLocalAbstrErr
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSmulSubOneLe
public import CORALean.Global.BoxDiameterMulVecImageLe
public import CORALean.Global.BoxDiameterAddLe

@[expose] public section

/-!
# `hstep`, derived from (10) at a single fixed linearization matrix

[1, Lemma 2]'s Appendix B expands (10) with `A(Δtₖ)` written `A`, "for ease of
notation" — one fixed matrix, the honest reading for a step that does not
re-linearize. `R (k+1) = e^{AΔt}R(k) ⊕ P(k) ⊞ Rabs(k)` and
`R̂ (k+1) = e^{AΔt}R̂(k) ⊕ P(k)` share `P(k)`, and reassociating it away — not
cancelling it through `⊖`, which fails for the erosion `minkowskiDiff` on bare
sets without a Rådström argument this general — leaves `R(k) = R̂(k) + E(k)`
for the honestly-tracked error `E(k+1) := e^{AΔt}E(k) ⊞ Rabs(k)`, `E(0) = {0}`.
`aux_exists_solverError` is that invariant; the two `boxDiameter` bounds turn
it into `hstep`'s `(1+LΔt)εₖ+εₖ,loc` with `L := ‖A‖e^{t_end‖A‖}`, valid across
the whole of `Δt ∈ (0, t_end]` and not only a neighbourhood of `0`.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `R` stays `R̂`'s own run widened by an explicit, well-behaved error set: (B.1)-(B.2)'s
content once the shared `P k` reassociates away, tracked forward instead of read off `⊖`. -/
theorem aux_exists_solverError {A : Mat ℝ n n} {Δt : ℝ} {N : ℕ}
    {R Rhat Rabs P : ℕ → Set (Vec ℝ n)} (hR0 : R 0 = Rhat 0)
    (hB1 : ∀ k < N, R (k + 1) = (exp (Δt • A)).mulVec '' R k + P k + Rabs k)
    (hB2 : ∀ k < N, Rhat (k + 1) = (exp (Δt • A)).mulVec '' Rhat k + P k)
    (hRabsNe : ∀ k < N, (Rabs k).Nonempty) (hRabsConv : ∀ k < N, Convex ℝ (Rabs k))
    (hRabsCpt : ∀ k < N, IsCompact (Rabs k)) : -- --- STMT ---
    ∀ k ≤ N, ∃ E : Set (Vec ℝ n), E.Nonempty ∧ Convex ℝ E ∧ IsCompact E ∧
      R k = Rhat k + E := by -- --- PROOF ---
  intro k
  induction k with
  | zero => exact fun _ => ⟨{0}, Set.singleton_nonempty 0, convex_singleton 0,
      isCompact_singleton, by simp [hR0]⟩
  | succ k ih =>
    intro hk
    have hkN : k < N := by omega
    obtain ⟨E, hEne, hEconv, hEcpt, hRk⟩ := ih (by omega)
    set M := exp (Δt • A) with hM
    refine ⟨M.mulVec '' E + Rabs k, hEne.image _ |>.add (hRabsNe k hkN),
      (hEconv.linear_image (Matrix.mulVecLin M)).add (hRabsConv k hkN),
      (hEcpt.image (Matrix.mulVecLin M).continuous_of_finiteDimensional).add (hRabsCpt k hkN),
      ?_⟩
    have himg : M.mulVec '' (Rhat k + E) = M.mulVec '' Rhat k + M.mulVec '' E :=
      Set.image_add (Matrix.mulVecLin M)
    rw [hB1 k hkN, hB2 k hkN, hRk, himg]
    abel


-- =======================================  MAIN THEOREM  ======================================= --

/-- `[1]`'s `hstep`, honestly derived rather than assumed: for a *fixed* `A`, one step of a
solver "of the form (10)" grows the global error by at most `1 + LΔt` before adding its own
local error, with `L := ‖A‖e^{t_end‖A‖}` independent of `Δt` and of `N`. -/
theorem globalAbstrErr_succ_le_of_solver {A : Mat ℝ n n} {Δt tEnd : ℝ} (hΔt : 0 < Δt)
    (htEnd : Δt ≤ tEnd) {N : ℕ} {R Rhat Rabs P : ℕ → Set (Vec ℝ n)} (hR0 : R 0 = Rhat 0)
    (hB1 : ∀ k < N, R (k + 1) = (exp (Δt • A)).mulVec '' R k + P k + Rabs k)
    (hB2 : ∀ k < N, Rhat (k + 1) = (exp (Δt • A)).mulVec '' Rhat k + P k)
    (hRhatNe : ∀ k ≤ N, (Rhat k).Nonempty) (hRhatBdd : ∀ k ≤ N, Bornology.IsBounded (Rhat k))
    (hRabsNe : ∀ k < N, (Rabs k).Nonempty) (hRabsConv : ∀ k < N, Convex ℝ (Rabs k))
    (hRabsCpt : ∀ k < N, IsCompact (Rabs k)) {k : ℕ} (hk : k < N) : -- --- STMT ---
    globalAbstrErr (R (k + 1)) (Rhat (k + 1)) ≤
      (1 + ‖A‖ * Real.exp (tEnd * ‖A‖) * Δt) * globalAbstrErr (R k) (Rhat k)
        + localAbstrErr (Rabs k) := by -- --- PROOF ---
  -- `Rk`'s own error set, carried forward one step: `E' := M.mulVec '' E + Rabs k`
  obtain ⟨E, hEne, hEconv, hEcpt, hRk⟩ :=
    aux_exists_solverError hR0 hB1 hB2 hRabsNe hRabsConv hRabsCpt k hk.le
  set M := exp (Δt • A) with hM
  set E' := M.mulVec '' E + Rabs k with hE'def
  have hE'ne : E'.Nonempty := (hEne.image _).add (hRabsNe k hk)
  have hE'conv : Convex ℝ E' := (hEconv.linear_image (Matrix.mulVecLin M)).add (hRabsConv k hk)
  have hE'cpt : IsCompact E' :=
    (hEcpt.image (Matrix.mulVecLin M).continuous_of_finiteDimensional).add (hRabsCpt k hk)
  -- the successor step really does land on `Rhat (k+1) + E'`, by the same reassociation
  have hRsucc : R (k + 1) = Rhat (k + 1) + E' := by
    have himg : M.mulVec '' (Rhat k + E) = M.mulVec '' Rhat k + M.mulVec '' E :=
      Set.image_add (Matrix.mulVecLin M)
    rw [hB1 k hk, hB2 k hk, hRk, himg, hE'def]; abel
  -- Rådström cancellation, `Def. 4`'s two forms of the local error, at each of `Rk`, `R(k+1)`
  have hstep1 : globalAbstrErr (R (k + 1)) (Rhat (k + 1)) = localAbstrErr E' := by
    rw [hRsucc]
    exact globalAbstrErr_eq_localAbstrErr (hRhatNe (k + 1) hk) (hRhatBdd (k + 1) hk) hE'conv
      hE'cpt.isClosed
  have hstep2 : globalAbstrErr (R k) (Rhat k) = localAbstrErr E := by
    rw [hRk]
    exact globalAbstrErr_eq_localAbstrErr (hRhatNe k hk.le) (hRhatBdd k hk.le) hEconv hEcpt.isClosed
  -- both `globalAbstrErr`s read off `Def. 4`'s local measure at `E` and `E'` in turn
  have hMEcpt : IsCompact (M.mulVec '' E) :=
    hEcpt.image (Matrix.mulVecLin M).continuous_of_finiteDimensional
  have hbd1 : ‖boxDiameter (M.mulVec '' E + Rabs k)‖
      ≤ ‖boxDiameter (M.mulVec '' E)‖ + ‖boxDiameter (Rabs k)‖ :=
    boxDiameter_add_le (hEne.image _) (hRabsNe k hk) hMEcpt.isBounded (hRabsCpt k hk).isBounded
  have hbd2 : ‖boxDiameter (M.mulVec '' E)‖ ≤ ‖M‖ * ‖boxDiameter E‖ :=
    boxDiameter_mulVec_image_le hEne hEcpt.isBounded
  have hbound : localAbstrErr E' ≤ ‖M‖ * localAbstrErr E + localAbstrErr (Rabs k) := by
    rw [hE'def]
    unfold localAbstrErr at *
    linarith
  -- `‖M‖ ≤ 1 + LΔt`: the identity's norm plus the Taylor bound on `e^{AΔt} - 1`
  have hone : ‖(1 : Mat ℝ n n)‖ ≤ 1 := by
    classical
    rcases isEmpty_or_nonempty (Fin n) with h | h
    · rw [Subsingleton.elim (1 : Mat ℝ n n) 0, norm_zero]; norm_num
    · have : NormOneClass (Mat ℝ n n) := Matrix.linfty_opNormOneClass
      rw [norm_one]
  -- `Δt ≤ t_end` lets `Real.exp (Δt‖A‖)` be bounded by the `Δt`-free `Real.exp (t_end‖A‖)`
  have hexp := Real.norm_exp_smul_sub_one_le A hΔt.le
  have hmono : Δt * ‖A‖ ≤ tEnd * ‖A‖ := mul_le_mul_of_nonneg_right htEnd (norm_nonneg A)
  have hexp2 : Real.exp (Δt * ‖A‖) ≤ Real.exp (tEnd * ‖A‖) := Real.exp_le_exp.mpr hmono
  have hexp3 : Δt * ‖A‖ * Real.exp (Δt * ‖A‖) ≤ Δt * ‖A‖ * Real.exp (tEnd * ‖A‖) :=
    mul_le_mul_of_nonneg_left hexp2 (by positivity)
  have hMnorm : ‖M‖ ≤ 1 + ‖A‖ * Real.exp (tEnd * ‖A‖) * Δt := by
    have h1 : M = 1 + (exp (Δt • A) - 1) := by rw [hM]; abel
    calc ‖M‖ ≤ ‖(1 : Mat ℝ n n)‖ + ‖exp (Δt • A) - 1‖ := by rw [h1]; exact norm_add_le _ _
      _ ≤ 1 + Δt * ‖A‖ * Real.exp (tEnd * ‖A‖) := by linarith
      _ = 1 + ‖A‖ * Real.exp (tEnd * ‖A‖) * Δt := by ring
  have hEnn : 0 ≤ localAbstrErr E := norm_nonneg _
  calc globalAbstrErr (R (k + 1)) (Rhat (k + 1)) = localAbstrErr E' := hstep1
    _ ≤ ‖M‖ * localAbstrErr E + localAbstrErr (Rabs k) := hbound
    _ ≤ (1 + ‖A‖ * Real.exp (tEnd * ‖A‖) * Δt) * localAbstrErr E + localAbstrErr (Rabs k) := by
        gcongr
    _ = (1 + ‖A‖ * Real.exp (tEnd * ‖A‖) * Δt) * globalAbstrErr (R k) (Rhat k)
        + localAbstrErr (Rabs k) := by rw [hstep2]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
