module

public import CORALean.ContDynamics.LinearSys.Operations.VerifyZonotopeRunFloat
public import CORALean.ContDynamics.LinearSys.Theorems.VerifyTimeSetdiff
public import CORALean.ContDynamics.LinearSys.Theorems.VerifyZonotopePassFloat
public import CORALean.ContDynamics.LinearSys.Theorems.VerifyZonotopeWitnessFloat

@[expose] public section

/-!
# `LinearSys.verifyZonotopeRunFloat` is sound

Verified: a time `t ∈ [0, t_f]` left in no unverified interval of `S` was removed by some step
(`LinearSys.mem_Icc_of_not_mem_verifyTimeSetdiff`, along the removals), a step of a computed
pass whose output set holds `S` at `t`; that set holds every output at `t`
(`LinearSys.verifyZonotopePassFloat_sound`). Falsified: a witness that holds violates its
specification at its time (`LinearSys.verifyZonotopeWitnessFloat_violated`). `none` claims
nothing.

## Inputs
* `sys` – linear system, its `A` the system matrix
* `c` – float center of the initial set
* `G` – float generators of the initial set
* `Bm` – float input matrix
* `uc` – float center of the input set
* `GU` – float generators of the input set
* `C` – float output matrix
* `specs` – float specifications
* `passes` – the grids of the passes
* `witnesses` – candidate falsifications
* `tFinal` – horizon

## Hypotheses
* none

## Conclusion
* `some true`: every specification holds over `[0, t_f]` for every initial point and input;
  `some false`: a specification is violated at a time in `(0, t_f]`
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m k p q : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A time left in no interval after the removals was in one of the removed ones. -/
private theorem LinearSys.aux_chain {t : ℝ} : -- --- CONCL ---
    ∀ (ops U : List (ℚ × ℚ)), (∃ iv ∈ U, (iv.1 : ℝ) ≤ t ∧ t ≤ iv.2) →
      ops.foldl (fun U iv => LinearSys.verifyTimeSetdiff U iv.1 iv.2) U = [] →
      ∃ op ∈ ops, (op.1 : ℝ) ≤ t ∧ t ≤ op.2 := by -- --- PROOF ---
  intro ops
  induction ops with
  | nil =>
    intro U ⟨iv, hiv, _⟩ h
    simp only [List.foldl_nil] at h
    simp [h] at hiv
  | cons op ops ih =>
    intro U hU h
    obtain ⟨iv, hiv, ht⟩ := hU
    by_cases hin : ∃ iv' ∈ LinearSys.verifyTimeSetdiff U op.1 op.2, (iv'.1 : ℝ) ≤ t ∧ t ≤ iv'.2
    · obtain ⟨op', hop', h'⟩ := ih _ hin h
      exact ⟨op', List.mem_cons_of_mem _ hop', h'⟩
    · push Not at hin
      exact ⟨op, List.mem_cons_self, LinearSys.mem_Icc_of_not_mem_verifyTimeSetdiff hiv ht
        fun iv' hiv' h' => absurd h'.2 (not_le.mpr (hin iv' hiv' h'.1))⟩

/-- An interval of a pass on which `S` holds is a step's, from that step's start. -/
private theorem LinearSys.aux_times (S : LinearSys.VerifySpecSet 𝕋 q) : -- --- CONCL ---
    ∀ (grid : List (LinearSys.VerifyGridStep 𝕋))
      (out : List (Option (LinearSys.VerifyZono 𝕋 q × List Bool))) (t₀ : ℚ) (iv : ℚ × ℚ),
      iv ∈ LinearSys.step_verifyRunTimesFloat S grid out t₀ →
      ∃ j g Y fl, grid[j]? = some g ∧ out[j]? = some (some (Y, fl)) ∧
        LinearSys.verifySpecHoldsFloat Y S = true ∧
        (iv.1 : ℝ) = t₀ + ((grid.take j).map fun g => toReal g.Δt).sum ∧
        (iv.2 : ℝ) = iv.1 + toReal g.Δt := by -- --- PROOF ---
  intro grid
  induction grid with
  | nil => intro out t₀ iv h; simp [LinearSys.step_verifyRunTimesFloat] at h
  | cons g gs ih =>
    intro out t₀ iv h
    cases out with
    | nil => simp [LinearSys.step_verifyRunTimesFloat] at h
    | cons o os =>
      simp only [LinearSys.step_verifyRunTimesFloat, List.mem_append] at h
      rcases h with h | h
      · -- this step
        rcases o with _ | ⟨Y, fl⟩
        · simp at h
        · simp only at h
          split_ifs at h with hS
          · simp only [List.mem_singleton] at h
            subst h
            refine ⟨0, g, Y, fl, rfl, rfl, hS, by simp, ?_⟩
            push_cast [ToRat.toReal_toRat]; ring
          · simp at h
      · -- a later step, from `t₀ + Δt`
        obtain ⟨j, g', Y, fl, hg, ho, hS, h1, h2⟩ := ih os _ iv h
        refine ⟨j + 1, g', Y, fl, hg, ho, hS, ?_, h2⟩
        rw [h1]
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
        push_cast [ToRat.toReal_toRat]; ring


-- =======================================  MAIN THEOREM  ======================================= --

set_option maxHeartbeats 400000 in -- the run is unfolded with its `let`s
theorem LinearSys.verifyZonotopeRunFloat_sound (sys : LinearSys 𝕋 n) (c : Vec 𝕋 n)
    (G : Mat 𝕋 n m) (Bm : Mat 𝕋 n k) (uc : Vec 𝕋 k) (GU : Mat 𝕋 k p) (C : Mat 𝕋 q n)
    (specs : List (LinearSys.VerifySpecSet 𝕋 q))
    (passes : List (List (LinearSys.VerifyGridStep 𝕋)))
    (witnesses : List (ℕ × 𝕋 × Vec 𝕋 m × Vec 𝕋 p)) (tFinal : 𝕋) : -- --- CONCL ---
    let U := (fun β => toRealMat Bm *ᵥ (toRealVec uc + toRealMat GU *ᵥ β)) '' Set.Icc (-1) 1
    let x := fun (t : ℝ) (b : Fin m → ℝ) (y : Vec ℝ n) =>
      toRealMat C *ᵥ (exp (t • toRealMat sys.A) *ᵥ (toRealVec c + toRealMat G *ᵥ b) + y)
    ∀ v ∈ LinearSys.verifyZonotopeRunFloat sys.A c G Bm uc GU C specs passes witnesses tFinal,
    (v = true → ∀ S ∈ specs, ∀ t : ℝ, 0 ≤ t → t ≤ toReal tFinal → ∀ b : Fin m → ℝ,
      (∀ j, |b j| ≤ 1) → ∀ y ∈ sys.inputReach (S := ExactSet) U t,
      (S.safe = true → ∀ ab ∈ S.rows, toRealVec ab.1 ⬝ᵥ x t b y < toReal ab.2) ∧
      (S.safe = false → ∃ ab ∈ S.rows, toReal ab.2 < toRealVec ab.1 ⬝ᵥ x t b y)) ∧
    (v = false → ∃ S ∈ specs, ∃ t : ℝ, 0 < t ∧ t ≤ toReal tFinal ∧ ∃ b : Fin m → ℝ,
      (∀ j, |b j| ≤ 1) ∧ ∃ y ∈ sys.inputReach (S := ExactSet) U t,
      (S.safe = true → ∃ ab ∈ S.rows, toReal ab.2 < toRealVec ab.1 ⬝ᵥ x t b y) ∧
      (S.safe = false → ∀ ab ∈ S.rows, toRealVec ab.1 ⬝ᵥ x t b y ≤ toReal ab.2))
    := by -- --- PROOF ---
  intro U x v hv
  replace hv : LinearSys.verifyZonotopeRunFloat sys.A c G Bm uc GU C specs passes witnesses tFinal
    = some v := hv
  unfold LinearSys.verifyZonotopeRunFloat at hv
  dsimp only at hv
  split_ifs at hv with hf hall
  · -- a witness holds
    simp only [Option.some.injEq] at hv
    subst hv
    refine ⟨fun h => absurd h Bool.false_ne_true, fun _ => ?_⟩
    obtain ⟨w, -, hw⟩ := List.any_eq_true.mp hf
    split at hw
    · rename_i S hS
      obtain ⟨hle, hwit⟩ := Bool.and_eq_true _ _ ▸ hw
      obtain ⟨ht, bb, hbb, y, hy, hviol⟩ :=
        LinearSys.verifyZonotopeWitnessFloat_violated sys c G Bm uc GU C S _ _ _ hwit
      exact ⟨S, List.mem_of_getElem? hS, _, ht, toReal_le_of_le hle, bb, hbb, y, hy, hviol⟩
    · exact absurd hw Bool.false_ne_true
  · -- every specification verified on `[0, t_f]`
    simp only [Option.some.injEq] at hv
    subst hv
    refine ⟨fun _ S hS t ht0 ht1 b hb y hy => ?_, fun h => absurd h.symm Bool.false_ne_true⟩
    have hS0 := List.isEmpty_iff.mp (List.all_eq_true.mp hall S hS)
    have hT : ((ToRat.toRat tFinal : ℚ) : ℝ) = toReal tFinal := ToRat.toReal_toRat _
    obtain ⟨op, hop, hin⟩ := LinearSys.aux_chain _ _
      ⟨(0, ToRat.toRat tFinal), List.mem_singleton_self _, by simpa [hT] using ⟨ht0, ht1⟩⟩ hS0
    -- the step of a computed pass that removed `t`
    obtain ⟨go, hgo, hop'⟩ := List.mem_flatMap.mp hop
    obtain ⟨grid, -, hgrid⟩ := List.mem_filterMap.mp hgo
    obtain ⟨out, hout, rfl⟩ := Option.map_eq_some_iff.mp hgrid
    obtain ⟨j, g, Y, fl, hg, ho, hSY, h1, h2⟩ := LinearSys.aux_times S grid out 0 op hop'
    obtain ⟨-, hpass⟩ := LinearSys.verifyZonotopePassFloat_sound sys c G Bm uc GU C specs grid
      out hout
    obtain ⟨-, hY⟩ := hpass j g Y fl hg ho
    simp only [Rat.cast_zero, zero_add] at h1
    obtain ⟨-, hspec⟩ := hY b hb t (by rw [← h1]; exact hin.1)
      (by rw [← h1, ← h2]; exact hin.2) y hy
    exact hspec S hS hSY

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
