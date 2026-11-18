module

public import CORALean.ContDynamics.LinearSys.Theorems.VerifyZonotopePassFloatStep
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachImageAdd
public import CORALean.ContDynamics.LinearSys.Theorems.VerifySpecHoldsFloat

@[expose] public section

/-!
# `LinearSys.verifyZonotopePassFloat` is sound

A step computed in full returns an output set holding `C x(t)` over the step, for every
`x₀ ∈ ⟨c, G⟩` and every input `u(s) ∈ B(u_c + G_U [-1, 1]^k)`: the invariant
`LinearSys.IsVerifyZonoInvariant` holds at `t = 0` and each step keeps it
(`LinearSys.verifyZonotopePassFloat_step`). A flag `true` proves its specification over the step
(`LinearSys.verifySpecHoldsFloat_sound`); a flag `false` claims nothing: no certificate, the step
is undecided and refined, never read as disjoint. The grid is CORA's tuning, an unchecked input.

## Inputs
* `sys` – linear system, its `A` the system matrix
* `c` – float center of the initial set
* `G` – float generators of the initial set
* `Bm` – float input matrix
* `uc` – float center of the input set
* `GU` – float generators of the input set
* `C` – float output matrix
* `specs` – float specifications
* `grid` – the steps

## Hypotheses
* none

## Conclusion
* a returned pass has one output per step; a step's output set holds every output over the step,
  and every flag `true` proves its specification there
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

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m k p q : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- What a step's output promises, from the start `t₀` of the step. -/
private def LinearSys.aux_stepOk (sys : LinearSys 𝕋 n) (c₀ : Vec ℝ n) (G₀ : Mat ℝ n m)
    (u0v : Vec ℝ n) (V : Set (Vec ℝ n)) (C : Mat 𝕋 q n) (specs : List (LinearSys.VerifySpecSet 𝕋 q))
    (t₀ : ℝ) (g : LinearSys.VerifyGridStep 𝕋) (o : Option (LinearSys.VerifyZono 𝕋 q × List Bool)) :
    Prop :=
  0 ≤ t₀ ∧ ∀ Y fl, o = some (Y, fl) → fl = specs.map (LinearSys.verifySpecHoldsFloat Y) ∧
    ∀ b : Fin m → ℝ, (∀ j, |b j| ≤ 1) → ∀ τ : ℝ, 0 ≤ τ → τ ≤ toReal g.Δt →
    ∀ y ∈ sys.inputReach (S := ExactSet) V (t₀ + τ),
      toRealMat C *ᵥ (exp ((t₀ + τ) • toRealMat sys.A) *ᵥ (c₀ + G₀ *ᵥ b)
        + Real.MatExp.expIntegral (toRealMat sys.A) (t₀ + τ) *ᵥ u0v + y) ∈ Y.toSet

/-- The steps from an enclosing state: the outputs after `acc`, one per step, each as promised
from the step's start. -/
private theorem LinearSys.aux_steps (sys : LinearSys 𝕋 n) {s : Vec 𝕋 n}
    (hs : ∀ i, 0 < toReal (s i)) {u₀ : Interval (Mat 𝕋 n 1)} {MU : Interval (Mat 𝕋 n p)}
    {u0r : Mat ℝ n 1} (hu : u0r ∈ u₀.toSet) {Mr : Mat ℝ n p} (hM : Mr ∈ MU.toSet)
    (C : Mat 𝕋 q n) (specs : List (LinearSys.VerifySpecSet 𝕋 q)) (c₀ : Vec ℝ n)
    (G₀ : Mat ℝ n m) : -- --- CONCL ---
    ∀ (grid : List (LinearSys.VerifyGridStep 𝕋)) (st : LinearSys.VerifyZonoState 𝕋 n m)
      (acc : List (Option (LinearSys.VerifyZono 𝕋 q × List Bool))) (t : ℝ)
      (out : List (Option (LinearSys.VerifyZono 𝕋 q × List Bool))),
      sys.IsVerifyZonoInvariant (toRealVec s) c₀ G₀ (fun l => u0r l 0)
        ((fun β => Mr *ᵥ β) '' Set.Icc (-1) 1) t st →
      LinearSys.step_verifyZonoStepsFloat sys.A s u₀ MU C specs st grid acc = some out →
      ∃ outs, out = acc.reverse ++ outs ∧ outs.length = grid.length ∧
        ∀ j g o, grid[j]? = some g → outs[j]? = some o →
          sys.aux_stepOk c₀ G₀ (fun l => u0r l 0) ((fun β => Mr *ᵥ β) '' Set.Icc (-1) 1) C specs
            (t + ((grid.take j).map fun g => toReal g.Δt).sum) g o := by -- --- PROOF ---
  intro grid
  induction grid with
  | nil =>
    intro st acc t out _ h
    simp only [LinearSys.step_verifyZonoStepsFloat, Option.some.injEq] at h
    exact ⟨[], by simp [h], rfl, fun j g o hg => by simp at hg⟩
  | cons g gs ih =>
    intro st acc t out hinv h
    simp only [LinearSys.step_verifyZonoStepsFloat] at h
    split at h
    · simp at h
    rename_i o st' hstep
    -- the step keeps the invariant, the rest of the grid gives the later outputs
    obtain ⟨-, hinv', hok⟩ := LinearSys.verifyZonotopePassFloat_step sys hs hu hM C specs hinv g
      (o, st') hstep
    obtain ⟨outs, rfl, hlen, hall⟩ := ih st' (o :: acc) (t + toReal g.Δt) out hinv' h
    refine ⟨o :: outs, by simp, by simp [hlen], fun j g' o' hg ho => ?_⟩
    -- this step's output, then the later ones from `t + Δt`
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hg ho
      subst hg ho
      simpa using ⟨hinv.1, hok⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at hg ho
      have := hall j g' o' hg ho
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
      rwa [← add_assoc]

/-- Over an empty window nothing is contributed. -/
private theorem LinearSys.aux_inputReach_zero (sys : LinearSys 𝕋 n) {V : Set (Vec ℝ n)}
    {y : Vec ℝ n} (hy : y ∈ sys.inputReach (S := ExactSet) V 0) : y = 0 := by
  obtain ⟨u, -, -, rfl⟩ := hy
  simp


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every step of the pass computed in full holds every output over the step, and every flag
`true` proves its specification there; a flag `false` claims nothing (no Farkas certificate: the
step is undecided and refined, never read as disjoint). The grid is CORA's tuning, not checked. -/
theorem LinearSys.verifyZonotopePassFloat_sound (sys : LinearSys 𝕋 n) (c : Vec 𝕋 n)
    (G : Mat 𝕋 n m) (Bm : Mat 𝕋 n k) (uc : Vec 𝕋 k) (GU : Mat 𝕋 k p) (C : Mat 𝕋 q n)
    (specs : List (LinearSys.VerifySpecSet 𝕋 q))
    (grid : List (LinearSys.VerifyGridStep 𝕋)) : -- --- CONCL ---
    let U := (fun β => toRealMat Bm *ᵥ (toRealVec uc + toRealMat GU *ᵥ β)) '' Set.Icc (-1) 1
    ∀ out ∈ LinearSys.verifyZonotopePassFloat sys.A c G Bm uc GU C specs grid,
    out.length = grid.length ∧
    ∀ j g Y fl, grid[j]? = some g → out[j]? = some (some (Y, fl)) →
      let t₀ := ((grid.take j).map fun g => toReal g.Δt).sum
      fl = specs.map (LinearSys.verifySpecHoldsFloat Y) ∧
      ∀ b : Fin m → ℝ, (∀ j, |b j| ≤ 1) → ∀ t : ℝ, t₀ ≤ t → t ≤ t₀ + toReal g.Δt →
      ∀ y ∈ sys.inputReach (S := ExactSet) U t,
        let x := exp (t • toRealMat sys.A) *ᵥ (toRealVec c + toRealMat G *ᵥ b) + y
        toRealMat C *ᵥ x ∈ Y.toSet ∧ ∀ S ∈ specs, LinearSys.verifySpecHoldsFloat Y S = true →
          (S.safe = true → ∀ ab ∈ S.rows, toRealVec ab.1 ⬝ᵥ (toRealMat C *ᵥ x) < toReal ab.2) ∧
          (S.safe = false → ∃ ab ∈ S.rows, toReal ab.2 < toRealVec ab.1 ⬝ᵥ (toRealMat C *ᵥ x))
    := by -- --- PROOF ---
  intro U out h
  replace h : LinearSys.verifyZonotopePassFloat sys.A c G Bm uc GU C specs grid = some out := h
  -- the input in state space: `B u_c` and `B G_U`, each in its bracket
  set u0r : Mat ℝ n 1 := fun l _ => (toRealMat Bm *ᵥ toRealVec uc) l with hu0r
  set Mr : Mat ℝ n p := toRealMat Bm * toRealMat GU with hMr
  set V := (fun β => Mr *ᵥ β) '' Set.Icc (-1) 1 with hV
  have hbdd : Bornology.IsBounded V :=
    (isCompact_Icc.image (Matrix.mulVecLin Mr).continuous_of_finiteDimensional).isBounded
  have hUeq : U = (fun z => (fun l => u0r l 0) + z) '' V := by
    simp only [U, hV, Set.image_image]
    refine Set.image_congr fun β _ => ?_
    rw [Matrix.mulVec_add, hMr, ← Matrix.mulVec_mulVec]
  have hu : u0r ∈ (⟨matMulDown Bm fun j _ => uc j, matMulUp Bm fun j _ => uc j⟩ :
      Interval (Mat 𝕋 n 1)).materialiseMat.toSet := by
    rw [Interval.materialiseMat_eq]
    exact Interval.mem_mat_iff.mpr fun l c => ⟨dotDown_le (Bm l) fun j => uc j,
      le_dotUp (Bm l) fun j => uc j⟩
  have hM : Mr ∈ (⟨matMulDown Bm GU, matMulUp Bm GU⟩ : Interval (Mat 𝕋 n p)).materialiseMat.toSet
      := by
    rw [Interval.materialiseMat_eq]
    exact Interval.mem_mat_iff.mpr fun l c => ⟨dotDown_le (Bm l) fun j => GU j c,
      le_dotUp (Bm l) fun j => GU j c⟩
  -- the pass: positive scales, then the steps from `t = 0`
  unfold LinearSys.verifyZonotopePassFloat at h
  dsimp only at h
  split_ifs at h with hsc
  have hsc' : ∀ i, ltStrict FloatOps.zero (MatExp.balanceScalesFloat sys.A i) = true := by
    simpa using hsc
  set s := MatExp.balanceScalesFloat sys.A
  have hs : ∀ i, 0 < toReal (s i) := fun i => by
    have := toReal_lt_of_ltStrict (hsc' i)
    rwa [toReal_zero] at this
  have hinv0 : sys.IsVerifyZonoInvariant (toRealVec s) (toRealVec c) (toRealMat G)
      (fun l => u0r l 0) V 0 ⟨c, G, zero, fun i j => if i = j then one else zero, zero, [],
        fun _ => zero, zero⟩ := by
    have hI : toRealMat (fun (i j : Fin n) => if i = j then (one : 𝕋) else zero) = 1 := by
      ext p q
      simp only [toRealMat, Matrix.one_apply]
      split_ifs <;> simp [toReal_zero, toReal_one]
    have hΓ0 : Real.MatExp.expIntegral (toRealMat sys.A) 0 = 0 := by
      simp [Real.MatExp.expIntegral]
    -- at `t = 0`: no error, `Φ = I`, nothing contributed
    refine ⟨le_rfl, by simp [toReal_zero], by simp [toReal_zero], by simp [toReal_zero],
      fun b _ i => ?_, fun a ha x _ i => ?_, fun y hy => ?_⟩
    · simp [hΓ0, toReal_zero]
    · simp only [hI, zero_smul, exp_zero, sub_self, Matrix.zero_mulVec, Pi.zero_apply, abs_zero,
        toReal_zero, zero_mul, le_refl]
    · rw [LinearSys.aux_inputReach_zero sys hy]
      exact ⟨0, rfl, 0, 0, fun i => by simp [toReal_zero], fun i => by simp [toReal_zero],
        by simp⟩
  -- every step of the grid as promised, from its start
  obtain ⟨outs, hout, hlen, hall⟩ := LinearSys.aux_steps sys hs hu hM C specs (toRealVec c)
    (toRealMat G) grid _ [] 0 out hinv0 h
  simp only [List.reverse_nil, List.nil_append] at hout
  subst hout
  refine ⟨hlen, fun j g Y fl hg ho => ?_⟩
  intro t₀
  obtain ⟨ht₀, hok⟩ := hall j g _ hg ho
  obtain ⟨hfl, hY⟩ := hok Y fl rfl
  simp only [zero_add] at ht₀ hY
  refine ⟨hfl, fun b hb t ht0 ht1 y hy => ?_⟩
  intro x
  -- the constant input's part and the varying part
  have ht : 0 ≤ t := le_trans ht₀ ht0
  rw [hUeq, sys.inputReach_image_add hbdd ht] at hy
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  have hτ := hY b hb (t - t₀) (by linarith) (by linarith)
  rw [add_sub_cancel] at hτ
  -- the output set, then the specifications
  have hx : toRealMat C *ᵥ x ∈ Y.toSet := by
    have hxeq : x = exp (t • toRealMat sys.A) *ᵥ (toRealVec c + toRealMat G *ᵥ b)
        + Real.MatExp.expIntegral (toRealMat sys.A) t *ᵥ (fun l => u0r l 0) + y₀ := by
      simp only [x]
      rw [add_assoc]
      congr 1
    rw [hxeq]
    exact hτ y₀ hy₀
  refine ⟨hx, fun S _ hS => ?_⟩
  obtain ⟨h1, h2⟩ := LinearSys.verifySpecHoldsFloat_sound hS
  exact ⟨fun hs => h1 hs _ hx, fun hs => h2 hs _ hx⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
