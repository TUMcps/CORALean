module

public import CORALean.ContDynamics.LinearSys.Operations.VerifySupportFuncFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.LogNormUpFloat
public import CORALean.ContDynamics.LinearSys.Theorems.VerifySupportPassFloat
public import CORALean.ContDynamics.LinearSys.Theorems.VerifyTimeSetdiff
public import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint

@[expose] public section

/-!
# `LinearSys.verifySupportFuncFloat` is sound

A verdict `true` holds `(C_s C e^{tA} x)_q < d_q` for every row `q`, time `t ∈ [0, t_f]` and point
`x` of `X₀ = c + G [-1, 1]^m`; a verdict `false` comes with a time `t ∈ [0, t_f]` and a row `q`
that a point of `X₀` violates there. The passes keep the unverified times `U`: every time of
`[0, t_f]` outside them holds every row (`LinearSys.mem_Icc_of_not_mem_verifyTimeSetdiff`), and a
pass removes only steps it verified (`LinearSys.verifySupportPassFloat_sound`, whose hypotheses the
run constants meet: the balanced scales, the log norm `μ`
(`MatExp.norm_scaleConj_exp_le_logNormUpFloat`), and the bracket of `C_s C`).

## Inputs
* `A` – float system matrix
* `c` – float center of the initial set
* `G` – float generators of the initial set
* `Cs` – float specification rows
* `Cm` – float output matrix
* `d` – float offsets
* `tFinal` – horizon
* `minStep` – smallest step
* `fuel` – passes at most

## Hypotheses
* `htf` – the horizon is nonnegative

## Conclusion
* verified: every row holds over `[0, t_f]` for all of `X₀`; falsified: a point of `X₀` violates
  the returned row at the returned time
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m p r : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A time in no interval of the fold over the flags is in none of `W` or in a flagged step. -/
private theorem LinearSys.aux_fold (Δt : ℚ) (q : Fin r) (t : ℝ) : -- --- CONCL ---
    ∀ (l : List ((Fin r → Bool) × ℕ)) (W : List (ℚ × ℚ)),
    (∀ iv ∈ l.foldl (fun W f => if f.1 q then LinearSys.verifyTimeSetdiff W (f.2 * Δt)
        ((f.2 + 1) * Δt) else W) W, ¬((iv.1 : ℝ) ≤ t ∧ t ≤ iv.2)) →
    (∀ iv ∈ W, ¬((iv.1 : ℝ) ≤ t ∧ t ≤ iv.2)) ∨ ∃ f ∈ l, f.1 q = true ∧
      (((f.2 * Δt : ℚ)) : ℝ) ≤ t ∧ t ≤ (((f.2 + 1) * Δt : ℚ) : ℝ) := by -- --- PROOF ---
  intro l
  induction l with
  | nil => intro W h; exact Or.inl h
  | cons f l ih =>
    intro W h
    rcases ih _ h with h' | ⟨f', hf', hq, ht⟩
    · by_cases hfq : f.1 q = true
      · simp only [hfq, if_true] at h'
        by_cases hin : ∃ iv ∈ W, (iv.1 : ℝ) ≤ t ∧ t ≤ iv.2
        · obtain ⟨iv, hiv, ht⟩ := hin
          exact Or.inr ⟨f, List.mem_cons_self, hfq,
            LinearSys.mem_Icc_of_not_mem_verifyTimeSetdiff hiv ht h'⟩
        · push Not at hin
          exact Or.inl fun iv hiv h => absurd h.2 (not_le.mpr (hin iv hiv h.1))
      · simp only [hfq, Bool.false_eq_true, if_false] at h'
        exact Or.inl h'
    · exact Or.inr ⟨f', List.mem_cons_of_mem _ hf', hq, ht⟩

/-- The passes: what a verdict claims holds as long as every time outside `U` holds every row. -/
private theorem LinearSys.aux_loop (A : Mat 𝕋 n n) {s c : Vec 𝕋 n} {G : Mat 𝕋 n m}
    {v : Vec 𝕋 n} {βX μ : 𝕋} {ℓ₀ : Mat 𝕋 r n} {E₀ d : Vec 𝕋 r} {T : ℚ} {minStep : 𝕋}
    {Lr : Fin r → Vec ℝ n} (hs : ∀ i, 0 < toReal (s i))
    (hv : ∀ i, |toReal (c i)| + ∑ j, |toReal (G i j)| ≤ toReal (v i)) (hβX0 : 0 ≤ toReal βX)
    (hβX : ∀ i, toReal (v i) ≤ toReal βX * toReal (s i))
    (hμ : ∀ t : ℝ, 0 ≤ t →
      ‖Real.MatExp.scaleConj (toRealVec s) (exp (t • toRealMat A))‖ ≤ Real.exp (t * toReal μ))
    (hE₀ : ∀ q, ∑ i, |Lr q i - toReal (ℓ₀ q i)| * toReal (s i) ≤ toReal (E₀ q)) : -- --- CONCL ---
    ∀ fuel Δt (U : Fin r → List (ℚ × ℚ)) tf it,
    (∀ q (t : ℝ), 0 ≤ t → t ≤ T → (∀ iv ∈ U q, ¬((iv.1 : ℝ) ≤ t ∧ t ≤ iv.2)) →
      ∀ b : Fin m → ℝ, (∀ j, |b j| ≤ 1) →
      Lr q ⬝ᵥ (exp (t • toRealMat A) *ᵥ (toRealVec c + toRealMat G *ᵥ b)) < toReal (d q)) →
    ∀ R, R = LinearSys.step_verifySupportLoop A s c G v βX μ ℓ₀ E₀ d T minStep fuel Δt U tf it →
    (R.verdict = some true → ∀ q (t : ℝ), 0 ≤ t → t ≤ T → ∀ b : Fin m → ℝ, (∀ j, |b j| ≤ 1) →
      Lr q ⬝ᵥ (exp (t • toRealMat A) *ᵥ (toRealVec c + toRealMat G *ᵥ b)) < toReal (d q))
    ∧ (R.verdict = some false → ∃ t q, R.falsification = some (t, q) ∧ 0 ≤ t ∧ t ≤ T ∧
      ∃ b : Fin m → ℝ, (∀ j, |b j| ≤ 1) ∧
      toReal (d q) < Lr q ⬝ᵥ (exp ((t : ℝ) • toRealMat A) *ᵥ (toRealVec c + toRealMat G *ᵥ b)))
    := by -- --- PROOF ---
  intro fuel
  induction fuel with
  | zero => intro Δt U tf it _ R hR; subst hR; simp [LinearSys.step_verifySupportLoop]
  | succ fuel ih =>
    intro Δt U tf it hU R hR
    subst hR
    have hpass := LinearSys.verifySupportPassFloat_sound A (Δt := Δt) (N := ⌈tf / ToRat.toRat Δt⌉₊)
      (T := T) (d := d) hs hv hβX0 hβX hμ hE₀
    -- one pass, by its outcome: not converged, no bound, falsified, decided
    rw [LinearSys.step_verifySupportLoop]
    dsimp only
    split
    · next h => exact ih _ U tf _ hU _ rfl
    · simp
    -- a falsifying step: its time as a rational
    · next k q h =>
      obtain ⟨hT, h0, b, hb, hviol⟩ := hpass.2 k q h
      refine ⟨by simp, fun _ => ⟨_, q, rfl, h0, hT, b, hb, ?_⟩⟩
      have hc : (((k : ℚ) * ToRat.toRat Δt : ℚ) : ℝ) = (k : ℝ) * toReal Δt := by
        push_cast; rw [ToRat.toReal_toRat]
      rw [hc]; exact hviol
    · next fl h =>
      obtain ⟨_, hfl⟩ := hpass.1 fl h
      -- every time outside the new `U` holds every row
      have hU' : ∀ q (t : ℝ), 0 ≤ t → t ≤ T →
          (∀ iv ∈ LinearSys.step_verifySupportUnsat (ToRat.toRat Δt) fl U q,
            ¬((iv.1 : ℝ) ≤ t ∧ t ≤ iv.2)) →
          ∀ b : Fin m → ℝ, (∀ j, |b j| ≤ 1) →
          Lr q ⬝ᵥ (exp (t • toRealMat A) *ᵥ (toRealVec c + toRealMat G *ᵥ b)) < toReal (d q) := by
        intro q t ht0 htT hnot b hb
        simp only [LinearSys.step_verifySupportUnsat, Vector.getElem_ofFn] at hnot
        rcases LinearSys.aux_fold _ q t _ _ hnot with hW | ⟨f, hf, hq, ht1, ht2⟩
        · exact hU q t ht0 htT hW b hb
        -- a flagged step holds the row by the pass's soundness
        · obtain ⟨hi, hfi⟩ := List.mem_zipIdx' (x := f.1) (i := f.2) hf
          have hc : ∀ j : ℕ, (((j : ℚ) * ToRat.toRat Δt : ℚ) : ℝ) = (j : ℝ) * toReal Δt := by
            intro j; push_cast; rw [ToRat.toReal_toRat]
          have hc1 : ((((f.2 : ℚ) + 1) * ToRat.toRat Δt : ℚ) : ℝ) = ((f.2 : ℝ) + 1) * toReal Δt :=
            by push_cast; rw [ToRat.toReal_toRat]
          rw [hc] at ht1
          rw [hc1] at ht2
          exact hfl f.2 hi q (hfi ▸ hq) t ht1 ht2 b hb
      -- all rows verified, the step too small, or the next pass
      split_ifs with hall hmin
      · refine ⟨fun _ q t ht0 htT b hb => hU' q t ht0 htT ?_ b hb, by simp⟩
        have := List.all_eq_true.mp hall q (List.mem_finRange q)
        rw [List.isEmpty_iff] at this
        simp [this]
      · simp
      · exact ih _ _ _ _ hU' _ rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.verifySupportFuncFloat_sound (A : Mat 𝕋 n n) (c : Vec 𝕋 n) (G : Mat 𝕋 n m)
    (Cs : Mat 𝕋 r p) (Cm : Mat 𝕋 p n) (d : Vec 𝕋 r) {tFinal : 𝕋} (minStep : 𝕋) (fuel : ℕ)
    (htf : 0 ≤ toReal tFinal) : -- --- CONCL ---
    ((LinearSys.verifySupportFuncFloat A c G Cs Cm d tFinal minStep fuel).verdict = some true →
      ∀ q (t : ℝ), 0 ≤ t → t ≤ toReal tFinal → ∀ b : Fin m → ℝ, (∀ j, |b j| ≤ 1) →
      ((toRealMat Cs * toRealMat Cm) *ᵥ (exp (t • toRealMat A) *ᵥ
        (toRealVec c + toRealMat G *ᵥ b))) q < toReal (d q))
    ∧ ((LinearSys.verifySupportFuncFloat A c G Cs Cm d tFinal minStep fuel).verdict = some false →
      ∃ t q, (LinearSys.verifySupportFuncFloat A c G Cs Cm d tFinal minStep fuel).falsification
        = some (t, q) ∧ 0 ≤ t ∧ t ≤ ToRat.toRat tFinal ∧ ∃ b : Fin m → ℝ, (∀ j, |b j| ≤ 1) ∧
      toReal (d q) < ((toRealMat Cs * toRealMat Cm) *ᵥ (exp ((t : ℝ) • toRealMat A) *ᵥ
        (toRealVec c + toRealMat G *ᵥ b))) q) := by -- --- PROOF ---
  set Lr : Fin r → Vec ℝ n := fun q i => (toRealMat Cs * toRealMat Cm) q i
  have hLr : ∀ q (y : Vec ℝ n), ((toRealMat Cs * toRealMat Cm) *ᵥ y) q = Lr q ⬝ᵥ y :=
    fun _ _ => rfl
  simp only [hLr]
  have hT : ((ToRat.toRat tFinal : ℚ) : ℝ) = toReal tFinal := ToRat.toReal_toRat _
  -- the run constants, named as the definition names them
  unfold LinearSys.verifySupportFuncFloat
  dsimp only
  simp only [Interval.materialiseMat_eq, Interval.materialise_eq, Interval.point]
  set s := MatExp.balanceScalesFloat A
  set v : Vec 𝕋 n := fun i => addUp (absolute (c i)) (sumUp fun j => absolute (G i j))
  set βX := maximum FloatOps.zero (maximumOver fun i => divUp (v i) (s i))
  set L := Interval.matMul (Interval.point Cs) (Interval.point Cm)
  set E₀ : Vec 𝕋 r := fun q => sumUp fun j => mulUp (subUp (L.sup q j) (L.inf q j)) (s j)
  split_ifs with hsc
  · simp
  -- past the check of the scales: they are positive
  have hs : ∀ i, 0 < toReal (s i) := by
    intro i
    simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true, List.mem_finRange,
      forall_const] at hsc
    have := toReal_lt_of_ltStrict (hsc i)
    rwa [toReal_zero] at this
  -- the run constants meet the pass's hypotheses
  have hv : ∀ i, |toReal (c i)| + ∑ j, |toReal (G i j)| ≤ toReal (v i) := by
    intro i
    have h1 := add_le_addUp (absolute (c i)) (sumUp fun j => absolute (G i j))
    have h2 := sum_le_sumUp (fun j => absolute (G i j))
    simp only [toReal_absolute] at h1 h2
    show _ ≤ toReal (addUp (absolute (c i)) (sumUp fun j => absolute (G i j)))
    linarith
  have hβX0 : 0 ≤ toReal βX := by
    rw [toReal_maximum, toReal_zero]; exact le_max_left _ _
  have hβX : ∀ i, toReal (v i) ≤ toReal βX * toReal (s i) := by
    intro i
    have hdiv := div_le_divUp (v i) (s i) (hs i)
    rw [div_le_iff₀ (hs i)] at hdiv
    refine le_trans hdiv (mul_le_mul_of_nonneg_right ?_ (hs i).le)
    rw [toReal_maximum]
    exact le_trans (le_maximumOver (fun i => divUp (v i) (s i)) i) (le_max_right _ _)
  -- the growth rate, and the rows' bracket with its error
  have hμ := fun t (ht : (0 : ℝ) ≤ t) => MatExp.norm_scaleConj_exp_le_logNormUpFloat A hs ht
  have hL : toRealMat Cs * toRealMat Cm ∈ L.toSet :=
    Interval.matMul_outer _ _ (Interval.mem_point Cs) (Interval.mem_point Cm)
  have hE₀ : ∀ q, ∑ i, |Lr q i - toReal (L.sup q i)| * toReal (s i) ≤ toReal (E₀ q) := by
    intro q
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) (sum_le_sumUp _)
    obtain ⟨hlo, hhi⟩ := Interval.mem_mat_iff.mp hL q i
    have h1 := sub_le_subUp (L.sup q i) (L.inf q i)
    refine le_trans (mul_le_mul_of_nonneg_right ?_ (hs i).le) (mul_le_mulUp _ _)
    rw [abs_sub_comm, abs_of_nonneg (by simp only [Lr]; linarith)]
    simp only [Lr]; linarith
  have hloop := LinearSys.aux_loop A hs hv hβX0 hβX hμ hE₀ (minStep := minStep)
    (T := ToRat.toRat tFinal) (d := d)
  split
  · -- `X₀` itself violates a row
    next q hfind =>
    refine ⟨by simp, fun _ => ⟨0, q, rfl, le_rfl, ?_, ?_⟩⟩
    · rw [← hT] at htf
      exact_mod_cast htf
    · have hlow := List.find?_some hfind
      have hpos : 0 < toReal (subDown (LinearSys.verifySupportDownFloat c G βX (L.sup q) (E₀ q))
          (d q)) := by
        have := toReal_lt_of_ltStrict hlow
        rwa [toReal_zero] at this
      have hβ : ∀ i, |toReal (c i)| + ∑ j, |toReal (G i j)| ≤ toReal βX * toReal (s i) :=
        fun i => le_trans (hv i) (hβX i)
      obtain ⟨b, hb, hle⟩ := LinearSys.exists_le_dotProduct_verifySupportDownFloat c G hβX0 hβ
        (L.sup q) (hE₀ q)
      have hsub := subDown_le_sub (LinearSys.verifySupportDownFloat c G βX (L.sup q) (E₀ q)) (d q)
      refine ⟨b, hb, ?_⟩
      rw [Rat.cast_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec]
      linarith
  · -- the passes from `U = [0, t_f]`
    obtain ⟨h1, h2⟩ := hloop fuel _ (fun _ => [(0, ToRat.toRat tFinal)]) (ToRat.toRat tFinal) 0
      (fun q t ht0 htT hnot => (hnot _ List.mem_cons_self
        ⟨by simpa using ht0, by simpa using htT⟩).elim) _ rfl
    exact ⟨fun h q t ht0 htT => h1 h q t ht0 (hT ▸ htT), h2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
