module

public import CORALean.ContDynamics.LinearSys.Theorems.AdaptTimeStepBudget
public import CORALean.ContDynamics.LinearSys.Operations.TunedRun
public import CORALean.ContSet.Zonotope.Real.Theorems.AdaptSetOrderBudget

@[expose] public section

/-!
# `Thm. 1`, the error half: a tuned run stays inside its error budget

[1, Thm. 1] claims two things of `Alg. 1`; this is the second, that the overall error stays below
`ε_max = ε_H,max + ε_P,max + ε_S,max`. Proved of the errors eq. (9) and eq. (12) accumulate and of
the `ε_H` of the step last taken, which eq. (2) makes independent of the earlier ones. [1] proves
only that each of the three bounds is *satisfiable*; that the accumulation stays inside is eq.
(10)/(11)'s telescoping, which `aux_tunedStep_le` is. [1]'s "assuming the reduction of the set
representation in each step is optional" is discharged rather than assumed: `param(PR)` reduces
nothing, which is what starts `Alg. 3`'s loop admissible. Two side conditions, neither of them the
claim: the run must reach the step it is read at, and must not step past `t_f`.

## Inputs
* `sys` – linear system
* `le` – comparison oracle on reals
* `X₀` – initial zonotope
* `U` – input zonotope
* `εHmax` – maximal homogeneous error
* `εPmax` – maximal particular error
* `εSmax` – maximal reduction error
* `tf` – final time
* `μ` – shrink factor
* `ηmax` – maximal Taylor order
* `fuel` – number of shrinkings
* `k` – iteration count

## Hypotheses
* `hle` – comparison oracle is sound
* `hn` – dimension positive
* `hμ` – shrink factor positive
* `htf` – final time positive
* `hεPmax` – maximal particular error nonnegative
* `hεSmax` – maximal reduction error nonnegative

## Conclusion
* a run inside the horizon keeps its errors under their maxima

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning for reachability
      analysis of linear systems". 2020 59th IEEE Conference on Decision and Control (CDC), 2020.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Eq. (10)/(11)'s telescoping, at one step: an error grown by a share of what
is left of the budget, proportional to the step, stays under the fraction of
the budget the elapsed time has spent. -/
private theorem aux_tunedStep_le {ε a a' tf ti Δt : ℝ} (htf : 0 < tf)
    (hΔt : 0 < Δt) (hsum : ti + Δt ≤ tf) (ha : a ≤ ε * (ti / tf))
    (ha' : a' ≤ a + (ε - a) / (tf - ti) * Δt) : -- --- CONCL ---
    a' ≤ ε * ((ti + Δt) / tf) := by -- --- PROOF ---
  have hd : 0 < tf - ti := by linarith
  have ham : a * tf ≤ ε * ti := by
    rw [← mul_div_assoc] at ha
    exact (le_div_iff₀ htf).mp ha
  have ha'm : (a' - a) * (tf - ti) ≤ (ε - a) * Δt := by
    have h : a' - a ≤ (ε - a) * Δt / (tf - ti) := by
      have he : (ε - a) / (tf - ti) * Δt = (ε - a) * Δt / (tf - ti) := by ring
      rw [he] at ha'
      linarith
    exact (le_div_iff₀ hd).mp h
  have hgap : 0 ≤ tf - ti - Δt := by linarith
  -- the two bounds, cleared of denominators, add up to exactly the goal
  have h1 : (a' - a) * (tf - ti) * tf ≤ (ε - a) * Δt * tf :=
    mul_le_mul_of_nonneg_right ha'm htf.le
  have h2 : a * tf * (tf - ti - Δt) ≤ ε * ti * (tf - ti - Δt) :=
    mul_le_mul_of_nonneg_right ham hgap
  rw [← mul_div_assoc, le_div_iff₀ htf]
  refine le_of_mul_le_mul_right ?_ hd
  nlinarith [h1, h2]

/-- Every step the sweep of `Alg. 2` can report is the one it came in with,
shrunk by `μ` finitely often, so both being positive leaves it positive. -/
private theorem aux_adaptTimeStepSearch_pos (sys : LinearSys 𝕋 n) (le : ℝ → ℝ → Bool)
    (X₀ U : Zonotope (Vec ℝ n)) (εHmax εPmax εPacc tf ti μ : ℝ) (ηmax : ℕ)
    (hμ : 0 < μ) : -- --- CONCL ---
    ∀ (k : ℕ) (Δt Δti : ℝ) (ηi : ℕ), 0 < Δt →
      LinearSys.adaptTimeStepSearch sys le X₀ U εHmax εPmax εPacc tf ti μ ηmax Δt k
        = some (Δti, ηi) → 0 < Δti := by -- --- PROOF ---
  intro k
  induction k with
  | zero =>
    intro Δt Δti ηi _ h
    rw [LinearSys.adaptTimeStepSearch] at h
    exact absurd h (by simp)
  | succ k ih =>
    intro Δt Δti ηi hΔt h
    simp only [LinearSys.adaptTimeStepSearch] at h
    split at h
    -- an order cleared both bounds at this `Δt`, so this `Δt` is what was reported
    · rw [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hΔt
    · exact ih _ _ _ (mul_pos hΔt hμ) h

/-- The step `Alg. 2` reports is positive, the one it starts from being so. -/
private theorem aux_adaptTimeStep_pos (sys : LinearSys 𝕋 n) (le : ℝ → ℝ → Bool)
    (X₀ U : Zonotope (Vec ℝ n)) (εHmax εPmax εPacc tf ti Δtprev μ : ℝ) (ηmax fuel : ℕ)
    (hμ : 0 < μ) (hΔtprev : 0 < Δtprev) {Δti εP : ℝ} {ηi : ℕ}
    (h : sys.adaptTimeStep le X₀ U εHmax εPmax εPacc tf ti Δtprev μ ηmax fuel
      = some (Δti, ηi, εP)) : -- --- CONCL ---
    0 < Δti := by -- --- PROOF ---
  simp only [LinearSys.adaptTimeStep] at h
  split at h
  · exact absurd h (by simp)
  · rename_i Δt' η' hsw
    rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, -⟩ := h
    exact aux_adaptTimeStepSearch_pos sys le X₀ U εHmax εPmax εPacc tf ti μ ηmax hμ fuel _ _ _
      (div_pos hΔtprev hμ) hsw

/-- The run's invariant: the time only grows, the step stays positive, each
accumulated error stays under the fraction of its budget the elapsed time has
spent, and once a step has been taken its `ε_H` is inside `ε_H,max`. -/
private theorem aux_tunedRun_invariant (sys : LinearSys 𝕋 n) {le : ℝ → ℝ → Bool}
    (hle : ∀ a b, le a b = true → a ≤ b) (hn : 0 < n) (X₀ U : Zonotope (Vec ℝ n))
    {εHmax εPmax εSmax tf μ : ℝ} (hμ : 0 < μ) (htf : 0 < tf)
    (hεSmax : 0 ≤ εSmax) (ηmax fuel : ℕ) : -- --- CONCL ---
    ∀ (k : ℕ), (∀ j ≤ k, ∀ s, sys.tunedRun le X₀ U εHmax εPmax εSmax tf μ ηmax fuel j = some s →
        s.t ≤ tf) →
      ∀ s, sys.tunedRun le X₀ U εHmax εPmax εSmax tf μ ηmax fuel k = some s →
        0 ≤ s.t ∧ 0 < s.Δt ∧ s.εP ≤ εPmax * (s.t / tf) ∧ s.εS ≤ εSmax * (s.t / tf) ∧
          (0 < s.t → sys.timeIntervalStepCurvatureError s.Δt s.η X₀ ≤ εHmax) := by -- --- PROOF ---
  intro k
  induction k with
  | zero =>
    intro _ s h
    rw [LinearSys.tunedRun, Option.some.injEq] at h
    subst h
    dsimp only [LinearSys.aux_tunedInit]
    exact ⟨le_refl 0, mul_pos htf hμ, by simp, by simp, by simp⟩
  | succ k ih =>
    intro hhor s h
    have hst : s.t ≤ tf := hhor (k + 1) (le_refl _) s h
    cases hprev : sys.tunedRun le X₀ U εHmax εPmax εSmax tf μ ηmax fuel k with
    | none => simp [LinearSys.tunedRun, hprev] at h
    | some s₀ =>
      obtain ⟨ht₀, hΔt₀, hP₀, hS₀, hH₀⟩ :=
        ih (fun j hj => hhor j (Nat.le_succ_of_le hj)) s₀ hprev
      have hst₀ : s₀.t ≤ tf := hhor k (Nat.le_succ k) s₀ hprev
      simp only [LinearSys.tunedRun, hprev] at h
      split at h
      -- the horizon is not reached, so line 5 runs
      · rename_i hlt
        simp only [LinearSys.aux_tunedStep] at h
        split at h
        · exact absurd h (by simp)
        · rename_i Δt η εP hA2
          rw [Option.some.injEq] at h
          subst h
          dsimp only at hst ⊢
          have hΔt : 0 < Δt :=
            aux_adaptTimeStep_pos sys le X₀ U εHmax εPmax s₀.εP tf s₀.t s₀.Δt μ ηmax fuel
              hμ hΔt₀ hA2
          obtain ⟨hH, hP, hPacc⟩ := LinearSys.adaptTimeStep_budget sys hle X₀ U εHmax εPmax
            s₀.εP tf s₀.t s₀.Δt μ ηmax fuel _ _ _ hA2
          -- the `ε_S` share is nonnegative, so `Alg. 3`'s loop starts admissible
          have hεS₀ : s₀.εS ≤ εSmax := by
            have hfrac : s₀.t / tf ≤ 1 := div_le_one_of_le₀ hst₀ htf.le
            nlinarith [hS₀, mul_le_mul_of_nonneg_left hfrac hεSmax]
          have hSbudget : 0 ≤ (εSmax - s₀.εS) / (tf - s₀.t) * Δt :=
            mul_nonneg (div_nonneg (by linarith) (by linarith)) hΔt.le
          have hSgen : ∀ Z : Zonotope (Vec ℝ n),
              (Z.adaptSetOrder le εSmax s₀.εS tf s₀.t Δt).2
                ≤ s₀.εS + (εSmax - s₀.εS) / (tf - s₀.t) * Δt := by
            intro Z
            obtain ⟨h1, h2⟩ := Zonotope.adaptSetOrder_budget hle Z hn hSbudget
            rw [h2]
            linarith
          refine ⟨by linarith, hΔt, ?_, ?_, fun _ => hH⟩
          · exact aux_tunedStep_le htf hΔt hst hP₀ (by rw [hPacc]; linarith)
          · exact aux_tunedStep_le htf hΔt hst hS₀ (hSgen _)
      -- the horizon is reached, and the state stands still
      · rw [Option.some.injEq] at h
        subst h
        exact ⟨ht₀, hΔt₀, hP₀, hS₀, hH₀⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1], the error half: a run that stays inside the horizon keeps
`ε_P([0,t_i])` under `ε_P,max`, `ε_S([0,t_i])` under `ε_S,max`, and the `ε_H` of
the step last taken under `ε_H,max`. -/
theorem LinearSys.tunedRun_error_le (sys : LinearSys 𝕋 n) {le : ℝ → ℝ → Bool}
    (hle : ∀ a b, le a b = true → a ≤ b) (hn : 0 < n) (X₀ U : Zonotope (Vec ℝ n))
    {εHmax εPmax εSmax tf μ : ℝ} (hμ : 0 < μ) (htf : 0 < tf) (hεPmax : 0 ≤ εPmax)
    (hεSmax : 0 ≤ εSmax) (ηmax fuel k : ℕ) : -- --- CONCL ---
    ∀ s ∈ sys.tunedRun le X₀ U εHmax εPmax εSmax tf μ ηmax fuel k,
      (∀ j ≤ k, ∀ s, sys.tunedRun le X₀ U εHmax εPmax εSmax tf μ ηmax fuel j = some s → s.t ≤ tf) →
      s.εP ≤ εPmax ∧ s.εS ≤ εSmax ∧
        (0 < s.t → sys.timeIntervalStepCurvatureError s.Δt s.η X₀ ≤ εHmax) := by -- --- PROOF ---
  intro s (h : sys.tunedRun le X₀ U εHmax εPmax εSmax tf μ ηmax fuel k = some s) hhor
  obtain ⟨ht, -, hP, hS, hH⟩ :=
    aux_tunedRun_invariant sys hle hn X₀ U hμ htf hεSmax ηmax fuel k hhor s h
  have hfrac : s.t / tf ≤ 1 := div_le_one_of_le₀ (hhor k (le_refl _) s h) htf.le
  refine ⟨?_, ?_, hH⟩
  · calc s.εP ≤ εPmax * (s.t / tf) := hP
      _ ≤ εPmax * 1 := by exact mul_le_mul_of_nonneg_left hfrac hεPmax
      _ = εPmax := mul_one _
  · calc s.εS ≤ εSmax * (s.t / tf) := hS
      _ ≤ εSmax * 1 := by exact mul_le_mul_of_nonneg_left hfrac hεSmax
      _ = εSmax := mul_one _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
