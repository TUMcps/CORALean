module

public import CORALean.ContDynamics.LinearSys.Operations.AdaptTimeStep

@[expose] public section

/-!
# What `Alg. 2` returns is inside the budgets it searched for

The soundness of [1, Alg. 2] as written here: a step it *reports* meets both of line 12's bounds
(`ε_H` under `ε_H,max`, and `ε_P` under eq. (10)'s share of what is left of the `ε_P` budget, read
at the step actually returned) and the third component is eq. (9)'s accumulation. One hypothesis, on
the caller's check: `le a b = true` implies `a ≤ b`. Nothing asks the converse, so a check that
gives up early loses steps and never reports a wrong one, which is why the search returns an
`Option`. Both sweeps are proved by induction on their own fuel; nothing here needs the search to
terminate.

## Inputs
* `sys` – linear system
* `le` – comparison oracle on reals
* `X₀` – initial zonotope
* `U` – input zonotope
* `εHmax` – maximal homogeneous error
* `εPmax` – maximal particular error
* `εPacc` – accumulated particular error
* `tf` – final time
* `ti` – step start time
* `Δtprev` – previous step length
* `μ` – shrink factor
* `ηmax` – maximal Taylor order
* `fuel` – number of shrinkings

## Hypotheses
* `hle` – comparison oracle is sound

## Conclusion
* a reported step meets both error budgets and the accumulated error is as stated

## References

* [1] [M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning for reachability
      analysis of linear systems". 2020 59th IEEE Conference on Decision and Control (CDC),
      2020.](../../../../../references/2020/wetzlinger-cdc-adaptive-tuning.md)
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

/-- The order sweep reports only orders its own check cleared. -/
private theorem aux_adaptTimeStepOrder_budget (sys : LinearSys 𝕋 n) {le : ℝ → ℝ → Bool}
    (hle : ∀ a b, le a b = true → a ≤ b) (X₀ U : Zonotope (Vec ℝ n))
    (εHmax εPi Δt : ℝ) : -- --- CONCL ---
    ∀ (k η η' : ℕ), LinearSys.adaptTimeStepOrder sys le X₀ U εHmax εPi Δt η k = some η' →
      sys.timeIntervalStepCurvatureError Δt η' X₀ ≤ εHmax ∧
        sys.timePointStepRemainderError Δt η' U ≤ εPi := by -- --- PROOF ---
  intro k
  induction k with
  | zero => intro η η' h; rw [LinearSys.adaptTimeStepOrder] at h; exact absurd h (by simp)
  | succ k ih =>
    intro η η' h
    simp only [LinearSys.adaptTimeStepOrder] at h
    split at h
    -- the check cleared `η`, and `η` is what was reported
    · rename_i hc
      rw [Option.some.injEq] at h
      subst h
      rw [Bool.and_eq_true] at hc
      exact ⟨hle _ _ hc.1, hle _ _ hc.2⟩
    · exact ih _ _ h

/-- The step sweep reports only steps at which the order sweep succeeded, the
share being the one read at that very step. -/
private theorem aux_adaptTimeStepSearch_budget (sys : LinearSys 𝕋 n) {le : ℝ → ℝ → Bool}
    (hle : ∀ a b, le a b = true → a ≤ b) (X₀ U : Zonotope (Vec ℝ n))
    (εHmax εPmax εPacc tf ti μ : ℝ) (ηmax : ℕ) : -- --- CONCL ---
    ∀ (k : ℕ) (Δt Δti : ℝ) (ηi : ℕ),
      LinearSys.adaptTimeStepSearch sys le X₀ U εHmax εPmax εPacc tf ti μ ηmax Δt k
        = some (Δti, ηi) →
      sys.timeIntervalStepCurvatureError Δti ηi X₀ ≤ εHmax ∧
        sys.timePointStepRemainderError Δti ηi U
          ≤ (εPmax - εPacc) / (tf - ti) * Δti := by -- --- PROOF ---
  intro k
  induction k with
  | zero =>
    intro Δt Δti ηi h
    rw [LinearSys.adaptTimeStepSearch] at h
    exact absurd h (by simp)
  | succ k ih =>
    intro Δt Δti ηi h
    simp only [LinearSys.adaptTimeStepSearch] at h
    split at h
    -- an order cleared both bounds at this `Δt`, so this `Δt` is what was reported
    · rename_i η hsw
      rw [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact aux_adaptTimeStepOrder_budget sys hle X₀ U εHmax _ _ _ _ _ hsw
    · exact ih _ _ _ h


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 2]: a step the search reports is inside `ε_H,max` and inside its
own share of the `ε_P` budget, and the error it accumulates is eq. (9)'s. -/
theorem LinearSys.adaptTimeStep_budget (sys : LinearSys 𝕋 n) {le : ℝ → ℝ → Bool}
    (hle : ∀ a b, le a b = true → a ≤ b) (X₀ U : Zonotope (Vec ℝ n))
    (εHmax εPmax εPacc tf ti Δtprev μ : ℝ) (ηmax fuel : ℕ) : -- --- CONCL ---
    ∀ Δti ηi εP,
      (Δti, ηi, εP) ∈ sys.adaptTimeStep le X₀ U εHmax εPmax εPacc tf ti Δtprev μ ηmax fuel →
      sys.timeIntervalStepCurvatureError Δti ηi X₀ ≤ εHmax ∧
        sys.timePointStepRemainderError Δti ηi U ≤ (εPmax - εPacc) / (tf - ti) * Δti ∧
          εP = εPacc + sys.timePointStepRemainderError Δti ηi U := by -- --- PROOF ---
  intro Δti ηi εP (h : sys.adaptTimeStep le X₀ U εHmax εPmax εPacc tf ti Δtprev μ ηmax fuel = some
      (Δti, ηi, εP))
  simp only [LinearSys.adaptTimeStep] at h
  split at h
  · exact absurd h (by simp)
  -- the sweep settled on a step, and the third component is read off it
  · rename_i Δt' η' hsw
    rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨(aux_adaptTimeStepSearch_budget sys hle X₀ U εHmax εPmax εPacc tf ti μ ηmax
      fuel _ _ _ hsw).1, (aux_adaptTimeStepSearch_budget sys hle X₀ U εHmax εPmax εPacc tf ti μ
      ηmax fuel _ _ _ hsw).2, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
