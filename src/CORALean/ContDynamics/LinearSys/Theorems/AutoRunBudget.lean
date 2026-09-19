import CORALean.ContDynamics.LinearSys.AutoTuneReach
import CORALean.ContSet.Zonotope.Real.Theorems.AutoTuneSetOrderLe

/-!
# `Alg. 2` keeps both accumulated errors inside their shares, at every step

Eq. (33)'s `ε^a_{k+1} = ε^a_k + Δε^a_k` and eq. (28)'s `ε^r_{k+1} = ε^r_k + Δε^r_k` are the
two accumulations line 29 carries, and eq. (36)/(35) are the shares of `ε_max` they may
occupy at `t_k`. This is the invariant [1] maintains across the loop rather than proves:
along every run, `ε^a_k ≤ (t_k/t_end)(1-ζ)ε_max` and `ε^r_k ≤ (t_k/t_end)ζε_max`.

What keeps them there is *not* the accumulation but the two checks the tuning stops on.
Line 14 measures `Δε^a_k` against `ε^{a,τ}_k = (t_{k+1}/t_end)(1-ζ)ε_max - ε^a_k`, already
net of what has accumulated, and line 22 measures `Δε^r_k(ρ_k)` against line 19's
`ε^{r,τ}_k = (t_{k+1}/t_end)ζε_max - ε^r_k` likewise; so each step re-establishes its own
bound outright and the induction carries nothing but the time and the step size.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       19-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Lines 9-15: the order the sweep reports is one line 15 checked, so `Δε^a_k` is inside
the share `ε^{a,τ}_k` it was measured against. -/
theorem aux_autoTuneOrder_le (sys : LinearSys 𝕋 n) {le : ℝ → ℝ → Bool}
    (hle : ∀ a b : ℝ, le a b = true → a ≤ b) (H : Zonotope (Vec ℝ n)) (ũ : Vec ℝ n) (tk : ℝ)
    (U₀ : Zonotope (Vec ℝ n)) {Δt εaτ εnτ : ℝ} :
    ∀ (m η η' : ℕ), sys.autoTuneOrder le H ũ tk U₀ Δt εaτ εnτ η m = some η' →
      MatExp.particularSolutionError (toRealMat sys.A) tk U₀.construct Δt η'
        ≤ εaτ := by -- --- PROOF ---
  intro m
  induction m with
  | zero => intro η η' h; rw [LinearSys.autoTuneOrder] at h; exact absurd h (by simp)
  | succ m ih =>
    intro η η' h
    rw [LinearSys.autoTuneOrder] at h
    split at h
    -- line 15 cleared both shares at this `η`, and the left conjunct is the one wanted
    · rename_i hchk
      rw [Option.some.injEq] at h
      subst h
      exact hle _ _ (Bool.and_eq_true_iff.mp hchk).1
    · exact ih _ _ h

-- the sweep's own `let`s carry three error terms, each re-solving the matrix instances
set_option maxHeartbeats 400000 in
/-- Lines 6-15: whatever the halving sweep reports is a positive step whose `Δε^a_k` is
inside line 14's share at that very step. -/
theorem aux_autoTuneSearch_le (sys : LinearSys 𝕋 n) {le : ℝ → ℝ → Bool}
    (hle : ∀ a b : ℝ, le a b = true → a ≤ b) (H : Zonotope (Vec ℝ n)) (ũ : Vec ℝ n)
    {tk tend εmax ζ εaAcc : ℝ} (ηmax : ℕ) (U₀ : Zonotope (Vec ℝ n)) :
    ∀ (m : ℕ) (Δt Δtk : ℝ) (ηk : ℕ), 0 < Δt →
      sys.autoTuneSearch le H ũ tk tend εmax ζ εaAcc ηmax U₀ Δt m = some (Δtk, ηk) →
        0 < Δtk ∧ MatExp.particularSolutionError (toRealMat sys.A) tk U₀.construct Δtk ηk
          ≤ (tk + Δtk) / tend * (1 - ζ) * εmax - εaAcc := by -- --- PROOF ---
  intro m
  induction m with
  | zero => intro Δt Δtk ηk _ h; rw [LinearSys.autoTuneSearch] at h; exact absurd h (by simp)
  | succ m ih =>
    intro Δt Δtk ηk hΔt h
    simp only [LinearSys.autoTuneSearch] at h
    split at h
    -- an order cleared both shares at this candidate, so this halving is what was reported
    · rename_i η hord
      rw [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by linarith, aux_autoTuneOrder_le sys hle H ũ tk U₀ ηmax 2 η hord⟩
    · exact ih _ _ _ (by linarith) h

/-- Lines 5-15: the same of `autoTuneDeltaT`, whose own line 5 doubles a positive step. -/
theorem aux_autoTuneDeltaT_le (sys : LinearSys 𝕋 n) {le : ℝ → ℝ → Bool}
    (hle : ∀ a b : ℝ, le a b = true → a ≤ b) (H : Zonotope (Vec ℝ n)) (ũ : Vec ℝ n)
    {tk tend εmax ζ εaAcc Δtprev : ℝ} (ηmax fuel : ℕ) (U₀ : Zonotope (Vec ℝ n))
    (hΔtprev : 0 < Δtprev) {Δtk : ℝ} {ηk : ℕ}
    (h : sys.autoTuneDeltaT le H ũ tk tend εmax ζ εaAcc Δtprev ηmax fuel U₀
      = some (Δtk, ηk)) :
    0 < Δtk ∧ MatExp.particularSolutionError (toRealMat sys.A) tk U₀.construct Δtk ηk
      ≤ (tk + Δtk) / tend * (1 - ζ) * εmax - εaAcc :=
  aux_autoTuneSearch_le sys hle H ũ ηmax U₀ fuel _ _ _ (by linarith) h

/-- One iteration re-establishes both budget bounds outright: lines 14 and 22 check each
increment against what is left of its own share at `t_{k+1}`. -/
theorem aux_autoStep_budget (sys : LinearSys 𝕋 n) {le : ℝ → ℝ → Bool}
    (hle : ∀ a b : ℝ, le a b = true → a ≤ b) (X₀ U : Zonotope (Vec ℝ n))
    {tend εmax ζ : ℝ} {ηmax fuel : ℕ} {s : LinearSys.AutoState n} (hΔt : 0 < s.Δt)
    (ht : 0 ≤ s.t) {r : LinearSys.AutoState n × Zonotope (Vec ℝ n)}
    (h : sys.autoStep le X₀ U tend εmax ζ ηmax fuel s = some r) :
    0 ≤ r.1.t ∧ 0 < r.1.Δt ∧ r.1.εa ≤ r.1.t / tend * (1 - ζ) * εmax ∧
      r.1.εr ≤ r.1.t / tend * ζ * εmax := by -- --- PROOF ---
  simp only [LinearSys.autoStep] at h
  split at h
  · exact absurd h (by simp)
  · rename_i Δtk ηk hdt
    obtain ⟨hΔtk, hεa⟩ := aux_autoTuneDeltaT_le sys hle s.H U.c ηmax fuel _ hΔt hdt
    split at h
    · exact absurd h (by simp)
    -- lines 19-22 reported an order, so line 29's `Δε^r_k` is the one line 22 cleared
    · rename_i ρk hρ
      have hεr := Zonotope.autoTuneSetOrder_le hle _ _ 0 ρk hρ
      rw [Option.some.injEq] at h
      subst h
      exact ⟨by dsimp only; linarith, hΔtk, by dsimp only; linarith, by dsimp only; linarith⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1]'s carried invariant, over [1, Alg. 2]'s own loop: along every run, `ε^a_k` and
`ε^r_k` stay inside eq. (36)'s and eq. (35)'s shares at `t_k`, and the step stays positive. -/
theorem LinearSys.autoRun_budget (sys : LinearSys 𝕋 n) {le : ℝ → ℝ → Bool}
    (hle : ∀ a b : ℝ, le a b = true → a ≤ b) (X₀ U : Zonotope (Vec ℝ n))
    {tend εmax ζ : ℝ} (htend : 0 < tend) (ηmax fuel : ℕ) :
    ∀ (k : ℕ) (s : LinearSys.AutoState n),
      sys.autoRun le X₀ U tend εmax ζ ηmax fuel k = some s →
        0 ≤ s.t ∧ 0 < s.Δt ∧ s.εa ≤ s.t / tend * (1 - ζ) * εmax ∧
          s.εr ≤ s.t / tend * ζ * εmax := by -- --- PROOF ---
  intro k
  induction k with
  | zero =>
    intro s h
    rw [LinearSys.autoRun, Option.some.injEq] at h
    subst h
    exact ⟨le_refl 0, htend, by simp [LinearSys.autoInit], by simp [LinearSys.autoInit]⟩
  | succ k ih =>
    intro s h
    cases hprev : sys.autoRun le X₀ U tend εmax ζ ηmax fuel k with
    | none => simp [LinearSys.autoRun, hprev] at h
    | some s₀ =>
      obtain ⟨ht₀, hΔt₀, -, -⟩ := ih s₀ hprev
      simp only [LinearSys.autoRun, hprev] at h
      split at h
      -- the horizon is not reached, so one iteration runs and re-establishes both bounds
      · cases hstep : sys.autoStep le X₀ U tend εmax ζ ηmax fuel s₀ with
        | none => rw [hstep] at h; exact absurd h (by simp)
        | some r =>
          rw [hstep, Option.map_some, Option.some.injEq] at h
          subst h
          exact aux_autoStep_budget sys hle X₀ U hΔt₀ ht₀ hstep
      · rw [Option.some.injEq] at h
        subst h
        exact ih s₀ hprev

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
