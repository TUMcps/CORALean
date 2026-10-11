import CORALean.HybridDynamics.TimeTriggered.Definitions.FinalConversion
import CORALean.HybridDynamics.TimeTriggered.Definitions.FirstDwell
import CORALean.HybridDynamics.TimeTriggered.Definitions.OverapproxErrorLE
import CORALean.HybridDynamics.TimeTriggered.Definitions.SecondDwell
import CORALean.HybridDynamics.TimeTriggered.Operations.SpaceTriggered
import CORALean.HybridDynamics.TimeTriggered.Theorems.ExecFlowTimer
import CORALean.HybridDynamics.TimeTriggered.Theorems.LipschitzSolution
import CORALean.HybridDynamics.TimeTriggered.Theorems.SpaceTriggeredExecOrbit

/-!
# The error of the combined transformation does not go to zero

[1, Thm. 1] says that for every `T` and `δ > 0` some `t_scaling` brings the error of `H_final`
against `Reach≤T(H)` below `δ`. It does not. Take `ẋ = 1` in `m₁`, `ẋ = 0` in `m₂`, the guard
`x = 0` (`a = 1`, `b = 0`), initial states `-100` and `-10`: they reach the guard at `100` and
`10`, so `t₁ = 10` and every `t₂ > 90` fits `SecondDwell` (here `t₂ = 100`). With
`f_either = [0, 1]` the run from `-10` is on the guard at `t₁`, where the scaling `g = -x` does
nothing, and it spends the whole dwell `t₂` in `m_either`, reaching `50` within
`T' = 100 + t_scaling` for every `t_scaling ≥ 0`, while `Reach≤100(H) ⊆ [-100, 0]`. The printed
proof bounds the time spent in `m_either` by `t₂ ≤ t_γ`, but `t₂` is the dwell time of `H`, which
scaling does not shrink. All executions of `H` end in `[-100, 0]`, so the unbounded `Reach(H)` is
no nearer.

## References

* [1] S. Bak, S. Bogomolov and M. Althoff. "Time-Triggered Conversion of Guards for
      Reachability Analysis of Hybrid Automata". In Formal Modeling and Analysis of Timed
      Systems (FORMATS), LNCS 10419, pp. 133-150, 2017.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Every execution of the counterexample ends in `[-100, 0]`, in `m₂` at `0` after `10` or more. -/
theorem aux_exec_char {d x : ℝ} {m : Fin 2}
    (h : (DiffInclAutomaton.spaceTriggered ({-100, -10} : Set ℝ) (fun _ => (1 : ℝ))
      (fun _ => (0 : ℝ)) (1 : ℝ) 0).Exec d m x) :
    (m = 0 → -100 ≤ x ∧ x ≤ 0 ∧ d ≤ 100) ∧ (m = 1 → x = 0 ∧ 10 ≤ d) := by -- --- PROOF ---
  obtain ⟨hd0, h0, h1⟩ := DiffInclAutomaton.spaceTriggered_exec_orbit
    (LipschitzWith.const (1 : ℝ)) (LipschitzWith.const (0 : ℝ)) h
  refine ⟨fun hm => ?_, fun hm => ?_⟩
  · -- in `m₁`, `x = x₀ + d` for the initial state `x₀`, and `x₀ + u ≤ 0` up to `d`
    obtain ⟨x₀, hx₀, hz⟩ := h0 hm
    obtain ⟨hzx, hzle⟩ := hz (fun u => x₀ + u) (add_zero x₀) (fun u _ => by
      simpa using (hasDerivAt_id u).const_add x₀)
    have hx₀' : x₀ = -100 ∨ x₀ = -10 := by simpa using hx₀
    rcases hd0.eq_or_lt with hd | hd
    · subst hd
      have hx : x = x₀ := by simpa using hzx.symm
      rcases hx₀' with rfl | rfl <;> subst hx <;> refine ⟨?_, ?_, ?_⟩ <;> norm_num
    · have := hzle hd d ⟨hd.le, le_rfl⟩
      simp at this
      rcases hx₀' with rfl | rfl <;> refine ⟨?_, ?_, ?_⟩ <;> linarith
  · -- in `m₂`, at `0` after the guard `-x₀` is reached
    obtain ⟨x₀, hx₀, τ, hτ0, hτd, hz⟩ := h1 hm
    obtain ⟨hwx, hga, -, -⟩ := hz (fun u => x₀ + u) (fun _ => x₀ + τ) (add_zero x₀) (fun u _ => by
      simpa using (hasDerivAt_id u).const_add x₀) rfl (fun u _ => by
      simpa using hasDerivAt_const u (x₀ + τ))
    have hx₀' : x₀ = -100 ∨ x₀ = -10 := by simpa using hx₀
    simp at hga hwx
    refine ⟨by linarith, ?_⟩
    rcases hx₀' with rfl | rfl <;> linarith

/-- The run from `-10` reaches `50` in `m_either` within the extended time bound. -/
theorem aux_reaches_fifty {ts : ℝ} (hts : 0 ≤ ts) :
    (50 : ℝ) ∈ Prod.fst '' (DiffInclAutomaton.finalConversion ({-100, -10} : Set ℝ)
      (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) (fun _ => Icc (0 : ℝ) 1) (1 : ℝ) 0 10 100 ts).reachLE
        (100 + ts) := by -- --- PROOF ---
  set Hf := DiffInclAutomaton.finalConversion ({-100, -10} : Set ℝ) (fun _ => (1 : ℝ))
    (fun _ => (0 : ℝ)) (fun _ => Icc (0 : ℝ) 1) (1 : ℝ) 0 10 100 ts with hHf
  -- the same state at another duration or timer
  have cast : ∀ {k : Fin 4} {d d' : ℝ} {p p' : ℝ × ℝ}, Hf.Exec d k p → d = d' → p = p' →
      Hf.Exec d' k p' := by
    intro k d d' p p' h hd hp
    subst hd; subst hp; exact h
  -- the run from `-10`: `m₁` for `10`, `m_scaling` at the guard, `m_either` for `50`
  have e0 : Hf.Exec 0 0 (-10, 0) :=
    DiffInclAutomaton.Exec.init (by simp [hHf, DiffInclAutomaton.finalConversion])
  have e1 := DiffInclAutomaton.exec_flow_timer (H := Hf) (k := 0) (w := fun u => -10 + u)
    (V := fun _ => (1 : ℝ)) (τ := 0) (d := 0) (r := 10) (by norm_num)
    (fun u _ => by simpa using (hasDerivAt_id u).const_add (-10 : ℝ))
    (fun u _ => by simp [hHf, DiffInclAutomaton.finalConversion]) (fun u hu => by
      simp [hHf, DiffInclAutomaton.finalConversion]
      linarith [hu.2]) (by simpa using e0)
  have e2 : Hf.Exec 10 1 (0, 0) :=
    (cast e1 (by norm_num) (by norm_num) : Hf.Exec 10 0 (0, 10)).jump
      ⟨0, {p | p.2 = 10}, fun p => (p.1, 0), 1⟩
      (by simp [hHf, DiffInclAutomaton.finalConversion]) rfl (by simp)
  -- at the guard `g = 0`, so the scaled solution stays
  have e3 := DiffInclAutomaton.exec_flow_timer (H := Hf) (k := 1) (w := fun _ => (0 : ℝ))
    (V := fun _ => (0 : ℝ)) (τ := 0) (d := 10) (r := ts) hts
    (fun u _ => hasDerivAt_const u (0 : ℝ))
    (fun u _ => by simp [hHf, DiffInclAutomaton.finalConversion]) (fun u hu => by
      simp [hHf, DiffInclAutomaton.finalConversion]
      linarith [hu.2]) e2
  have e4 : Hf.Exec (10 + ts) 2 (0, 0) :=
    (cast e3 rfl (by simp) : Hf.Exec (10 + ts) 1 (0, ts)).jump
      ⟨1, {p | p.2 = ts}, fun p => (p.1, 0), 2⟩
      (by simp [hHf, DiffInclAutomaton.finalConversion]) rfl (by simp)
  have e5 := DiffInclAutomaton.exec_flow_timer (H := Hf) (k := 2) (w := fun u => u)
    (V := fun _ => (1 : ℝ)) (τ := 0) (d := 10 + ts) (r := 50) (by norm_num)
    (fun u _ => hasDerivAt_id' u)
    (fun u _ => by simp [hHf, DiffInclAutomaton.finalConversion]) (fun u hu => by
      simp [hHf, DiffInclAutomaton.finalConversion]
      linarith [hu.2]) e4
  exact ⟨(50, 0 + 50), ⟨10 + ts + 50, 2, by linarith, e5⟩, rfl⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- With `t₁ = 10`, `t₂ = 100` the dwell conditions hold, but for every `t_scaling ≥ 0` the error
of `H_final` against `Reach≤100(H)` is at least `50`: none brings it below `δ = 50`. -/
theorem DiffInclAutomaton.finalConversion_not_error_lt :
    (DiffInclAutomaton.spaceTriggered ({-100, -10} : Set ℝ) (fun _ => (1 : ℝ))
        (fun _ => (0 : ℝ)) (1 : ℝ) 0).FirstDwell 10 ∧
      (DiffInclAutomaton.spaceTriggered ({-100, -10} : Set ℝ) (fun _ => (1 : ℝ))
        (fun _ => (0 : ℝ)) (1 : ℝ) 0).SecondDwell 10 100 ∧
      ∀ ts : ℝ, 0 ≤ ts → ∀ e : ENNReal, e < ENNReal.ofReal 50 →
        ¬ (DiffInclAutomaton.spaceTriggered ({-100, -10} : Set ℝ) (fun _ => (1 : ℝ))
          (fun _ => (0 : ℝ)) (1 : ℝ) 0).OverapproxErrorLE 100
          (DiffInclAutomaton.finalConversion ({-100, -10} : Set ℝ) (fun _ => (1 : ℝ))
            (fun _ => (0 : ℝ)) (fun _ => Icc (0 : ℝ) 1) (1 : ℝ) 0 10 100 ts) Prod.fst
          (100 + ts) e := by -- --- PROOF ---
  refine ⟨fun d hd m x h => ?_, fun d hd m x h => ?_, fun ts hts e he hle => ?_⟩
  · -- an execution in `m₂` has duration at least `10`
    by_contra hm
    have hm1 : m = 1 := by omega
    exact absurd (aux_exec_char h).2 (fun hh => by linarith [(hh hm1).2])
  · -- an execution in `m₁` has duration at most `100`
    by_contra hm
    have hm0 : m = 0 := by omega
    linarith [((aux_exec_char h).1 hm0).2.2]
  · -- `50` is at distance at least `50` from the states `H` reaches, which are in `[-100, 0]`
    have h50 := hle 50 (aux_reaches_fifty hts)
    have hge : ENNReal.ofReal 50 ≤ Metric.infEDist (50 : ℝ) ((DiffInclAutomaton.spaceTriggered
        ({-100, -10} : Set ℝ) (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) (1 : ℝ) 0).reachLE 100) := by
      rw [Metric.le_infEDist]
      rintro y ⟨d, m, -, hy⟩
      have hy0 : -100 ≤ y ∧ y ≤ 0 := by
        fin_cases m
        · exact ⟨((aux_exec_char hy).1 rfl).1, ((aux_exec_char hy).1 rfl).2.1⟩
        · have := ((aux_exec_char hy).2 rfl).1
          constructor <;> linarith
      rw [edist_dist, Real.dist_eq]
      exact ENNReal.ofReal_le_ofReal (by rw [abs_of_pos (by linarith [hy0.2])]; linarith [hy0.2])
    exact absurd (hge.trans h50) (not_le.2 he)


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
