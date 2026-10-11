import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IntermediateValue
import CORALean.HybridDynamics.TimeTriggered.Definitions.ContOverapprox
import CORALean.HybridDynamics.TimeTriggered.Definitions.FinalConversion
import CORALean.HybridDynamics.TimeTriggered.Definitions.FirstDwell
import CORALean.HybridDynamics.TimeTriggered.Definitions.SecondDwell
import CORALean.HybridDynamics.TimeTriggered.Operations.SpaceTriggered
import CORALean.HybridDynamics.TimeTriggered.Theorems.ExecFlowTimer
import CORALean.HybridDynamics.TimeTriggered.Theorems.LipschitzSolution
import CORALean.HybridDynamics.TimeTriggered.Theorems.ScaledSolutionClockLe
import CORALean.HybridDynamics.TimeTriggered.Theorems.ScaledSolutionEqOrbit
import CORALean.HybridDynamics.TimeTriggered.Theorems.ScaledSolutionNonneg
import CORALean.HybridDynamics.TimeTriggered.Theorems.SpaceTriggeredExecOrbit

/-!
# The combined transformation overapproximates

[1, Cor. 1]: for every `t_scaling ≥ 0`, `H_final` with time bound `T + t_scaling` overapproximates
`H` with time bound `T`. The paper reads it off `Lemma 1` and `Lemma 2`; the execution of `H_final`
is built from the end state of one of `H` here, whose f₁-orbit `z` (and, in `m₂`, the f₂-orbit from
the guard point `z(τ)`) `spaceTriggered_exec_orbit` gives. `H_final` follows `z` to `t₁`, then the
scaled solution `y` from `z(t₁)` for `t_scaling`, which is `z(t₁ + σ)` for the clock `σ`, and `σ`
stops at the guard point `z(τ)` (`scaledSolution_clock_le`, the step the paper does not mention:
the scaled run does not cross `G`). What is left of the orbit, `z` from `t₁ + σ` to `τ` and the
f₂-orbit, is run in `m_either` (and `m₂`), within `t₂` as `τ < t₁ + t₂`. The duration is
`d + t_scaling - σ ≤ T + t_scaling`. Flows are Lipschitz by [1, Def. 2], the scaled one too.

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
open scoped NNReal

variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]


-- =======================================  MAIN THEOREM  ======================================= --

-- the proof builds the execution of `H_final` in three modes, by cases, in one declaration
set_option maxHeartbeats 1000000 in
/-- `H_final` with time bound `T + t_scaling` overapproximates `H` with time bound `T`. -/
theorem DiffInclAutomaton.finalConversion_contOverapprox {I : Set X} {f₁ f₂ : X → X}
    {fe : X → Set X} {a : X} {b : ℝ} {t₁ t₂ ts : ℝ} {K₁ K₂ K' : ℝ≥0}
    (hf₁ : LipschitzWith K₁ f₁) (hf₂ : LipschitzWith K₂ f₂)
    (hF : LipschitzWith K' fun x => ((b - inner ℝ a x) / ‖a‖) • f₁ x)
    (hfe₁ : ∀ x, f₁ x ∈ fe x) (hfe₂ : ∀ x, f₂ x ∈ fe x) (ht₁ : 0 ≤ t₁) (hts : 0 ≤ ts)
    (h₁ : (spaceTriggered I f₁ f₂ a b).FirstDwell t₁)
    (h₂ : (spaceTriggered I f₁ f₂ a b).SecondDwell t₁ t₂) (T : ℝ) :
    (spaceTriggered I f₁ f₂ a b).ContOverapprox T
      (finalConversion I f₁ f₂ fe a b t₁ t₂ ts) Prod.fst (T + ts) := by -- --- PROOF ---
  unfold DiffInclAutomaton.ContOverapprox
  set Hs := spaceTriggered I f₁ f₂ a b with hHs
  set Hf := finalConversion I f₁ f₂ fe a b t₁ t₂ ts with hHf
  set g : X → ℝ := fun x => (b - inner ℝ a x) / ‖a‖ with hgdef
  have hg : Continuous g :=
    (continuous_const.sub (continuous_const.inner continuous_id)).div_const _
  -- the same state at another duration or timer
  have cast : ∀ {k : Fin 4} {d d' : ℝ} {p p' : X × ℝ}, Hf.Exec d k p → d = d' → p = p' →
      Hf.Exec d' k p' := by
    intro k d d' p p' h hd hp
    subst hd; subst hp; exact h
  -- the three time-triggered jumps
  have jump01 : ∀ {d : ℝ} {x : X}, Hf.Exec d 0 (x, t₁) → Hf.Exec d 1 (x, 0) := fun h =>
    h.jump ⟨0, {p | p.2 = t₁}, fun p => (p.1, 0), 1⟩
      (by simp [hHf, finalConversion]) rfl rfl
  have jump12 : ∀ {d : ℝ} {x : X}, Hf.Exec d 1 (x, ts) → Hf.Exec d 2 (x, 0) := fun h =>
    h.jump ⟨1, {p | p.2 = ts}, fun p => (p.1, 0), 2⟩
      (by simp [hHf, finalConversion]) rfl rfl
  have jump23 : ∀ {d : ℝ} {x : X}, Hf.Exec d 2 (x, t₂) → Hf.Exec d 3 (x, 0) := fun h =>
    h.jump ⟨2, {p | p.2 = t₂}, fun p => (p.1, 0), 3⟩
      (by simp [hHf, finalConversion]) rfl rfl
  -- an initial state followed by the orbit of `f₁` in `m₁`, up to the timer bound `t₁`
  have mode0 : ∀ {z : ℝ → X} {s : ℝ}, 0 ≤ s → s ≤ t₁ → z 0 ∈ I →
      (∀ u ∈ Icc 0 s, HasDerivAt z (f₁ (z u)) u) → Hf.Exec s 0 (z s, s) := by
    intro z s hs hst hz0 hz
    have e0 : Hf.Exec 0 0 (z 0, 0) :=
      DiffInclAutomaton.Exec.init (by simp [hHf, finalConversion, hz0])
    have := DiffInclAutomaton.exec_flow_timer (H := Hf) (k := 0) (V := fun u => f₁ (z u)) hs hz
      (fun u _ => by simp [hHf, finalConversion]) (fun u hu => by
        simp [hHf, finalConversion]
        linarith [hu.2]) e0
    simpa using this
  -- the scaled solution from a state of `m_scaling`, with its executions of any length up to `ts`
  have scale : ∀ {p : X} {d₀ : ℝ}, 0 ≤ g p → Hf.Exec d₀ 1 (p, 0) → ∃ y : ℝ → X, y 0 = p ∧
      (∀ u ∈ Icc 0 ts, HasDerivAt y (g (y u) • f₁ (y u)) u) ∧ (∀ u ∈ Icc 0 ts, 0 ≤ g (y u)) ∧
      ∀ r, 0 ≤ r → r ≤ ts → Hf.Exec (d₀ + r) 1 (y r, 0 + r) := by
    intro p d₀ hp he
    obtain ⟨y, hy0, hy⟩ := lipschitzSolution hF p ts
    refine ⟨y, hy0, hy, scaledSolution_nonneg hg hF hy (by rw [hy0]; exact hp), fun r hr hrts => ?_⟩
    refine DiffInclAutomaton.exec_flow_timer (H := Hf) (k := 1)
      (V := fun u => g (y u) • f₁ (y u)) hr (fun u hu => hy u ⟨hu.1, hu.2.trans hrts⟩)
      (fun u _ => by simp [hHf, finalConversion, hgdef]) (fun u hu => by
        simp [hHf, finalConversion]
        linarith [hu.2]) (by rw [hy0]; exact he)
  rintro x ⟨d, m, hdT, hex⟩
  obtain ⟨hd0, h0, h1⟩ := DiffInclAutomaton.spaceTriggered_exec_orbit hf₁ hf₂ hex
  have hdT' : d ≤ T + ts := by linarith
  fin_cases m
  · -- `x` is in `m₁`: it is `z d` on the orbit of `f₁` from an initial state
    obtain ⟨x₀, hx₀, hz⟩ := h0 rfl
    obtain ⟨z, hz0, hzd⟩ := lipschitzSolution hf₁ x₀ d
    obtain ⟨hzx, hzle⟩ := hz z hz0 hzd
    have hlt₂ : d < t₁ + t₂ := by
      by_contra hc
      exact absurd (h₂ d (not_lt.1 hc) 0 x hex) (by decide)
    by_cases hdt : d ≤ t₁
    · exact ⟨(z d, d), ⟨d, 0, hdT', mode0 hd0 hdt (hz0 ▸ hx₀) hzd⟩, by simp [hzx]⟩
    · -- `d > t₁`: `m₁` up to `t₁`, the scaled solution from `z t₁`, then `m_either`
      rw [not_le] at hdt
      have hz₁ : ∀ u ∈ Icc 0 t₁, HasDerivAt z (f₁ (z u)) u := fun u hu =>
        hzd u ⟨hu.1, hu.2.trans hdt.le⟩
      have e2 := jump01 (mode0 ht₁ le_rfl (hz0 ▸ hx₀) hz₁)
      set θ : ℝ := d - t₁ with hθ
      have hθpos : 0 < θ := by linarith
      have hgz : 0 ≤ g (z t₁) :=
        div_nonneg (sub_nonneg.2 (hzle (by linarith) t₁ ⟨ht₁, hdt.le⟩)) (norm_nonneg a)
      obtain ⟨y, hy0, hy, hsign, hystep⟩ := scale hgz e2
      have hyc : ContinuousOn y (Icc 0 ts) := fun u hu => (hy u hu).continuousAt.continuousWithinAt
      -- `z` from `t₁`, as the orbit the scaled solution follows
      have hz₂ : ∀ u ∈ Icc 0 θ, HasDerivAt (fun v => z (t₁ + v)) (f₁ (z (t₁ + u))) u :=
        fun u hu => by
          have := (hzd (t₁ + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩).comp_const_add t₁ u
          simpa using this
      have hrel : ∀ τ ∈ Icc 0 ts, (∫ v in (0 : ℝ)..τ, g (y v)) ≤ θ →
          y τ = z (t₁ + ∫ v in (0 : ℝ)..τ, g (y v)) := fun τ hτ hle =>
        scaledSolution_eq_orbit hf₁ hg hτ.1 (fun u hu => hsign u ⟨hu.1, hu.2.trans hτ.2⟩)
          (hyc.mono (Icc_subset_Icc le_rfl hτ.2))
          (fun u hu => (hy u ⟨hu.1, hu.2.le.trans hτ.2⟩).hasDerivWithinAt) hz₂ (by simp [hy0]) hle
      have hgy : ContinuousOn (fun v => g (y v)) (Icc 0 ts) := hg.comp_continuousOn hyc
      have hσc : ContinuousOn (fun τ => ∫ v in (0 : ℝ)..τ, g (y v)) (Icc 0 ts) := by
        have hint : IntervalIntegrable (fun v => g (y v)) MeasureTheory.volume 0 ts :=
          (hgy.mono (by simp)).intervalIntegrable_of_Icc hts
        simpa [uIcc_of_le hts] using
          intervalIntegral.continuousOn_primitive_interval' hint (a := 0) (by simp [hts])
      by_cases hbig : θ ≤ ∫ v in (0 : ℝ)..ts, g (y v)
      · -- the clock reaches `θ` within `t_scaling`: `x` is on the scaled solution
        obtain ⟨τ0, hτ0, hστ0⟩ := intermediate_value_Icc hts hσc (a := 0)
          (show θ ∈ Icc (∫ v in (0 : ℝ)..0, g (y v)) (∫ v in (0 : ℝ)..ts, g (y v)) by
            simpa using ⟨hθpos.le, hbig⟩)
        simp only at hστ0
        have hpt := hrel τ0 hτ0 hστ0.le
        rw [hστ0, hθ, add_sub_cancel, hzx] at hpt
        exact ⟨(y τ0, 0 + τ0), ⟨t₁ + τ0, 1, by linarith [hτ0.2], hystep τ0 hτ0.1 hτ0.2⟩, by
          simp [hpt]⟩
      · -- the clock stops short: `t_scaling` is spent, the rest of the orbit is in `m_either`
        rw [not_le] at hbig
        -- the clock `σ`, the full scaling step, and the jump into `m_either`
        set σ : ℝ := ∫ v in (0 : ℝ)..ts, g (y v) with hσ
        have hσ0 : 0 ≤ σ := intervalIntegral.integral_nonneg hts fun u hu => hsign u ⟨hu.1, hu.2⟩
        have e3 := hystep ts hts le_rfl
        simp only [zero_add] at e3
        have e4 := jump12 e3
        have hyts := hrel ts ⟨hts, le_rfl⟩ hbig.le
        have hr : 0 ≤ θ - σ := by linarith
        -- the rest of `z` is the orbit shifted by the clock, run in `m_either`
        have hw : ∀ u ∈ Icc 0 (θ - σ), HasDerivAt (fun v => z (t₁ + σ + v))
            (f₁ (z (t₁ + σ + u))) u := fun u hu => by
          have := (hzd (t₁ + σ + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩).comp_const_add
            (t₁ + σ) u
          simpa using this
        have e5 := DiffInclAutomaton.exec_flow_timer (H := Hf) (k := 2) (τ := 0) (d := t₁ + ts)
          (w := fun v => z (t₁ + σ + v)) (V := fun u => f₁ (z (t₁ + σ + u))) hr hw
          (fun u _ => by simp [hHf, finalConversion, hfe₁]) (fun u hu => by
            simp [hHf, finalConversion]
            linarith [hu.2]) (by simpa [hyts] using e4)
        refine ⟨(z (t₁ + σ + (θ - σ)), 0 + (θ - σ)), ⟨t₁ + ts + (θ - σ), 2, ?_, e5⟩, ?_⟩
        · linarith
        · simp only
          rw [← hzx]
          congr 1
          rw [hθ]; ring
  · -- `x` is in `m₂`: `w d-τ` on the orbit of `f₂` from the guard point `z τ` of the orbit of `f₁`
    obtain ⟨x₀, hx₀, τ, hτ0, hτd, hQ⟩ := h1 rfl
    obtain ⟨z, hz0, hzd⟩ := lipschitzSolution hf₁ x₀ τ
    obtain ⟨w, hw0, hwd⟩ := lipschitzSolution hf₂ (z τ) (d - τ)
    obtain ⟨hwx, hga, hle, hexτ⟩ := hQ z w hz0 hzd hw0 hwd
    -- the transition is taken between the two dwell times
    have hjump : Hs.Exec τ 1 (z τ) := hexτ.jump ⟨0, {x | inner ℝ a x = b}, id, 1⟩
      (by simp [spaceTriggered]) rfl hga
    have hτt₁ : t₁ ≤ τ := by
      by_contra hc
      have := h₁ τ (not_le.1 hc) 1 _ hjump
      simp at this
    have hτt₂ : τ < t₁ + t₂ := by
      by_contra hc
      have := h₂ τ (not_lt.1 hc) 0 _ hexτ
      simp at this
    -- `m₁` up to `t₁`, then the scaled solution from `z t₁`, whose clock stops at `τ - t₁`
    have e2 := jump01 (mode0 ht₁ le_rfl (hz0 ▸ hx₀) fun u hu => hzd u ⟨hu.1, hu.2.trans hτt₁⟩)
    have hgz : 0 ≤ g (z t₁) :=
      div_nonneg (sub_nonneg.2 (hle t₁ ⟨ht₁, hτt₁⟩)) (norm_nonneg a)
    obtain ⟨y, hy0, hy, hsign, hystep⟩ := scale hgz e2
    have hyc : ContinuousOn y (Icc 0 ts) := fun u hu => (hy u hu).continuousAt.continuousWithinAt
    have hz₂ : ∀ u ∈ Icc 0 (τ - t₁), HasDerivAt (fun v => z (t₁ + v)) (f₁ (z (t₁ + u))) u :=
      fun u hu => by
        have := (hzd (t₁ + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩).comp_const_add t₁ u
        simpa using this
    have hgM : g (z (t₁ + (τ - t₁))) = 0 := by
      simp [hgdef, hga]
    set σ : ℝ := ∫ v in (0 : ℝ)..ts, g (y v) with hσ
    have hσ0 : 0 ≤ σ := intervalIntegral.integral_nonneg hts fun u hu => hsign u ⟨hu.1, hu.2⟩
    have hσle : σ ≤ τ - t₁ := scaledSolution_clock_le hf₁ hg hF hts hy hsign hz₂
      (by simp [hy0]) (by linarith) hgM
    have hyts : y ts = z (t₁ + σ) := scaledSolution_eq_orbit hf₁ hg hts hsign hyc
      (fun u hu => (hy u ⟨hu.1, hu.2.le.trans le_rfl⟩).hasDerivWithinAt) hz₂ (by simp [hy0]) hσle
    have e3 := hystep ts hts le_rfl
    simp only [zero_add] at e3
    have e4 := jump12 e3
    -- what is left of the orbit of `f₁`, `ρ` long, is run in `m_either`
    set ρ : ℝ := τ - t₁ - σ with hρ
    set r : ℝ := d - τ with hr
    have hρ0 : 0 ≤ ρ := by linarith
    have hρt₂ : ρ < t₂ := by linarith
    have hr0 : 0 ≤ r := by linarith
    have hw₁ : ∀ u ∈ Icc 0 ρ, HasDerivAt (fun v => z (t₁ + σ + v)) (f₁ (z (t₁ + σ + u))) u :=
      fun u hu => by
        have := (hzd (t₁ + σ + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩).comp_const_add
          (t₁ + σ) u
        simpa using this
    have e5 := DiffInclAutomaton.exec_flow_timer (H := Hf) (k := 2) (τ := 0) (d := t₁ + ts)
      (w := fun v => z (t₁ + σ + v)) (V := fun u => f₁ (z (t₁ + σ + u))) hρ0 hw₁
      (fun u _ => by simp [hHf, finalConversion, hfe₁]) (fun u hu => by
        simp [hHf, finalConversion]
        linarith [hu.2]) (by simpa [hyts] using e4)
    -- at its end the state is `z τ = w 0`
    have e5' : Hf.Exec (t₁ + ts + ρ) 2 (w 0, ρ) := cast e5 rfl (by simp [hw0, hρ])
    have hwd' : ∀ u ∈ Icc 0 r, HasDerivAt w (f₂ (w u)) u := hwd
    by_cases hρr : ρ + r ≤ t₂
    · -- the rest of `w` fits in `m_either`
      have e6 := DiffInclAutomaton.exec_flow_timer (H := Hf) (k := 2) (w := w)
        (V := fun u => f₂ (w u)) hr0 hwd' (fun u _ => by simp [hHf, finalConversion, hfe₂])
        (fun u hu => by
          simp [hHf, finalConversion]
          linarith [hu.2]) e5'
      exact ⟨(w r, ρ + r), ⟨t₁ + ts + ρ + r, 2, by linarith, e6⟩, hwx⟩
    · -- `m_either` is left after `t₂ - ρ` of `w`, and the rest of `w` is run in `m₂`
      rw [not_le] at hρr
      -- `r₁` is how much of `w` is run in `m_either`, the rest `r - r₁` in `m₂`
      set r₁ : ℝ := t₂ - ρ with hr₁
      have hr₁0 : 0 ≤ r₁ := by linarith
      have hr₁r : r₁ ≤ r := by linarith
      have e6 := DiffInclAutomaton.exec_flow_timer (H := Hf) (k := 2) (w := w)
        (V := fun u => f₂ (w u)) hr₁0 (fun u hu => hwd' u ⟨hu.1, hu.2.trans hr₁r⟩)
        (fun u _ => by simp [hHf, finalConversion, hfe₂]) (fun u hu => by
          simp [hHf, finalConversion]
          linarith [hu.2]) e5'
      have e7 := jump23 (x := w r₁) (cast e6 rfl (by simp [hr₁]))
      -- after the jump, `m₂` runs the rest of `w`
      have hw₃ : ∀ u ∈ Icc 0 (r - r₁), HasDerivAt (fun v => w (r₁ + v)) (f₂ (w (r₁ + u))) u :=
        fun u hu => by
          have := (hwd' (r₁ + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩).comp_const_add r₁ u
          simpa using this
      have e8 := DiffInclAutomaton.exec_flow_timer (H := Hf) (k := 3) (τ := 0)
        (w := fun v => w (r₁ + v)) (V := fun u => f₂ (w (r₁ + u))) (by linarith) hw₃
        (fun u _ => by simp [hHf, finalConversion]) (fun u _ => by simp [hHf, finalConversion])
        (by simpa using e7)
      refine ⟨(w (r₁ + (r - r₁)), 0 + (r - r₁)), ⟨t₁ + ts + ρ + r₁ + (r - r₁), 3, ?_, e8⟩, ?_⟩
      · linarith
      · simp only
        rw [show r₁ + (r - r₁) = d - τ by rw [hr]; ring, hwx]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
