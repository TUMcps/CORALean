import Mathlib.Analysis.Calculus.Deriv.MeanValue
import CORALean.HybridDynamics.TimeTriggered.Definitions.OverapproxErrorLE
import CORALean.HybridDynamics.TimeTriggered.Operations.ScalingConversion
import CORALean.HybridDynamics.TimeTriggered.Operations.SingleMode
import CORALean.HybridDynamics.TimeTriggered.Theorems.FlowsTimer

/-!
# The scaled automaton is not a zero-error overapproximation within the time bound

[1, Lemma 2] says `H_scaling` with time bound `T' = T + t_scaling` is a *zero-error*
time-bounded overapproximation of `H_single` with time bound `T`: by [1, Def. 9] every
state it reaches within `T'` lies in `Reach≤T(H_single)`. It does not. At `ẋ = 1` in one
dimension from `x = 0`, with `g ≡ 1`, `t_begin = t_scaling = 1` and `T = 1`, the scaled
automaton is the original one with a pause-free relabelling, and it reaches `x = 2` by time
`T' = 2` while `Reach≤1(H_single) = [0, 1]`. The printed proof shows `d_{Reach(H)}(x') = 0`
for the *unbounded* `Reach(H)` instead.

## References

* [1] S. Bak, S. Bogomolov and M. Althoff. "Time-Triggered Conversion of Guards for
      Reachability Analysis of Hybrid Automata". In Formal Modeling and Analysis of Timed
      Systems (FORMATS), LNCS 10419, pp. 133-150, 2017.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A flow with derivative one moves the state by the dwell time. -/
theorem aux_flows_one {x x' t : ℝ}
    (h : (DiffInclAutomaton.singleMode ({0} : Set ℝ) (fun _ => (1 : ℝ))).Flows () x t x') :
    x' = x + t := by -- --- PROOF ---
  obtain ⟨ht, g, hd, h0, htt, hg⟩ := h
  -- the mean value theorem for `g δ - δ`, whose derivative vanishes on the interior
  have hd' : DifferentiableOn ℝ (fun δ => g δ - δ) (Set.Icc 0 t) :=
    hd.sub differentiableOn_id
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope (fun δ => g δ - δ) ht hd'.continuousOn
    (hd'.mono Set.Ioo_subset_Icc_self)
  have hdc : DifferentiableAt ℝ g c := hd.differentiableAt (Icc_mem_nhds hc.1 hc.2)
  have h1 : deriv g c = 1 := by simpa [DiffInclAutomaton.singleMode] using (hg c hc).2
  have : deriv (fun δ => g δ - δ) c = 0 := by
    have hh : HasDerivAt (fun δ => g δ - δ) (deriv g c - 1) c :=
      hdc.hasDerivAt.sub (hasDerivAt_id' c)
    rw [hh.deriv, h1]; simp
  rw [this] at hcd
  have := (div_eq_zero_iff.1 hcd.symm).resolve_right (by simpa using ht.ne')
  simp only [h0, htt] at this
  linarith

/-- Every state of the original automaton is its duration. -/
theorem aux_exec_eq {d x : ℝ} {m : Unit}
    (h : (DiffInclAutomaton.singleMode ({0} : Set ℝ) (fun _ => (1 : ℝ))).Exec d m x) :
    x = d := by
  induction h with
  | init hx => simpa [DiffInclAutomaton.singleMode] using hx
  | flow _ hf ih => rw [aux_flows_one hf, ih]
  | jump _ e he => simp [DiffInclAutomaton.singleMode] at he

/-- The unit-speed flow of the original automaton over one time unit. -/
theorem aux_flows_unit (x : ℝ) :
    (DiffInclAutomaton.singleMode ({0} : Set ℝ) (fun _ => (1 : ℝ))).Flows () x 1 (x + 1) :=
  ⟨one_pos, fun δ => x + δ, by fun_prop, by simp, rfl, fun δ _ => by
    have : deriv (fun δ : ℝ => x + δ) δ = 1 := by
      simp
    simp [DiffInclAutomaton.singleMode, this]⟩

-- The scaled automaton, at `g ≡ 1` and `t_begin = t_scaling = 1`, runs `x` up to `x + 1` in a mode.
theorem aux_scaling_flow {k : Fin 3} (hk : k = 0 ∨ k = 1) (x : ℝ) :
    (DiffInclAutomaton.scalingConversion ({0} : Set ℝ) (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
      1 1).Flows k (x, 0) 1 (x + 1, 0 + 1) := by -- --- PROOF ---
  refine DiffInclAutomaton.flows_timer (c := 1) (aux_flows_unit x) ?_ ?_ (by norm_num)
  · intro y τ' v hv
    rcases hk with rfl | rfl <;> simp_all [DiffInclAutomaton.scalingConversion,
      DiffInclAutomaton.singleMode]
  · intro y _ τ' hτ
    rcases hk with rfl | rfl <;> simp [DiffInclAutomaton.scalingConversion, hτ]

/-- The scaled automaton reaches `2` in duration `2`. -/
theorem aux_reaches_two :
    (2 : ℝ) ∈ Prod.fst '' (DiffInclAutomaton.scalingConversion ({0} : Set ℝ) (fun _ => (1 : ℝ))
      (fun _ => (1 : ℝ)) 1 1).reachLE (1 + 1) := by -- --- PROOF ---
  set H := DiffInclAutomaton.scalingConversion ({0} : Set ℝ) (fun _ => (1 : ℝ))
    (fun _ => (1 : ℝ)) 1 1 with hH
  -- init, flow in `m`, jump, flow in `m_scaling`, jump
  have e0 : H.Exec 0 0 (0, 0) :=
    DiffInclAutomaton.Exec.init (by simp [hH, DiffInclAutomaton.scalingConversion])
  have e1 := e0.flow (aux_scaling_flow (Or.inl rfl) 0)
  have e2 := e1.jump ⟨0, {p | p.2 = 1}, fun p => (p.1, 0), 1⟩
    (by simp [hH, DiffInclAutomaton.scalingConversion]) rfl (by simp)
  have e3 := e2.flow (aux_scaling_flow (Or.inr rfl) (0 + 1))
  have e4 := e3.jump ⟨1, {p | p.2 = 1}, fun p => (p.1, 0), 2⟩
    (by simp [hH, DiffInclAutomaton.scalingConversion]) rfl (by simp)
  exact ⟨(0 + 1 + 1, 0), ⟨0 + 1 + 1, 2, by norm_num, e4⟩, by norm_num⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- At `ẋ = 1`, `g ≡ 1`, `t_begin = t_scaling = T = 1` the error against `Reach≤T` is not zero. -/
theorem DiffInclAutomaton.scalingConversion_not_zeroError :
    ¬ (DiffInclAutomaton.singleMode ({0} : Set ℝ) (fun _ => (1 : ℝ))).OverapproxErrorLE 1
      (DiffInclAutomaton.scalingConversion ({0} : Set ℝ) (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
        1 1) Prod.fst (1 + 1) 0 := by -- --- PROOF ---
  intro h
  have h2 := h 2 aux_reaches_two
  -- `Reach≤1` of the original is below `1`, so `2` is at distance at least one from it
  have hge : 1 ≤ Metric.infEDist (2 : ℝ) ((DiffInclAutomaton.singleMode ({0} : Set ℝ)
      (fun _ => (1 : ℝ))).reachLE 1) := by
    rw [Metric.le_infEDist]
    rintro y ⟨d, m, hd, he⟩
    have hy := aux_exec_eq he
    rw [edist_dist, Real.dist_eq]
    exact ENNReal.one_le_ofReal.2 (by rw [abs_of_pos (by linarith)]; linarith)
  exact absurd (hge.trans h2) (by norm_num)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
