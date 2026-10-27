module

public import CORALean.HybridDynamics.TimeTriggered.Operations.ScalingConversion
public import CORALean.HybridDynamics.TimeTriggered.Theorems.FlowsOfHasDerivAt
public import CORALean.HybridDynamics.TimeTriggered.Theorems.HasDerivWithinAtIciOfDeriv
public import CORALean.HybridDynamics.TimeTriggered.Theorems.ScaledSolutionUnscale
public import CORALean.HybridDynamics.TimeTriggered.Theorems.SingleModeExistsSolutionOfIsExec

@[expose] public section

/-!
# What the scaled automaton reaches, the original reaches

[1, Lemma 2]'s proof: "the point `x'` will eventually be the continuous part of a reachable state
of `H`", so that `d_{Reach(H)}(x') = 0`. Every state `H_scaling` reaches, in any time and any
mode, is reached by `H_single` in some time: the copies of the mode are the same flow, and the
scaled one moves along the same orbit (`scaledSolution_unscale`). This is the zero-error half of the
lemma, against `Reach(H)` and not `Reach≤T(H)`, which the printed statement mixes up
(`scalingConversion_not_zeroError`).

## Inputs
* `I` – initial states
* `f` – flow
* `K` – Lipschitz constant
* `g` – scaling function
* `tb` – time scaling begins
* `ts` – scaling duration
* `d` – duration
* `τ` – clock
* `k` – mode
* `x` – continuous state

## Hypotheses
* `hf` – flow is Lipschitz
* `hg` – scaling function continuous
* `hg0` – scaling function nonnegative
* `h` – execution of the scaled automaton

## Conclusion
* the single mode reaches the same continuous state

## References

* [1] [S. Bak, S. Bogomolov and M. Althoff. "Time-Triggered Conversion of Guards for Reachability
      Analysis of Hybrid Automata". Formal Modeling and Analysis of Timed Systems,
      2017.](../../../../../references/2017/bak-formats-time-triggered-conversion.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set
open scoped NNReal

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [CompleteSpace X] in
/-- The `X`-component of a continuous successor of the scaled automaton. -/
private theorem aux_scaling_flows_proj {I : Set X} {f : X → X} {g : X → ℝ} {tb ts : ℝ} {k : Fin 3}
    {x x' : X} {τ τ' t : ℝ}
    (h : (DiffInclAutomaton.scalingConversion I f g tb ts).Flows k (x, τ) t (x', τ'))
    : -- --- CONCL ---
    0 < t ∧ ∃ y : ℝ → X, DifferentiableOn ℝ y (Icc 0 t) ∧ y 0 = x ∧ y t = x' ∧
      ∀ u ∈ Ioo 0 t,
        deriv y u = if k = 1 then g (y u) • f (y u) else f (y u) := by -- --- PROOF ---
  obtain ⟨ht, γ, hd, h0, htt, hγ⟩ := h
  refine ⟨ht, fun u => (γ u).1, hd.fst, by simp [h0], by simp [htt], fun u hu => ?_⟩
  have hda : HasDerivAt γ (deriv γ u) u :=
    (hd.differentiableAt (Icc_mem_nhds hu.1 hu.2)).hasDerivAt
  have hfst : HasDerivAt (fun u => (γ u).1) (deriv γ u).1 u :=
    (ContinuousLinearMap.fst ℝ X ℝ).hasFDerivAt.comp_hasDerivAt u hda
  rw [hfst.deriv]
  have := (hγ u hu).2
  simp only [DiffInclAutomaton.scalingConversion, Set.mem_prod, Set.mem_singleton_iff] at this
  split_ifs at this ⊢ with hk <;> simpa using this.1

omit [CompleteSpace X] in
/-- A solution from the end of an execution of the original automaton extends it. -/
private theorem aux_single_append {I : Set X} {f : X → X} {s σ : ℝ} {x : X} {γ : ℝ → X}
    (h : (DiffInclAutomaton.singleMode I f).IsExec s () x) (hσ : 0 ≤ σ) (h0 : γ 0 = x)
    (hγ : ∀ u ∈ Icc 0 σ, HasDerivAt γ (f (γ u)) u) : -- --- CONCL ---
    (DiffInclAutomaton.singleMode I f).IsExec (s + σ) () (γ σ) := by -- --- PROOF ---
  rcases hσ.eq_or_lt with rfl | hpos
  · simpa [h0] using h
  · rw [← h0] at h
    exact h.flow (DiffInclAutomaton.flows_of_hasDerivAt (v := fun u => f (γ u))
      (H := DiffInclAutomaton.singleMode I f) (m := ()) hpos hγ
      (fun u _ => by simp [DiffInclAutomaton.singleMode]) (fun u _ => by
        simp [DiffInclAutomaton.singleMode]))


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every state the scaled automaton reaches, in any duration and mode, the original reaches. -/
theorem DiffInclAutomaton.scalingConversion_isExec_subset_reach {I : Set X} {f : X → X} {K : ℝ≥0}
    (hf : LipschitzWith K f) {g : X → ℝ} (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x)
    {tb ts d τ : ℝ} {k : Fin 3} {x : X}
    (h : (DiffInclAutomaton.scalingConversion I f g tb ts).IsExec d k (x, τ)) : -- --- CONCL ---
    ∃ s, 0 ≤ s ∧ (DiffInclAutomaton.singleMode I f).IsExec s () x := by -- --- PROOF ---
  -- the induction over the execution, with the state's `X`-component and the timer kept apart
  generalize hp : (x, τ) = p at h
  induction h generalizing x τ with
  | @init m p0 hx =>
    subst hp
    refine ⟨0, le_rfl, DiffInclAutomaton.IsExec.init ?_⟩
    by_cases hm0 : m = 0
    · subst hm0
      simp only [DiffInclAutomaton.scalingConversion, if_true, Set.mem_prod,
        Set.mem_singleton_iff] at hx
      simpa [DiffInclAutomaton.singleMode] using hx.1
    · simp [DiffInclAutomaton.scalingConversion, hm0] at hx
  | @jump d m p0 h e he hm hx ih =>
    -- both transitions reset the timer only
    simp only [DiffInclAutomaton.scalingConversion, Set.mem_insert_iff,
      Set.mem_singleton_iff] at he
    have hxp : x = p0.1 := by rcases he with rfl | rfl <;> simpa using congrArg Prod.fst hp
    subst hxp
    exact ih rfl
  | @flow d t m p0 p1 h hf' ih =>
    subst hp
    obtain ⟨x0, τ0⟩ := p0
    obtain ⟨s, hs, hse⟩ := ih rfl
    obtain ⟨ht, y, hd, hy0, hyt, hder⟩ := aux_scaling_flows_proj hf'
    by_cases hm : m = 1
    · -- the scaled mode: the end state lies on the orbit, reached after the clock `∫ g(y)`
      obtain ⟨γ, hγ0, hγ, hγt⟩ := scaledSolution_unscale hf hg ht.le (fun u _ => hg0 _)
        hd.continuousOn
        (hasDerivWithinAt_Ici_of_deriv_eq (V := fun v => g v • f v) (hg.smul hf.continuous) ht hd
          fun u hu => by simpa [hm] using hder u hu)
      have hσ : 0 ≤ ∫ v in (0 : ℝ)..t, g (y v) :=
        intervalIntegral.integral_nonneg ht.le fun u _ => hg0 _
      refine ⟨_, hs.trans (le_add_of_nonneg_right hσ), ?_⟩
      have := aux_single_append hse hσ (hγ0.trans hy0) hγ
      rwa [hγt, hyt] at this
    · refine ⟨s + t, by linarith, hse.flow ⟨ht, y, hd, hy0, hyt, fun u hu => ⟨trivial, ?_⟩⟩⟩
      simpa [DiffInclAutomaton.singleMode, hm] using hder u hu

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
