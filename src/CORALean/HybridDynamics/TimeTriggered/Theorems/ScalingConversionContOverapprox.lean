import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IntermediateValue
import CORALean.HybridDynamics.TimeTriggered.Definitions.ContOverapprox
import CORALean.HybridDynamics.TimeTriggered.Operations.ScalingConversion
import CORALean.HybridDynamics.TimeTriggered.Theorems.FlowsOfHasDerivAt
import CORALean.HybridDynamics.TimeTriggered.Theorems.LipschitzSolutionUnique
import CORALean.HybridDynamics.TimeTriggered.Theorems.ScaledSolutionUnscale
import CORALean.HybridDynamics.TimeTriggered.Theorems.SingleModeExistsSolutionOfExec

/-!
# The scaled automaton overapproximates within the extended time bound

[1, Lemma 2], the overapproximation half: `Reach≤T(H_single) ⊆ Reach≤T+t_scaling(H_scaling)`. A
state of `H_single` at time `s ≤ T` is `z(s)` on a solution `z`. If `s ≤ t_begin` the same
execution is one of `H_scaling`. Otherwise `H_scaling` follows `z` to `t_begin`, then the scaled
solution `y` from `z(t_begin)`, which is `z(t_begin + σ)` for the clock `σ(τ) = ∫₀^τ g(y)`
(`scaledSolution_unscale` and uniqueness): `z(s)` is on `y` if the clock reaches `s - t_begin`
within `t_scaling`, by the intermediate value theorem, and is otherwise reached in `m'` for the
rest, `t_scaling` having been spent. The paper's "pauses for at most `t_scaling`" is this
count of the time budget. `t_begin, t_scaling > 0` are [1, Sec. 3.2]'s; `g · f` is Lipschitz
because [1, Def. 2] makes every flow so, which gives the solution `y`.

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

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `H_scaling` with time bound `T + t_scaling` overapproximates `H_single` with time bound `T`. -/
theorem DiffInclAutomaton.scalingConversion_contOverapprox {I : Set X} {f : X → X} {K K' : ℝ≥0}
    (hf : LipschitzWith K f) {g : X → ℝ} (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x)
    (hF : LipschitzWith K' fun x => g x • f x) {tb ts : ℝ} (htb : 0 < tb) (hts : 0 < ts) (T : ℝ) :
    (DiffInclAutomaton.singleMode I f).ContOverapprox T
      (DiffInclAutomaton.scalingConversion I f g tb ts) Prod.fst (T + ts) := by -- --- PROOF ---
  set H' := DiffInclAutomaton.scalingConversion I f g tb ts with hH'
  -- a flow of `H'` in mode `k`, along a curve `w` with derivative `V` and the timer running
  have step : ∀ (k : Fin 3) {w V : ℝ → X} {r τ d : ℝ}, 0 < r →
      (∀ u ∈ Icc 0 r, HasDerivAt w (V u) u) →
      (∀ u ∈ Ioo 0 r, V u ∈ (if k = 1 then {g (w u) • f (w u)} else {f (w u)} : Set X)) →
      (∀ u ∈ Ioo 0 r, (w u, τ + u) ∈ H'.inv k) → H'.Exec d k (w 0, τ) →
      H'.Exec (d + r) k (w r, τ + r) := by
    intro k w V r τ d hr hw hV hinv h
    have hy : ∀ u ∈ Icc 0 r, HasDerivAt (fun u => (w u, τ + u)) (V u, 1) u := fun u hu =>
      (hw u hu).prodMk
        (by simpa using (hasDerivAt_id u).const_add τ : HasDerivAt (fun δ : ℝ => τ + δ) 1 u)
    have := DiffInclAutomaton.flows_of_hasDerivAt (H := H') (m := k) hr hy
      (fun u hu => by
        simp only [hH', DiffInclAutomaton.scalingConversion, Set.mem_prod, Set.mem_singleton_iff]
        exact ⟨hV u hu, trivial⟩) hinv
    simp only [add_zero] at this
    exact h.flow this
  -- the jumps at the two time-triggered guards, which reset the timer
  have jump01 : ∀ {d : ℝ} {x : X}, H'.Exec d 0 (x, tb) → H'.Exec d 1 (x, 0) := fun h =>
    h.jump ⟨0, {p | p.2 = tb}, fun p => (p.1, 0), 1⟩
      (by simp [hH', DiffInclAutomaton.scalingConversion]) rfl rfl
  have jump12 : ∀ {d : ℝ} {x : X}, H'.Exec d 1 (x, ts) → H'.Exec d 2 (x, 0) := fun h =>
    h.jump ⟨1, {p | p.2 = ts}, fun p => (p.1, 0), 2⟩
      (by simp [hH', DiffInclAutomaton.scalingConversion]) rfl rfl
  rintro x ⟨s, m, hsT, hex⟩
  obtain ⟨hs0, z, hz0, hz, hzs⟩ := DiffInclAutomaton.singleMode_exists_solution_of_exec hf hex
  have e00 : H'.Exec 0 0 (z 0, 0) :=
    DiffInclAutomaton.Exec.init (by simp [hH', DiffInclAutomaton.scalingConversion, hz0])
  -- the state `x` is `z s`, reached after `s ≤ T`
  rcases le_or_gt s tb with hstb | hstb
  · -- `s ≤ t_begin`: the execution stays in `m`
    rcases hs0.eq_or_lt with rfl | hpos
    · exact ⟨(z 0, 0), ⟨0, 0, by linarith [hsT], e00⟩, by simp [← hzs]⟩
    · have e1 := step 0 (w := z) (V := fun u => f (z u)) (r := s) (τ := 0) (d := 0) hpos hz
        (fun u _ => by simp) (fun u hu => by
          simp [hH', DiffInclAutomaton.scalingConversion]
          linarith [hu.2, hstb]) e00
      exact ⟨(z s, 0 + s), ⟨0 + s, 0, by linarith [hsT], e1⟩, by simp [hzs]⟩
  · -- `s > t_begin`: `m` up to `t_begin`, then the scaled solution
    have e1 := step 0 (w := z) (V := fun u => f (z u)) (r := tb) (τ := 0) (d := 0) htb
      (fun u hu => hz u ⟨hu.1, hu.2.trans hstb.le⟩) (fun u _ => by simp) (fun u hu => by
        simp [hH', DiffInclAutomaton.scalingConversion]
        linarith [hu.2]) e00
    simp only [zero_add] at e1
    have e2 := jump01 e1
    set θ : ℝ := s - tb with hθ
    have hθpos : 0 < θ := by linarith
    -- the scaled solution from `z t_begin`, and the clock along it
    obtain ⟨yy, hyy0, hyy⟩ := lipschitzSolution hF (z tb) ts
    have hyyc : ContinuousOn yy (Icc 0 ts) := fun u hu => (hyy u hu).continuousAt.continuousWithinAt
    have hgy : ContinuousOn (fun v => g (yy v)) (Icc 0 ts) := hg.comp_continuousOn hyyc
    have hσc : ContinuousOn (fun τ => ∫ v in (0 : ℝ)..τ, g (yy v)) (Icc 0 ts) := by
      have hint : IntervalIntegrable (fun v => g (yy v)) MeasureTheory.volume 0 ts :=
        (hgy.mono (by simp)).intervalIntegrable_of_Icc hts.le
      simpa [uIcc_of_le hts.le] using
        intervalIntegral.continuousOn_primitive_interval' hint (a := 0)
          (by simp [hts.le])
    -- while the clock has not passed `θ`, the scaled solution is on `z`
    have hrel : ∀ τ ∈ Icc 0 ts, (∫ v in (0 : ℝ)..τ, g (yy v)) ≤ θ →
        yy τ = z (tb + ∫ v in (0 : ℝ)..τ, g (yy v)) := by
      intro τ hτ hle
      obtain ⟨γ, hγ0, hγ, hγt⟩ := scaledSolution_unscale hf hg hτ.1 (fun u _ => hg0 _)
        (hyyc.mono (Icc_subset_Icc le_rfl hτ.2)) fun u hu =>
          (hyy u ⟨hu.1, hu.2.le.trans hτ.2⟩).hasDerivWithinAt
      have hσ0 : 0 ≤ ∫ v in (0 : ℝ)..τ, g (yy v) :=
        intervalIntegral.integral_nonneg hτ.1 fun u _ => hg0 _
      -- `z` shifted by `t_begin` is the solution of `ẋ = f(x)` from `z t_begin`
      have hzs' : ∀ u ∈ Icc 0 (∫ v in (0 : ℝ)..τ, g (yy v)),
          HasDerivAt (fun v => z (tb + v)) (f (z (tb + u))) u := fun u hu => by
        have := (hz (tb + u) ⟨by linarith [hu.1], by linarith [hu.2, hle]⟩).comp_const_add tb u
        simpa using this
      rw [← hγt]
      exact lipschitzSolution_unique hf hγ hzs' (by simp [hγ0, hyy0]) _ ⟨hσ0, le_rfl⟩
    -- the scaled solution as an execution of `H'`, from `(z t_begin, 0)` in `m_scaling`
    have hyystep : ∀ {r d : ℝ}, 0 < r → r ≤ ts → H'.Exec d 1 (z tb, 0) →
        H'.Exec (d + r) 1 (yy r, 0 + r) := fun hr hrts h =>
      step 1 (w := yy) (V := fun u => g (yy u) • f (yy u)) hr
        (fun u hu => hyy u ⟨hu.1, hu.2.trans hrts⟩) (fun u _ => by simp) (fun u hu => by
          simp [hH', DiffInclAutomaton.scalingConversion]
          linarith [hu.2]) (by rw [hyy0]; exact h)
    have hσts : 0 ≤ ∫ v in (0 : ℝ)..ts, g (yy v) :=
      intervalIntegral.integral_nonneg hts.le fun u _ => hg0 _
    by_cases hbig : θ ≤ ∫ v in (0 : ℝ)..ts, g (yy v)
    · -- the clock reaches `θ` before `t_scaling` is spent: `z s` is on the scaled solution
      obtain ⟨τ0, hτ0, hστ0⟩ := intermediate_value_Icc hts.le hσc (a := 0)
        (show θ ∈ Icc (∫ v in (0 : ℝ)..0, g (yy v)) (∫ v in (0 : ℝ)..ts, g (yy v)) by
          simpa using ⟨hθpos.le, hbig⟩)
      have hτ0pos : 0 < τ0 := by
        rcases hτ0.1.eq_or_lt with rfl | h
        · simp at hστ0; linarith
        · exact h
      have e3 := hyystep hτ0pos hτ0.2 e2
      have hpt := hrel τ0 hτ0 (by simp only at hστ0; rw [hστ0])
      simp only at hστ0
      rw [hστ0] at hpt
      exact ⟨(yy τ0, 0 + τ0), ⟨tb + τ0, 1, by linarith [hτ0.2], e3⟩, by
        simp [hpt, hθ, ← hzs]⟩
    · -- the clock stops short: `t_scaling` is spent, and the rest of `z` is done in `m'`
      have hlt : (∫ v in (0 : ℝ)..ts, g (yy v)) < θ := not_le.1 hbig
      -- the full `t_scaling` in `m_scaling`, the jump, then `z` shifted by the clock
      set σ : ℝ := ∫ v in (0 : ℝ)..ts, g (yy v) with hσ
      have e3 := hyystep hts le_rfl e2
      simp only [zero_add] at e3
      have e4 := jump12 e3
      have hyts := hrel ts ⟨hts.le, le_rfl⟩ hlt.le
      have hr : 0 < θ - σ := by linarith
      -- the rest of `z`, in `m'`, is the solution shifted by the clock
      have hw2 : ∀ u ∈ Icc 0 (θ - σ), HasDerivAt (fun v => z (tb + σ + v))
          (f (z (tb + σ + u))) u := fun u hu => by
        have := (hz (tb + σ + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩).comp_const_add
          (tb + σ) u
        simpa using this
      have e5 := step 2 (w := fun v => z (tb + σ + v)) (V := fun u => f (z (tb + σ + u)))
        (r := θ - σ) (τ := 0) (d := tb + ts) hr hw2 (fun u _ => by simp) (fun u _ => by
          simp [hH', DiffInclAutomaton.scalingConversion]) (by simpa [hyts] using e4)
      refine ⟨(z (tb + σ + (θ - σ)), 0 + (θ - σ)), ⟨tb + ts + (θ - σ), 2, ?_, e5⟩, ?_⟩
      · linarith
      · simp only
        rw [← hzs]
        congr 1
        rw [hθ]; ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
