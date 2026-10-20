module

public import Mathlib.Analysis.ODE.ExistUnique
public import CORALean.HybridDynamics.TimeTriggered.Operations.SingleMode
public import CORALean.HybridDynamics.TimeTriggered.Theorems.HasDerivWithinAtIciOfDeriv
public import CORALean.HybridDynamics.TimeTriggered.Theorems.LipschitzSolution

@[expose] public section

/-!
# An execution of the single-mode automaton follows a solution

For `f` Lipschitz, an execution of `H_single` of duration `s` ends where a solution of
`ẋ = f(x)` from an initial state is at time `s`, [1, Sec. 3.2]. The executions are chains of
continuous successors, each with a differentiable `g` that is a solution on its own piece, so the
statement is proved in the universal form, every solution from that initial state, which is what
the chain needs: the next piece is the shifted solution, by uniqueness.

## Inputs
* `I` – initial states
* `f` – flow
* `K` – Lipschitz constant
* `s` – duration
* `m` – mode
* `x` – end state

## Hypotheses
* `hf` – flow is Lipschitz
* `h` – execution of the single mode

## Conclusion
* a solution from an initial state reaches the end state

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

open Set
open scoped NNReal

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [CompleteSpace X] in
/-- Every solution from the initial state of an execution is at its end after its duration. -/
theorem aux_exec_unique {I : Set X} {f : X → X} {K : ℝ≥0} (hf : LipschitzWith K f) {s : ℝ}
    {m : Unit} {x : X} (h : (DiffInclAutomaton.singleMode I f).IsExec s m x) : -- --- CONCL ---
    0 ≤ s ∧ ∃ x₀ ∈ I, ∀ z : ℝ → X, z 0 = x₀ → (∀ u ∈ Icc 0 s, HasDerivAt z (f (z u)) u) →
      z s = x := by -- --- PROOF ---
  -- the induction over the execution, the flow step by uniqueness of the shifted solution
  induction h with
  | init hx => exact ⟨le_rfl, _, hx, fun z hz _ => hz⟩
  | jump _ e he => simp [DiffInclAutomaton.singleMode] at he
  | flow h hf' ih =>
    rename_i d t _ x x'
    obtain ⟨hd0, x₀, hx₀, hz⟩ := ih
    obtain ⟨ht, g, hgd, hg0, hgt, hgi⟩ := hf'
    refine ⟨by linarith, x₀, hx₀, fun z hz0 hzd => ?_⟩
    have hzx : z d = x := hz z hz0 fun u hu => hzd u ⟨hu.1, hu.2.trans (by linarith)⟩
    -- the piece `g` and the shifted `z` solve the same ODE from `x` on `[0, t]`
    have hgder := hasDerivWithinAt_Ici_of_deriv_eq hf.continuous ht hgd fun u hu => by
      simpa [DiffInclAutomaton.singleMode] using (hgi u hu).2
    have hw : ∀ u ∈ Icc 0 t, HasDerivAt (fun v => z (d + v)) (f (z (d + u))) u := fun u hu => by
      have := (hzd (d + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩).comp_const_add d u
      simpa using this
    have heq := ODE_solution_unique (v := fun _ => f) (a := 0) (b := t) (fun _ => hf)
      hgd.continuousOn (fun u hu => hgder u hu)
      (fun u hu => (hw u hu).continuousAt.continuousWithinAt) (fun u hu =>
        (hw u ⟨hu.1, hu.2.le⟩).hasDerivWithinAt) (by simp [hg0, hzx])
    rw [← hgt, heq ⟨ht.le, le_rfl⟩]


-- =======================================  MAIN THEOREM  ======================================= --

/-- An execution of `H_single` of duration `s` ends at a solution of `ẋ = f(x)` at time `s`. -/
theorem DiffInclAutomaton.singleMode_exists_solution_of_isExec {I : Set X} {f : X → X} {K : ℝ≥0}
    (hf : LipschitzWith K f) {s : ℝ} {m : Unit} {x : X}
    (h : (DiffInclAutomaton.singleMode I f).IsExec s m x) :
    0 ≤ s ∧ ∃ z : ℝ → X, z 0 ∈ I ∧ (∀ u ∈ Icc 0 s, HasDerivAt z (f (z u)) u) ∧ z s = x := by
  obtain ⟨hs, x₀, hx₀, hz⟩ := aux_exec_unique hf h
  obtain ⟨z, hz0, hzd⟩ := lipschitzSolution hf x₀ s
  exact ⟨hs, z, hz0 ▸ hx₀, hzd, hz z hz0 hzd⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
