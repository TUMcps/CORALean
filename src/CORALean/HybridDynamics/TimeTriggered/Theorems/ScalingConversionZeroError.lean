module

public import CORALean.HybridDynamics.TimeTriggered.Theorems.ScalingConversionContOverapprox
public import CORALean.HybridDynamics.TimeTriggered.Theorems.ScalingConversionSubsetReach

@[expose] public section

/-!
# The scaled automaton: overapproximation, and zero error against the unbounded reachable set

[1, Lemma 2] corrected. For `H_single` with `f` Lipschitz and `H_scaling` with a continuous
`g ≥ 0` whose `g · f` is Lipschitz and `t_begin, t_scaling > 0`: `H_scaling` with time bound
`T + t_scaling` overapproximates `H_single` with time bound `T`, and everything `H_scaling`
reaches, within any time bound, `H_single` reaches, so the error against `Reach(H_single)` is
zero. Against `Reach≤T(H_single)`, as [1, Def. 9] and the statement have it, it is not
(`scalingConversion_not_zeroError`).

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

open scoped NNReal

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 2], corrected: overapproximation at `T + t_scaling`, zero error against `Reach(H)`. -/
theorem DiffInclAutomaton.scalingConversion_zeroError {I : Set X} {f : X → X} {K K' : ℝ≥0}
    (hf : LipschitzWith K f) {g : X → ℝ} (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x)
    (hF : LipschitzWith K' fun x => g x • f x) {tb ts : ℝ} (htb : 0 < tb) (hts : 0 < ts) (T : ℝ) :
    (DiffInclAutomaton.singleMode I f).ContOverapprox T
        (DiffInclAutomaton.scalingConversion I f g tb ts) Prod.fst (T + ts) ∧
      ∀ T', Prod.fst '' (DiffInclAutomaton.scalingConversion I f g tb ts).reachLE T' ⊆
        (DiffInclAutomaton.singleMode I f).reach := by -- --- PROOF ---
  refine ⟨DiffInclAutomaton.scalingConversion_contOverapprox hf hg hg0 hF htb hts T, ?_⟩
  rintro T' x' ⟨⟨x, τ⟩, ⟨d, k, _, h⟩, rfl⟩
  obtain ⟨s, _, hs⟩ := DiffInclAutomaton.scalingConversion_exec_subset_reach hf hg hg0 h
  exact ⟨s, (), hs⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
