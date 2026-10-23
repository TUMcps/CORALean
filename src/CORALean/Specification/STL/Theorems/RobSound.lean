module

public import CORALean.Specification.STL.Definitions.DiscreteFormula
public import Mathlib.Tactic.Linarith
public import CORALean.Specification.STL.Operations.DFormulaRob

@[expose] public section

/-!
# Positive robustness implies satisfaction

[1, Sec. II-C]: the robust semantics is a real-valued `ρ` with `(x, t) ⊨ φ ≡ ρ^φ(x, t) > 0`. The
two directions that hold: `ρ > 0` implies satisfaction, and satisfaction implies `ρ ≥ 0`, so
`ρ < 0` implies violation. Not the equivalence: at `μ(xₜ) = 0`, `¬μ` holds and `ρ^{¬μ} = 0`,
`STL.DFormula.rob_counterexample`. By induction, `min` and `max` passing both bounds through.

## Inputs
* `x` – trace

## Hypotheses
* none

## Conclusion
* positive robustness implies satisfaction and satisfaction implies nonnegative robustness

## References

* [1] V. Raman, A. Donzé, M. Maasoumy, R. M. Murray, A. Sangiovanni-Vincentelli and
      S. A. Seshia. "Model Predictive Control with Signal Temporal Logic Specifications". In
      Proc. of the 53rd IEEE Conference on Decision and Control (CDC), pp. 81-87, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.DFormula.rob_sound (x : ℕ → X) : -- --- CONCL ---
    ∀ (φ : STL.DFormula X) (t : ℕ),
      (0 < φ.rob x t → φ.Sat x t) ∧ (φ.Sat x t → 0 ≤ φ.rob x t) := by -- --- PROOF ---
  intro φ
  induction φ with
  | pred μ =>
    intro t
    exact ⟨fun h => h, fun h => h.le⟩
  | npred μ =>
    intro t
    simp only [STL.DFormula.rob, STL.DFormula.Sat]
    exact ⟨fun h => by linarith, fun h => by linarith [not_lt.mp h]⟩
  | and φ ψ ihφ ihψ =>
    intro t
    simp only [STL.DFormula.rob, STL.DFormula.Sat, lt_min_iff, le_min_iff]
    exact ⟨fun h => ⟨(ihφ t).1 h.1, (ihψ t).1 h.2⟩, fun h => ⟨(ihφ t).2 h.1, (ihψ t).2 h.2⟩⟩
  | or φ ψ ihφ ihψ =>
    intro t
    simp only [STL.DFormula.rob, STL.DFormula.Sat, lt_max_iff, le_max_iff]
    exact ⟨fun h => h.imp (ihφ t).1 (ihψ t).1, fun h => h.imp (ihφ t).2 (ihψ t).2⟩
  | always a b hab φ ih =>
    -- `inf'` is positive iff every term is, nonnegative if every term is
    intro t
    simp only [STL.DFormula.rob, STL.DFormula.Sat, Finset.lt_inf'_iff, Finset.le_inf'_iff]
    exact ⟨fun h t' ht' => (ih t').1 (h t' ht'), fun h t' ht' => (ih t').2 (h t' ht')⟩
  | eventually a b hab φ ih =>
    intro t
    simp only [STL.DFormula.rob, STL.DFormula.Sat, Finset.lt_sup'_iff, Finset.le_sup'_iff]
    exact ⟨fun ⟨t', ht', h⟩ => ⟨t', ht', (ih t').1 h⟩, fun ⟨t', ht', h⟩ => ⟨t', ht', (ih t').2 h⟩⟩
  | «until» a b hab φ ψ ihφ ihψ =>
    -- the witness `t'` of either side is the witness of the other
    intro t
    simp only [STL.DFormula.rob, STL.DFormula.Sat, Finset.lt_sup'_iff, Finset.le_sup'_iff,
      lt_min_iff, le_min_iff, Finset.lt_inf'_iff, Finset.le_inf'_iff]
    constructor
    · rintro ⟨⟨t', ht'⟩, -, hψ, hφ⟩
      exact ⟨t', ht', (ihψ t').1 hψ, fun s hs => (ihφ s).1 (hφ s hs)⟩
    · rintro ⟨t', ht', hψ, hφ⟩
      exact ⟨⟨t', ht'⟩, Finset.mem_attach _ _, (ihψ t').2 hψ, fun s hs => (ihφ s).2 (hφ s hs)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
