module

public import Mathlib.Analysis.ODE.ExistUnique

@[expose] public section

/-!
# Two solutions of a Lipschitz field from one point agree

Mathlib's uniqueness theorem, in the form the execution arguments use: two curves with a
two-sided derivative `f(z)` on `[0, M]` that start together coincide there, for `f` Lipschitz,
[1, Def. 2].

## Inputs
* `f` – vector field
* `K` – Lipschitz constant
* `z` – first curve
* `w` – second curve
* `M` – horizon

## Hypotheses
* `hf` – field is Lipschitz
* `hz` – first curve solves the field
* `hw` – second curve solves the field
* `h0` – the curves start together

## Conclusion
* the curves agree up to the horizon

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

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Solutions of `ẋ = f(x)` on `[0, M]` with the same start agree on `[0, M]`. -/
theorem lipschitzSolution_unique {f : X → X} {K : ℝ≥0} (hf : LipschitzWith K f) {z w : ℝ → X}
    {M : ℝ} (hz : ∀ u ∈ Icc 0 M, HasDerivAt z (f (z u)) u)
    (hw : ∀ u ∈ Icc 0 M, HasDerivAt w (f (w u)) u) (h0 : z 0 = w 0) :
    ∀ u ∈ Icc 0 M, z u = w u :=
  ODE_solution_unique (v := fun _ => f) (a := 0) (b := M) (fun _ => hf)
    (fun u hu => (hz u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hz u ⟨hu.1, hu.2.le⟩).hasDerivWithinAt)
    (fun u hu => (hw u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hw u ⟨hu.1, hu.2.le⟩).hasDerivWithinAt) h0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
