import CORALean.HybridDynamics.TimeTriggered.Theorems.HasDerivWithinAtIciOfDeriv
import CORALean.HybridDynamics.TimeTriggered.Theorems.LipschitzSolutionUnique

/-!
# A continuous successor of a Lipschitz flow is the solution

[1, Def. 4] gives a continuous successor as a differentiable `g` on `[0, t]` with `ġ = f(g)` on
`(0, t)` only. For `f` Lipschitz it agrees on all of `[0, t]` with any solution that starts where
it does: the right derivative at `0` is `f(g 0)` by `hasDerivWithinAt_Ici_of_deriv_eq`.

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

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A piece `g` with `ġ = f(g)` on `(0, t)` equals a solution `w` of `ẋ = f(x)` it starts with. -/
theorem lipschitzPiece_eq {f : X → X} {K : ℝ≥0} (hf : LipschitzWith K f) {g w : ℝ → X} {t : ℝ}
    (ht : 0 < t) (hgd : DifferentiableOn ℝ g (Icc 0 t))
    (hgder : ∀ u ∈ Ioo 0 t, deriv g u = f (g u)) (hw : ∀ u ∈ Icc 0 t, HasDerivAt w (f (w u)) u)
    (h0 : g 0 = w 0) : ∀ u ∈ Icc 0 t, g u = w u :=
  ODE_solution_unique (v := fun _ => f) (a := 0) (b := t) (fun _ => hf) hgd.continuousOn
    (hasDerivWithinAt_Ici_of_deriv_eq hf.continuous ht hgd hgder)
    (fun u hu => (hw u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hw u ⟨hu.1, hu.2.le⟩).hasDerivWithinAt) h0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
