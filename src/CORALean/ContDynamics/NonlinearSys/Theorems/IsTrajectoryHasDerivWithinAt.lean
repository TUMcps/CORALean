module

public import CORALean.ContDynamics.NonlinearSys.NonlinearSys
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# A Carathéodory run with a continuous field is classical

On a closed interval `[a, b] ∋ 0`, a run whose field `t ↦ f(x t, u t)` is continuous has that
field as its derivative at every point, within the interval: the converse of
`IsTrajectory.of_hasDerivWithinAt`. A continuous input under a continuous right-hand side, as
[1, Def. 1]'s Lipschitz-continuous inputs are, gives such a field.

## Inputs
* `sys` – system
* `a` – interval start
* `b` – interval end
* `R₀` – initial set
* `U` – input set
* `x` – state trajectory
* `u` – input trajectory
* `y` – output trajectory
* `t` – time

## Hypotheses
* `traj` – trajectory of the system
* `h0` – zero in interval
* `hf` – field continuous along run
* `ht` – time in interval

## Conclusion
* the state has the field as derivative at the time

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Nonlinear Systems with
      Uncertain Parameters using Conservative Linearization". In Proc. of the 47th IEEE
      Conference on Decision and Control (CDC), 2008, pp. 4042-4048.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet MeasureTheory intervalIntegral

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The integral equation on `[a, b] ∋ 0`, its integrand continuous there, gives the derivative
within `[a, b]` at every point. -/
theorem aux_hasDerivWithinAt_of_eq_add_integral {a b : ℝ} {x g : ℝ → Vec ℝ n}
    (h0 : (0:ℝ) ∈ Set.Icc a b) (hg : ContinuousOn g (Set.Icc a b))
    (hx : ∀ t ∈ Set.Icc a b, x t = x 0 + ∫ s in (0:ℝ)..t, g s) {t : ℝ}
    (ht : t ∈ Set.Icc a b) : -- --- CONCL ---
    HasDerivWithinAt x (g t) (Set.Icc a b) t := by -- --- PROOF ---
  haveI : Fact (t ∈ Set.Icc a b) := ⟨ht⟩
  have hint : IntervalIntegrable g volume 0 t :=
    (hg.mono (Set.OrdConnected.uIcc_subset inferInstance h0 ht)).intervalIntegrable
  have hF : HasDerivWithinAt (fun r => ∫ s in (0:ℝ)..r, g s) (g t) (Set.Icc a b) t :=
    integral_hasDerivWithinAt_right hint
      (hg.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hg t ht)
  exact (hF.const_add (x 0)).congr (fun r hr => hx r hr) (hx t ht)


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run on `[a, b] ∋ 0` whose field is continuous there has it as its derivative. -/
theorem NonlinearSys.IsTrajectory.hasDerivWithinAt {sys : NonlinearSys n m} {a b : ℝ}
    {R₀ : S n} {U : S m} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m}
    {y : ℝ → Vec ℝ sys.q} (traj : sys.IsTrajectory (Set.Icc a b) R₀ U x u y)
    (h0 : (0:ℝ) ∈ Set.Icc a b)
    (hf : ContinuousOn (fun t => sys.f (x t) (u t)) (Set.Icc a b)) {t : ℝ}
    (ht : t ∈ Set.Icc a b) :
    HasDerivWithinAt x (sys.f (x t) (u t)) (Set.Icc a b) t :=
  aux_hasDerivWithinAt_of_eq_add_integral h0 hf traj.flow ht

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
