module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Operations.HalderStep
public import CORALean.ContSet.Ellipsoid.Real.Theorems.HalderInvSumPos
public import CORALean.ContSet.Ellipsoid.Real.Theorems.HalderLamSumPos

@[expose] public section

/-!
# Halder's step is continuous on the positive reals

The sums in [1, Eq. 26] are continuous where their denominators `1 + βλᵢ` do not vanish,
and the quotient is of positive numbers, so `g` is continuous at every `β > 0`: the
fixed-point argument of [1, Thm. 3] passes to the limit through it.

## Inputs
* `L` – point

## Hypotheses
* `hlam` – every `λᵢ` positive
* `hL` – `0 < L`

## Conclusion
* the step is continuous at `L`

## References

* [1] A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of
      Minkowski sum of ellipsoids". In Proc. of the 57th IEEE Conference on Decision and
      Control (CDC), pp. 4040-4045, 2018. arXiv:1803.08157.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {ι : Type*} [Fintype ι]
variable {lam : ι → ℝ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The step [1, Eq. 26] is continuous at every `β > 0`. -/
theorem Ellipsoid.halderStep_continuousAt [Nonempty ι] (hlam : ∀ i, 0 < lam i) {L : ℝ}
    (hL : 0 < L) :
    ContinuousAt (Ellipsoid.halderStep lam) L := by -- --- PROOF ---
  have hA : ContinuousOn (Ellipsoid.halderInvSum lam) (Set.Ici 0) := by
    unfold Ellipsoid.halderInvSum
    refine continuousOn_finsetSum _ fun i _ => ?_
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_
    have := hlam i
    have : (0:ℝ) ≤ x := hx
    positivity
  have hB : ContinuousOn (Ellipsoid.halderLamSum lam) (Set.Ici 0) := by
    unfold Ellipsoid.halderLamSum
    refine continuousOn_finsetSum _ fun i _ => ?_
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_
    have := hlam i
    have : (0:ℝ) ≤ x := hx
    positivity
  have : ContinuousOn (Ellipsoid.halderStep lam) (Set.Ici 0) :=
    (hA.div hB fun x hx => (Ellipsoid.halderLamSum_pos hlam hx).ne').sqrt
  exact this.continuousAt (Ici_mem_nhds hL)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
