module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Theorems.AntitoneImageExact

@[expose] public section

/-!
# `Interval.acos` is exactly the image under `Real.arccos`

The arccosine is strictly decreasing on `[-1, 1]`, so the corners swap, so
`Interval.antitoneImage_exact` applies. CORA returns a complex or NaN result outside `[-1, 1]`;
here the domain is a hypothesis, both corners in `[-1, 1]`.

[1, Eq. 6], its first case.

## Inputs
* `I` – interval box

## Hypotheses
* `hI` – bounds within `[-1, 1]`

## Conclusion
* the arccosine box is exactly the image of `I`

## References

* [1] M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". ARCH16. 3rd
      International Workshop on Applied Verification for Continuous and Hybrid Systems, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.acos_exact (I : Interval (Vec ℝ n))
    (hI : ∀ i, (-1 ≤ I.inf i ∧ I.inf i ≤ 1) ∧ (-1 ≤ I.sup i ∧ I.sup i ≤ 1)) :
    I.acos.construct = (fun x i => Real.arccos (x i)) '' I.construct := by
  exact Interval.antitoneImage_exact Real.arccos (Set.Icc (-1) 1) Set.ordConnected_Icc
    (Real.strictAntiOn_arccos) (Real.continuous_arccos.continuousOn) I (hI)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
