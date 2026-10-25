module

public import CORALean.ContSet.Interval.Real.Operations.Atan
public import CORALean.ContSet.Interval.Real.Theorems.MonotoneImageExact

@[expose] public section

/-!
# `Interval.atan` is exactly the image under `Real.arctan`

The arctangent is strictly increasing and continuous on all of `ℝ`, so
`Interval.monotoneImage_exact` applies. No domain condition.

[1, Eq. 6].

## Inputs
* `I` – interval box

## Hypotheses
* none

## Conclusion
* the arctangent box is exactly the image of `I`

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

theorem Interval.atan_exact (I : Interval (Vec ℝ n)) :
    I.atan.construct = (fun x i => Real.arctan (x i)) '' I.construct := by
  exact Interval.monotoneImage_exact Real.arctan (Set.univ) Set.ordConnected_univ
    (fun a _ b _ h => Real.arctan_strictMono h) (Real.continuous_arctan.continuousOn)
    I (fun i => ⟨trivial, trivial⟩)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
