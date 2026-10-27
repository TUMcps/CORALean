module

public import CORALean.ContSet.Interval.Real.Operations.Acosh
public import CORALean.ContSet.Interval.Real.Theorems.MonotoneImageExact

@[expose] public section

/-!
# `Interval.acosh` is exactly the image under `Real.arcosh`

The inverse hyperbolic cosine is strictly increasing and continuous for `1 ≤ x`, so
`Interval.monotoneImage_exact` applies. CORA returns a complex or NaN result below `1`; here the
domain is a hypothesis, both corners at least `1`.

[1, Eq. 8], its first case.

## Inputs
* `I` – interval box

## Hypotheses
* `hI` – bounds at least one

## Conclusion
* the inverse hyperbolic cosine box is exactly the image of `I`

## References

* [1] [M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". ARCH16.
      3rd International Workshop on Applied Verification for Continuous and Hybrid Systems,
      2017.](../../../../../../references/2017/althoff-arch-interval-arithmetic.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.acosh_exact (I : Interval (Vec ℝ n))
    (hI : ∀ i, 1 ≤ I.inf i ∧ 1 ≤ I.sup i) :
    I.acosh.construct = (fun x i => Real.arcosh (x i)) '' I.construct := by
  exact Interval.monotoneImage_exact Real.arcosh (Set.Ici 1) Set.ordConnected_Ici
    (Real.strictMonoOn_arcosh.mono (fun _ hx => Set.mem_Ioi.2 (lt_of_lt_of_le one_pos hx)))
    Real.continuousOn_arcosh I hI

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
