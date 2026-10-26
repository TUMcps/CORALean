module

public import CORALean.ContSet.Interval.Real.Operations.Atanh
public import CORALean.ContSet.Interval.Real.Theorems.MonotoneImageExact

@[expose] public section

/-!
# `Interval.atanh` is exactly the image under `Real.artanh`

The inverse hyperbolic tangent is strictly increasing and continuous on `(-1, 1)`, so
`Interval.monotoneImage_exact` applies. CORA returns a complex result outside `[-1, 1]` and
`±Inf` at the endpoints; here the domain is a hypothesis, both corners in `(-1, 1)`. Mathlib has
no continuity lemma for `artanh`, so `aux_continuousOn_artanh` proves it from
`artanh x = ½ log ((1 + x) / (1 - x))`.

[1, Eq. 8], its first case.

## Inputs
* `I` – interval box

## Hypotheses
* `hI` – bounds strictly inside `(-1, 1)`

## Conclusion
* the inverse hyperbolic tangent box is exactly the image of `I`

## References

* [1] M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". ARCH16. 3rd
      International Workshop on Applied Verification for Continuous and Hybrid Systems, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- On `(-1, 1)`, `artanh` is `½ log ((1 + x) / (1 - x))`, a composite of continuous maps. -/
private theorem Interval.aux_continuousOn_artanh : -- --- CONCL ---
    ContinuousOn Real.artanh (Set.Ioo (-1) 1) := by -- --- PROOF ---
  have h : ContinuousOn (fun x : ℝ => 1 / 2 * Real.log ((1 + x) / (1 - x))) (Set.Ioo (-1) 1) := by
    refine continuousOn_const.mul (ContinuousOn.log ?_ ?_)
    · exact (continuousOn_const.add continuousOn_id).div
        (continuousOn_const.sub continuousOn_id) (fun x hx => by linarith [hx.2])
    · intro x hx
      exact (div_pos (by linarith [hx.1]) (by linarith [hx.2])).ne'
  exact h.congr (fun x hx => Real.artanh_eq_half_log ⟨hx.1.le, hx.2.le⟩)


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.atanh_exact (I : Interval (Vec ℝ n))
    (hI : ∀ i, (-1 < I.inf i ∧ I.inf i < 1) ∧ (-1 < I.sup i ∧ I.sup i < 1)) :
    I.atanh.construct = (fun x i => Real.artanh (x i)) '' I.construct := by
  exact Interval.monotoneImage_exact Real.artanh (Set.Ioo (-1) 1) Set.ordConnected_Ioo
    Real.strictMonoOn_artanh Interval.aux_continuousOn_artanh I hI

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
