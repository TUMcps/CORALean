module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# `Zonotope.overApproxIndex`, the over-approximation index `Θ`

[1, Sec. 5.3.1]: how much an enclosure `S_red` of `S_orig` gives away, as the `n`-th root of the
volume ratio, `Θ = (V(S_red) / V(S_orig))^{1/n}`, the edge-length ratio of two cubes of those
volumes, so that indices in different dimensions compare. One `let` per volume. The paper weights
both sets by `W = diag(w)` first and then assumes they are already normalized, `W = I`; so does
this. Volumes are Lebesgue measure read as reals; the index is meaningful only where
`V(S_orig) > 0`, which nothing here asks. Real only: a specification, with nothing to round.

## Inputs
* `Sred` – reduced zonotope
* `Sorig` – original zonotope

## Output
* volume ratio to the power `1/n`

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Computing Reachable Sets of Hybrid
      Systems Using a Combination of Zonotopes and Polytopes". Nonlinear
      Analysis: Hybrid Systems, 4(2):233-249, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. 5.3.1]'s `Θ = (V(S_red) / V(S_orig))^{1/n}`, at `W = I`. -/
noncomputable def Zonotope.overApproxIndex (Sred Sorig : Zonotope (Vec ℝ n)) : ℝ :=
  let Vred : ℝ := (MeasureTheory.volume Sred.construct).toReal
  let Vorig : ℝ := (MeasureTheory.volume Sorig.construct).toReal
  (Vred / Vorig) ^ ((n : ℝ)⁻¹)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
