module

public import CORALean.NN.Layers.Definitions.InvSqrt
public import CORALean.NN.Layers.Operations.Basic
public import CORALean.NN.Layers.Operations.RelaxationOfAntitone
public import CORALean.NN.Layers.Operations.RelaxationTighter

@[expose] public section

/-!
# The inverse square root's relaxation over ℝ

[1, Lemma 2] fits one affine `p` and computes `max |f - p|` exactly at its critical points; a
relaxation asks only for a *sound* error at any slope, so that fit is one a caller may supply, and
this is the instance provided. Two relaxations, neither dominating: the range,
`Relaxation.ofAntitone` at `invSqrt` itself, and the derivative bracket from `1 ≤ l` up. On `[1,5]`
the bracket errs by 0.91 against the range's 0.28; on a narrow box it wins, and `tighter` takes the
smaller. A specification: a graph network's layers are ℝ-only, the polynomial zonotope they run on
being the exact one.

## Inputs
* none

## Output
* relaxation of the inverse square root on antitonicity alone

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Total and sound on every box, on antitonicity alone. -/
noncomputable def invSqrtRelaxationRange : Relaxation ℝ :=
  Relaxation.ofAntitone (Enclosure.exact invSqrt)

/-- The derivative's lower end on a box starting at `l`, where `x√x` is smallest. -/
noncomputable def invSqrtDerivLo (l : ℝ) : ℝ := -(2 * l * Real.sqrt l)⁻¹

/-- The derivative's upper end, symmetric in `u`. -/
noncomputable def invSqrtDerivHi (u : ℝ) : ℝ := -(2 * u * Real.sqrt u)⁻¹

/-- The mean-value bracket from the clamp point up, its midpoint as the slope; below, the range. -/
noncomputable def invSqrtRelaxationDeriv : Relaxation ℝ where
  slope l u := if 1 ≤ l then (invSqrtDerivLo l + invSqrtDerivHi u) / 2
      else invSqrtRelaxationRange.slope l u
  offset l u := if 1 ≤ l then invSqrt l - (invSqrtDerivLo l + invSqrtDerivHi u) / 2 * l
      else invSqrtRelaxationRange.offset l u
  error l u := if 1 ≤ l then (invSqrtDerivHi u - invSqrtDerivLo l) * (u - l) / 2
      else invSqrtRelaxationRange.error l u

/-- The smaller error of the two at each box, both sound everywhere so the choice is free. -/
noncomputable def invSqrtRelaxation : Relaxation ℝ :=
  Relaxation.tighter invSqrtRelaxationRange invSqrtRelaxationDeriv

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
