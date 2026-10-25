module

public import CORALean.NN.Layers.Definitions.Sigmoid
public import CORALean.NN.Layers.Definitions.SigmoidNetworks
public import CORALean.NN.Layers.Definitions.SigmoidRelaxation
public import CORALean.NN.Layers.Operations.Activation
public import CORALean.NN.Layers.Operations.Sigmoid
public import CORALean.NN.Layers.Theorems.Real.ActivationPolySigmoidConvergent
public import CORALean.NN.Theorems.EncloseAtInflate

@[expose] public section

/-!
# The loop converges at a single sigmoid layer

Split out of `SigmoidRefinementConverges.lean` (issue #62): both declarations
there were genuinely public and neither used the other outside the file, so
demoting one to `aux_` would have left the file with none — split instead,
one file each, as `MultiLayerRefinementConverges.lean`'s pair does too.

Some schedule is inside any inflation of the exact image, which with
`encloseAt_outer` squeezes the enclosure onto it.

## Inputs
* `n` – layer width
* `X` – input polynomial zonotope
* `ε` – inflation radius

## Hypotheses
* `hε` – radius is positive

## Conclusion
* some schedule encloses the output inside the exact image inflated by the radius
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise ContSet


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The network statement, at a network that exists. -/
theorem aux_sigmoidRefinableNetwork_convergent (n : ℕ) :
    (Real.sigmoidRefinableNetwork n).IsConvergent :=
  ⟨Real.Layer.activationPolySigmoid_convergent n, ⟨1, LipschitzWith.id⟩, trivial⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem exists_schedule_sigmoid_subset {n : ℕ} (X : Real.PolyZonotope (Vec ℝ n)) {ε : ℝ}
    (hε : 0 < ε) : ∃ sch : Schedule,
      construct ((Real.sigmoidRefinableNetwork n).encloseAt sch X)
        ⊆ (Real.sigmoidRefinableNetwork n).image (construct X) + Metric.closedBall 0 ε :=
  (Real.sigmoidRefinableNetwork n).exists_schedule_encloseAt_subset
    (aux_sigmoidRefinableNetwork_convergent n) X ε hε

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
