import CORALean.NN.Layers.ActivationPolyRefine
import CORALean.NN.Layers.Sigmoid
import CORALean.NN.RefinableNetwork

/-!
# The refinement loop at the sigmoid

`polyRelaxationFamily` asks for a derivative and a bound on it over all of ℝ,
and the sigmoid has both: `hasDerivAt_sigmoid` and `abs_sigmoidDeriv_le_one`,
the second because `σ'` is a product of two sigmoids and each is inside `(0,1)`.

So the whole apparatus closes at a real activation rather than in principle:
`Layer.activationPolySigmoid_convergent` is `RefinableLayer.Convergent` at a
layer someone would actually build, and `sigmoidRefinableNetwork` puts it in a
graph for `Theorems.SigmoidRefinementConverges` to run the network statement on.

The family is CORA's `nn.refine` at the sigmoid [1] with the choice of fit left
open, which is the same freedom `sigmoidPolyRelaxation` already keeps: `sound`
quantifies over the coefficients, so a better `poly_method` is more precise and
never more correct.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

/-- Level `o` fits the sigmoid on `[-o, o]` to within `1 / (o + 1)`. -/
noncomputable def sigmoidPolyFamily : PolyRelaxationFamily sigmoid :=
  polyRelaxationFamily hasDerivAt_sigmoid abs_sigmoidDeriv_le_one

/-- The sigmoid activation layer converges under refinement. -/
theorem Layer.activationPolySigmoid_convergent (n : ℕ) :
    (Layer.activationPolyRefinable (n := n) sigmoidPolyFamily).Convergent :=
  Layer.activationPolyRefinable_convergent hasDerivAt_sigmoid abs_sigmoidDeriv_le_one

/-- That layer as a network, named so the statements about it stay readable. -/
noncomputable def sigmoidRefinableNetwork (n : ℕ) : RefinableNetwork 𝒫𝒵 n n :=
  .cons (Layer.activationPolyRefinable sigmoidPolyFamily) .nil

end CORALean.Real
