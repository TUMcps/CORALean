import CORALean.ContSet.PolyZonotope.Real.Operations.Mul
import CORALean.ContSet.PolyZonotope.Real.Theorems.BilinExact

/-!
# `mul` is exactly the product over shared factors

At one dimension, this is [1, Prop. 2.9], the same reading `Mul.lean` gives the
operation itself; `mul` and this exactness proof generalize it coordinatewise.

`bilin_exact` at the entrywise product, which is what `mul` is.

What exactness can mean here, and what it cannot: `construct (mul pZ₁ pZ₂)` is not
`construct pZ₁ * construct pZ₂`. Both sets are functions of one shared factor
vector, so their pointwise product ranges over far fewer points than the product
of the two sets. The claim is about the evaluation map — the result is exactly
the image of the admissible factors under `a ↦ point pZ₁ a ⊙ point pZ₂ a`, with
`pZ₂` read at the same factors through `Fin.cast`.

The independent blocks are not hypothesised away: `point` ignores them, so they
take no part on either side.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   21-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open PolyZonotope

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.mul_exact (pZ₁ pZ₂ : PolyZonotope (Vec ℝ n)) (hp : pZ₁.p = pZ₂.p) :
    (fun a : Fin pZ₁.p → ℝ => pZ₁.point a * pZ₂.point (fun k => a (Fin.cast hp.symm k)))
        '' {a | ∀ k, |a k| ≤ 1}
      = (pZ₁.mul pZ₂ hp).construct :=
  PolyZonotope.bilin_exact Entrywise.hadamardLin pZ₁ pZ₂ hp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
