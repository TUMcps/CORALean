import CORALean.ContSet.PolyZonotope.Real.Operations.Mul
import CORALean.ContSet.PolyZonotope.Real.Theorems.BilinExact

/-!
# `mul` is exactly the product over shared factors

`bilin_exact` at the entrywise product, which is what `mul` is.

What exactness can mean here, and what it cannot: `construct (mul S₁ S₂)` is not
`construct S₁ * construct S₂`. Both sets are functions of one shared factor
vector, so their pointwise product ranges over far fewer points than the product
of the two sets. The claim is about the evaluation map — the result is exactly
the image of the admissible factors under `a ↦ point S₁ a ⊙ point S₂ a`, with
`S₂` read at the same factors through `Fin.cast`.

The independent blocks are not hypothesised away: `point` ignores them, so they
take no part on either side.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open PolyZonotope

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.mul_exact (S₁ S₂ : PolyZonotope (Vec ℝ n)) (hp : S₁.p = S₂.p) :
    (fun a : Fin S₁.p → ℝ => S₁.point a * S₂.point (fun k => a (Fin.cast hp.symm k)))
        '' {a | ∀ k, |a k| ≤ 1}
      = (S₁.mul S₂ hp).construct :=
  PolyZonotope.bilin_exact Entrywise.hadamardLin S₁ S₂ hp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
