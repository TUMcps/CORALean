import CORALean.ContSet.PolyZonotope.Real.Operations.BilinE
import CORALean.ContSet.PolyZonotope.Real.Operations.BilinG

/-!
# `PolyZonotope.bilin`

Any bilinear map applied to two polynomial zonotopes over the *same* factors.
The result is again a polynomial zonotope, exactly, because `f` distributes
over the two sums and the product of two monomials is the monomial at the added
exponent column — which is what shared factors buy and what an unshared product
cannot have.

Sharing is a hypothesis rather than a shape in the signature: `p` is a field, so
two `PolyZonotope`s cannot be made to share it definitionally without
destructuring one of them. `Fin.cast` then reads `pZ₂`'s exponent matrix at
`pZ₁`'s factor indices, which moves no data — identity here is positional.

The independent blocks take no part, a pairing of two free coefficients not
being one, so `bilin` is a claim about `point`; a caller who needs those
coefficients to count runs `dependent` first, and once, so that repeated
pairings keep the freed ones identified.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β γ : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
  [AddCommGroup γ] [Module ℝ γ]


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.bilin (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (pZ₁ : PolyZonotope α) (pZ₂ : PolyZonotope β)
    (hp : pZ₁.p = pZ₂.p) : PolyZonotope γ where
  p := pZ₁.p
  h := (pZ₁.h + 1) * (pZ₂.h + 1)
  q := 0
  c := 0
  G := PolyZonotope.bilinG f pZ₁ pZ₂
  E := PolyZonotope.bilinE pZ₁ pZ₂ hp
  GI := Fin.elim0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
