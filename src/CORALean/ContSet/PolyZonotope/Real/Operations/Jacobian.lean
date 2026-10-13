import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# `PolyZonotope.jacobian`

CORA's `@polyZonotope/jacobian`: the derivative of every dimension of the polynomial zonotope with
respect to one of its identifiers, as a polynomial zonotope again. A dependent generator `Gᵢ αᴱⁱ`
differentiates to `eₖᵢ Gᵢ αᴱⁱ⁻ᵉᵏ`: the generator is scaled by the exponent of the factor `k` and
that exponent drops by one. The independent block does not depend on any factor and is dropped, and
the centre is `0` (CORA moves the generators whose exponents become all zero into the centre; here
they stay as constant generators, which changes the representation and not the point).

An identifier is an index `k` of `Fin p`; the cell array CORA returns is this family over the
identifiers in `id_diff`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The derivative with respect to the factor `k`. -/
def PolyZonotope.jacobian (pZ : PolyZonotope α) (k : Fin pZ.p) : PolyZonotope α where
  p := pZ.p
  h := pZ.h
  q := 0
  c := 0
  G := fun i => (pZ.E k i : ℝ) • pZ.G i
  E := fun k' i => if k' = k then pZ.E k i - 1 else pZ.E k' i
  GI := Fin.elim0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
