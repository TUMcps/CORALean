module

public import CORALean.ContSet.ConZonotope.Float.ConZonotope

@[expose] public section

/-!
# `ConZonotope.liftEq` over a floating-point scalar

The zonotope CORA's `@conZonotope/reduce` reduces [1, Sec. 4.3], on the stored floats:
generators `[G; Aₑ]` in `𝕋^{n + mₑ}`, the equality rows copied as they are (entry `Aₑ i j` is
generator `j`'s lower coordinate `i`), so nothing is rounded. As over ℝ, with two differences.
Only the zonotope is returned, the inequality rows being `reduceLiftBy`'s to carry; and the
lower center is `0`, not `-bₑ`, because the right-hand side `bₑ` is an interval here: the row
`Aₑ β ∈ bₑ` keeps it on the constraint, where the lifted coordinate is `Aₑ β` itself. The
error box is the first operand's, with `0` below, and `reduceBy` never reads it.

## Inputs
* `cZ` – float constrained zonotope

## Output
* zonotope with the equality rows as extra coordinates

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes: A new
      tool for set-based estimation and fault detection". Automatica, 2016.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Not the polytope's work (conversion): the lifted zonotope [G; Aₑ] of Scott et al. 2016, Sec.
4.3, a `Zonotope` whose lower generator rows are the equality rows. -/
def ConZonotope.liftEq (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : Zonotope (Vec 𝕋 (n + cZ.P.me)) where
  h := cZ.h
  c := Fin.append cZ.c fun _ => zero
  G := fun j => Fin.append (cZ.G j) fun i => cZ.P.Ae i j
  I_error := ⟨Fin.append cZ.I_error.inf fun _ => zero, Fin.append cZ.I_error.sup fun _ => zero⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
