import CORALean.ContSet.ConZonotope.Float.ConZonotope

/-!
# `ConZonotope.liftEq` over a floating-point scalar

The zonotope CORA's `@conZonotope/reduce` reduces [1, Sec. 4.3], on the stored floats:
generators `[G; Aₑ]` in `𝕋^{n + mₑ}`, the equality rows copied as they are (entry `Aₑ i j` is
generator `j`'s lower coordinate `i`), so nothing is rounded. As over ℝ, with two differences.
Only the zonotope is returned, the inequality rows being `reduceLiftBy`'s to carry; and the
lower centre is `0`, not `-bₑ`, because the right-hand side `bₑ` is an interval here: the row
`Aₑ β ∈ bₑ` keeps it on the constraint, where the lifted coordinate is `Aₑ β` itself. The
error box is the first operand's, with `0` below, and `reduceBy` never reads it.

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.liftEq (cZ : ConZonotope 𝕋 n) : Zonotope 𝕋 (n + cZ.P.me) where
  h := cZ.h
  c := Fin.append cZ.c fun _ => zero
  G := fun j => Fin.append (cZ.G j) fun i => cZ.P.Ae i j
  E := ⟨Fin.append cZ.E.inf fun _ => zero, Fin.append cZ.E.sup fun _ => zero⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
