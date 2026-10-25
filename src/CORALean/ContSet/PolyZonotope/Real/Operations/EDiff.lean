module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

@[expose] public section

/-!
# `PolyZonotope.eDiff`

How far two powers of the same factor can drift apart on `[-1,1]`: [1] defines it as
`max_{x ∈ [-1,1]} |x^a - x^b|`, and a relaxation is sound at any *upper bound* on that
maximum. This is the coarse bound parity alone gives: equal parity keeps `x^a` and `x^b` on one
side of zero, where they differ by at most one, and otherwise by at most two. The bound is
integral, stated over ℕ, which keeps the float layer exact in it (a repeated sum). The maximum
itself, real-valued, is `eDiffTight`; at `a = 3, b = 1` this bound is `1` where it is `≈ 0.385`.

## Inputs
* `a` – first exponent
* `b` – second exponent

## Output
* bound on the exponent difference

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and Its Applications in
      Formal Neural Network Verification". Proceedings of the AAAI Conference on Artificial
      Intelligence, 2024.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- An upper bound on `max_{x ∈ [-1,1]} |x^a - x^b|`, [1, Prop. 3]. -/
def PolyZonotope.eDiff (a b : ℕ) : ℕ :=
  if a = b then 0 else if a % 2 = b % 2 then 1 else 2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
