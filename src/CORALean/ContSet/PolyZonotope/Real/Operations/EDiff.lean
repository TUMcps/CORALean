module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

@[expose] public section

/-!
# `PolyZonotope.eDiff`

How far two powers of the same factor can drift apart on `[-1,1]`: `[1]` defines
it as `max_{x ∈ [-1,1]} |x^a - x^b|`, and a relaxation is sound at any *upper
bound* on that maximum, never needing the maximum itself. This is the coarse
bound parity alone gives — equal parity keeps `x^a` and `x^b` on one side of
zero, where they differ by at most one, and otherwise each stays in `[-1,1]` and
they differ by at most two.

The bound is integral, so it is stated over ℕ and coerced where a scalar is
wanted. That is what keeps the float layer exact in it: scaling a generator by a
natural number is a repeated sum there, and the exponents it reads are exact in
both layers. The maximum itself is real-valued, `eDiffTight`, which `relaxWidth`
reads over ℝ; this bound stays where a count of copies is wanted.

The maximum itself is `(b/a)^{b/(a-b)} (1 - b/a)` on `[0,1]`, so at `a = 3,
b = 1` this bound is `1` where the maximum is `≈ 0.385`.

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and
      Its Applications in Formal Neural Network Verification". AAAI, 2024.
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
