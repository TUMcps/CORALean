import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPolySortP

/-!
# `PolyZonotope.evalPolySort`

[1, Alg. 2]: the polynomial evaluated by powers rather than by Horner's rule —
`PZ^i` computed by repeated `sq`, each sorted and merged, and the `o` terms
summed with `sortPlus`. Coefficients lowest degree first and one vector per
degree, as `evalPoly` takes them, so every coordinate carries its own
polynomial.

`evalPoly` is Horner and reaches the same value by a different route, which is
what [1, Alg. 2] buys: this one keeps the exponent matrix sorted throughout and
never calls `compact`.

The independent block is not part of the claim: [1, Alg. 2] is given a
`PZ = ⟨c, G, [], E⟩` and so assumes it empty, `point` ignores it, and of the
terms here only the degree-one one carries it through at all. A caller who
needs those coefficients to count runs `dependent` on `pZ` first, as
`evalPoly`'s callers do.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       12-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2], coefficients lowest degree first. -/
noncomputable def PolyZonotope.evalPolySort (pZ : PolyZonotope (Vec ℝ n))
    (coeffs : List (Vec ℝ n)) : PolyZonotope (Vec ℝ n) := (pZ.evalPolySortP coeffs).1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
