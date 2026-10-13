module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

@[expose] public section

/-!
# `PolyZonotope.subsMul`

CORA's `priv_multiply`: the product of two sums of monomials, one term per pair. A term is a
coefficient and an exponent vector over the factors of `pZin`; `subs` expands powers of the output
polynomials with it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The product of two sums of monomials, one term per pair. -/
noncomputable def PolyZonotope.subsMul {p : ℕ} (A B : List (ℝ × (Fin p → ℕ))) :
    List (ℝ × (Fin p → ℕ)) :=
  A.flatMap fun s => B.map fun t => (s.1 * t.1, s.2 + t.2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
