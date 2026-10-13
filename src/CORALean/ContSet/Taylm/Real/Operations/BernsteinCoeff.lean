import CORALean.ContSet.Taylm.Real.Operations.BernsteinEntry
import CORALean.ContSet.Taylm.Real.Taylm

/-!
# `Taylm.bernsteinCoeff`

The Bernstein coefficient of a term list at the multi-index `β`: the tensor of per-variable
matrices `poly2bernstein` [1] applies to the coefficient tensor of the polynomial, written out.
A term `a · ∏ₖ xₖ^(eₖ)` contributes `a · ∏ₖ M(βₖ, eₖ)` with `M = bernsteinEntry`, since the matrix
acts on one variable's axis at a time. (A port of the printed algorithm, with its
transpositions, agrees with this sum on random polynomials in up to four variables and degree
three.)

## References

* [1] `global/functions/helper/sets/contSet/polyZonotope/poly2bernstein.m`, CORA (Sep. 2025).
      No paper behind the rule was confirmed.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The Bernstein coefficient at `β` of the polynomial the terms `L` define, at degree `N`. -/
noncomputable def Taylm.bernsteinCoeff (L : List (ℝ × (Fin n → ℕ))) (N : ℕ)
    (β : Fin n → Fin (N + 1)) : ℝ :=
  (L.map fun a => a.1 * ∏ k, Taylm.bernsteinEntry N (a.2 k) (β k)).sum

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
