module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EDiff

@[expose] public section

/-!
# `PolyZonotope.eDrift`

`eDiff` is a symmetric radius, and the drift of one monomial from another is not symmetric.
This splits it into a downward and an upward reach, so the pair reads `[-fst, snd]` and a
relaxation can absorb the difference into its center. A reach vanishes when a sign never
changes: the shared factors `∏_{k ≠ k₀} α_k^{E_{k,i}}` are nonnegative exactly when every
exponent is even; and `α^A - α^B` keeps one sign when `B = 0` or when `A` and `B` are both even.
Those two disjuncts are `[1, Def. 5]`'s parity condition. Naturals, as for `eDiff`: a count of
copies of a generator is exact in both layers.

## Inputs
* `p` – number of factors
* `h` – number of generators
* `E` – exponent matrix
* `k₀` – factor index
* `i` – first generator index
* `j` – second generator index

## Output
* pair of exponent reaches of the drift

## References

* [1] [T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and Its Applications
      in Formal Neural Network Verification". Proceedings of the AAAI Conference on Artificial
      Intelligence, 2024.](../../../../../../references/2024/ladner-aaai-exponent-relaxation.md)
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- How far the monomial at `i` falls below and rises above the one at `j`, for
two columns agreeing off `k₀`: the drift lies in `[-fst, snd]`. -/
def PolyZonotope.eDrift {p h : ℕ} (E : Fin p → Fin h → ℕ) (k₀ : Fin p) (i j : Fin h) : ℕ × ℕ :=
  if ∀ k, k ≠ k₀ → E k i % 2 = 0 then
    if E k₀ j = 0 ∨ (E k₀ i % 2 = 0 ∧ E k₀ j % 2 = 0 ∧ E k₀ j ≤ E k₀ i) then
      (PolyZonotope.eDiff (E k₀ i) (E k₀ j), 0)
    else if E k₀ i = 0 ∨ (E k₀ i % 2 = 0 ∧ E k₀ j % 2 = 0 ∧ E k₀ i ≤ E k₀ j) then
      (0, PolyZonotope.eDiff (E k₀ i) (E k₀ j))
    else (PolyZonotope.eDiff (E k₀ i) (E k₀ j), PolyZonotope.eDiff (E k₀ i) (E k₀ j))
  else (PolyZonotope.eDiff (E k₀ i) (E k₀ j), PolyZonotope.eDiff (E k₀ i) (E k₀ j))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
