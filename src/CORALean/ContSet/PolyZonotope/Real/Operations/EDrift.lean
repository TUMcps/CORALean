import CORALean.ContSet.PolyZonotope.Real.Operations.EDiff

/-!
# `PolyZonotope.eDrift`

`eDiff` is a symmetric radius, and the drift of one monomial from another is not
symmetric. This splits the radius into a downward and an upward reach, so that
the pair reads `[-fst, snd]` rather than `[-ξ_E, ξ_E]`, and a relaxation can
absorb the difference into its centre instead of paying for it twice.

What makes a reach vanish is a sign that never changes. The factors the two
columns share are `∏_{k ≠ k₀} α_k^{E_{k,i}}`, nonnegative exactly when every
exponent there is even; and `α^A - α^B` keeps one sign when `B = 0`, where it is
`α^A - 1 ≤ 0`, and when `A` and `B` are both even, where it is a difference of
powers of `α² ∈ [0,1]` and the higher exponent gives the smaller. Those two
disjuncts are `[1, Def. 5]`'s parity condition, which is why every edge of the
graph gets a one-sided reach and not only the all-even ones.

Naturals rather than integers, and the same reason as `eDiff`: a count of copies
of a generator is exact in both layers, where a real bound would have to round.

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and
      Its Applications in Formal Neural Network Verification". AAAI, 2024.
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
