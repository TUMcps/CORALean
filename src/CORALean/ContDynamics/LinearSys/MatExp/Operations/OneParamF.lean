module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.OneParamD

@[expose] public section

/-!
# `MatExp.oneParamF`

The auxiliary matrices `F_i^{(l)}` of [1, Thm. 1], the coefficient of `βˡ` in `(C + βG)ⁱ`, by the
printed recursion: `F_0^{(1)} = 0`, and for `i ≥ 1`
`F_i^{(1)} = D_{i-1} G + F_{i-1}^{(1)} C`, `F_i^{(l)} = F_{i-1}^{(l-1)} G + F_{i-1}^{(l)} C` for
`l = 2 … i - 1`, `F_i^{(i)} = F_{i-1}^{(i-1)} G`. Outside `1 ≤ l ≤ i` it is `0`. At `i = 1` the
rules for `l = 1` and `l = i` both apply; the second would need `F_0^{(0)}`, which [1] leaves
undefined, and the first is taken, giving `F_1^{(1)} = G`, which is the coefficient.

## Inputs
* `C` – first matrix
* `G` – second matrix

## Output
* sum of products of the two matrices with a given number of second factors

## References

* [1] M. Althoff and J. M. Dolan. "Reachability Computation of Low-Order Models for the Safety
      Verification of High-Order Road Vehicle Models". In Proc. of the American Control
      Conference, pp. 3559-3566, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def MatExp.oneParamF (C G : Mat ℝ n n) : ℕ → ℕ → Mat ℝ n n
  | 0, _ => 0  -- `F_0^{(1)} = 0`
  | i + 1, l =>
    if l = 1 then MatExp.oneParamD C i * G + MatExp.oneParamF C G i 1 * C  -- `F_i^{(1)}`
    else if 2 ≤ l ∧ l < i + 1 then
      MatExp.oneParamF C G i (l - 1) * G + MatExp.oneParamF C G i l * C  -- `F_i^{(l)}`
    else if l = i + 1 then MatExp.oneParamF C G i i * G  -- `F_i^{(i)}`
    else 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
