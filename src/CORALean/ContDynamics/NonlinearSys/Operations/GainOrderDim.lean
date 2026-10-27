module

public import CORALean.Global.Tensor
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The gain order of one dimension

`[1, Def. 6]` by way of `[1, (40)]`: expand `dᵢ(box(R^∞_abs(h)))` in powers of `h`, and dimension
`i`'s gain order is the exponent at which it first fails to vanish. `[1, Lemma 3]` supplies the
two families read here: `q p i`, the order in `h` of the coefficient `‖Aᵖ(h)G(h)‖₁,ᵢ`, and
`a p i`, its leading vector — `⊤` and `0` where the coefficient vanishes identically. **A minimum,
although `[1, (40)]` prints a maximum.** The limit `h → 0` is decided by the lowest-order
surviving term, and the printed maximum would give a system with infinitely many non-vanishing
coefficients the order `∞`, which `[1, Def. 6]` reads as *zero* abstraction error. Stated as "some
`a p i` at that order is nonzero", the summands being norms.

## Inputs
* `q` – orders of the coefficients
* `a` – leading vectors of the coefficients
* `i` – dimension

## Output
* the least order carrying a nonzero coefficient

## References

* [1] [M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive Reachability Algorithms
      for Nonlinear Systems Using Abstraction Error Analysis". Nonlinear Analysis: Hybrid Systems,
      2022.](../../../../../references/2022/wetzlinger-nahs-abstraction-error.md)
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `qᵢ`: the least order `p + q⁽ᵖ⁾ᵢ` carrying a nonzero coefficient, and `⊤`
when none does. -/
noncomputable def gainOrderDim (q : ℕ → Fin n → ℕ∞) (a : ℕ → Fin n → Vec ℝ m)
    (i : Fin n) : ℕ∞ :=
  sInf {j : ℕ∞ | ∃ p : ℕ, (p : ℕ∞) + q p i = j ∧ a p i ≠ 0}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
