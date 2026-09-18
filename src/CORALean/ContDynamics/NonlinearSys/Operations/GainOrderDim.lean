import CORALean.Global.Tensor

/-!
# The gain order of one dimension

`[1, Def. 6]` by way of `[1, (40)]`: expand `dᵢ(box(R^∞_abs(h)))` in powers of
`h`, and dimension `i`'s gain order is the exponent at which it first fails to
vanish. `[1, Lemma 3]` supplies the two families read here: `q p i`, the order
in `h` of the coefficient `‖Aᵖ(h)G(h)‖₁,ᵢ`, and `a p i`, that coefficient's
leading vector — `⊤` and `0` where the coefficient vanishes identically.

**A minimum, although `[1, (40)]` prints a maximum.** The limit `h → 0` is
decided by the lowest-order surviving term, and the printed maximum would give a
system with infinitely many non-vanishing coefficients the order `∞`, which
`[1, Def. 6]` reads as *zero* abstraction error. See the paper page's finding.

Stated as "some `a p i` at that order is nonzero" rather than as `[1, (40)]`'s
`Σ_{p+q⁽ᵖ⁾ᵢ=j} ‖a⁽ᵖ⁾ᵢ‖₁ ≠ 0`, the summands being norms. `a p i` is a vector of
`m` generator coefficients, `[1, (36)]`'s "`∈ ℝ∖{0}`" notwithstanding: `‖·‖₁`
there is the 1-norm of a row of `Aᵖ(h)G(h)`, one entry per generator.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


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
