module

public import CORALean.ContSet.Taylm.Real.Operations.Sin
public import CORALean.ContSet.Taylm.Real.Theorems.TaylorScaled
public import CORALean.Global.ElementaryDerivBounds

@[expose] public section

/-!
# `Taylm.sin` keeps the `(n+1)`-st order scaling

[1, Thm. 1], eq. (2.9), at [1, Def. 3 (sin)]: every derivative of `sin` is at most one, so both the
coefficients `sin⁽ᵏ⁾(c)/k!` and the derivative bound are, whatever `h`.

## Inputs
* `T` – Taylor model
* `h` – domain radius
* `C` – scaling constant

## Hypotheses
* `h0` – radius is positive
* `h1` – radius is at most one
* `hT` – the model is scaled by the constant

## Conclusion
* the sine model is scaled by a constant built from it

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.sin_scaled {T : Taylm n} {h C : ℝ} (h0 : 0 < h) (h1 : h ≤ 1) (hT : T.Scaled h C) :
    T.sin.Scaled h (1 * ∑ k : Fin (T.maxOrder + 1), (8 * C) ^ (k : ℕ)
      + 1 * (2 * C) ^ (T.maxOrder + 1)) := by -- --- PROOF ---
  refine Taylm.taylor_scaled h0 h1 hT (fun k _ => ?_) (by simp)
  -- a derivative at most one, divided by `k! ≥ 1`
  have hf : (1 : ℝ) ≤ (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rw [abs_div, Nat.abs_cast]
  exact le_trans (div_le_self (abs_nonneg _) hf) (abs_iteratedDeriv_sin_le k _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
