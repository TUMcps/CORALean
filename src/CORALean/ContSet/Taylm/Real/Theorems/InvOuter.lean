module

public import CORALean.ContSet.Taylm.Real.Operations.Inv
public import CORALean.ContSet.Taylm.Real.Theorems.TaylorOuter
public import Mathlib.Analysis.Calculus.Deriv.ZPow

@[expose] public section

/-!
# `Taylm.inv` encloses `1 / f`

[1, Def. 3 (inverse)] under its condition that `0` is outside the range, read as the hull of
the center and the range bound lying strictly on one side of zero. `|ξ| ≥ m` on that hull, so
`(N+1)! / |ξ|ᴺ⁺²` is at most `(N+1)! / mᴺ⁺²`.

## Inputs
* `T` – Taylor model
* `f` – enclosed function

## Hypotheses
* `h` – the model encloses the function
* `hside` – the range stays on one side of zero

## Conclusion
* the result encloses the reciprocal of the function

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion Methods".
      International Journal of Pure and Applied Mathematics, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.inv_outer {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    (hside : 0 < min T.constCoef T.bounds.inf ∨ max T.constCoef T.bounds.sup < 0) : -- --- CONCL ---
    T.inv.Encloses fun t => (f t)⁻¹ := by -- --- PROOF ---
  set lo := min T.constCoef T.bounds.inf
  set hi := max T.constCoef T.bounds.sup
  -- every point of the hull is at least `m` away from zero, and `m > 0`
  have hm : ∀ ξ ∈ Set.Icc lo hi, 0 < max lo (-hi) ∧ max lo (-hi) ≤ |ξ| := by
    intro ξ hξ
    rcases hside with hpos | hneg
    · have : max lo (-hi) = lo := max_eq_left (by linarith [hξ.1, hξ.2])
      rw [this, abs_of_pos (lt_of_lt_of_le hpos hξ.1)]
      exact ⟨hpos, hξ.1⟩
    · have : max lo (-hi) = -hi := max_eq_right (by linarith [hξ.1, hξ.2])
      rw [this, abs_of_neg (lt_of_le_of_lt hξ.2 hneg)]
      exact ⟨by linarith, by linarith [hξ.2]⟩
  refine Taylm.taylor_outer h _ _ _ (fun ξ hξ => contDiffAt_inv ℝ ?_) fun ξ hξ => ?_
  · exact abs_pos.1 (lt_of_lt_of_le (hm ξ hξ).1 (hm ξ hξ).2)
  obtain ⟨hm0, hmξ⟩ := hm ξ hξ
  have hξ0 : 0 < |ξ| := lt_of_lt_of_le hm0 hmξ
  -- `|(-1)ᴺ⁺¹ (N+1)! ξ⁻ᴺ⁻²| = (N+1)! / |ξ|ᴺ⁺²`, decreasing in `|ξ|`
  rw [iteratedDeriv_eq_iterate, show (fun x : ℝ => x⁻¹) = Inv.inv from rfl, iter_deriv_inv,
    abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast,
    show (-1 - ((T.maxOrder + 1 : ℕ) : ℤ)) = -((T.maxOrder + 2 : ℕ) : ℤ) by push_cast; ring,
    zpow_neg, zpow_natCast, abs_inv, abs_pow, div_eq_mul_inv]
  gcongr

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
