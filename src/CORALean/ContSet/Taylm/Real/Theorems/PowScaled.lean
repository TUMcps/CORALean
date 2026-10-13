import CORALean.ContSet.Taylm.Real.Theorems.TimesScaled
import CORALean.ContSet.Taylm.Real.Theorems.PowMaxOrder
import CORALean.ContSet.Taylm.Real.Operations.Pow

/-!
# `Taylm.pow` keeps the scaling

`k` factors of a model scaled by `B`, each a `times` at the same order, give one scaled by
`(4B)ᵏ`; the constant is independent of `h`, which is what [1, Thm. 1] needs of the powers its
intrinsics are made of.

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

theorem Taylm.pow_scaled {T : Taylm n} {h B : ℝ} (h0 : 0 < h) (h1 : h ≤ 1)
    (hT : T.Scaled h B) (k : ℕ) : (T.pow k).Scaled h ((4 * B) ^ k) := by -- --- PROOF ---
  induction k with
  | zero =>
    refine ⟨by simp [Taylm.pow, Taylm.const, Taylm.weight, Taylm.degree], ?_, ?_⟩ <;>
      simp [Taylm.pow, Taylm.const, (pow_pos h0 _).le]
  | succ k ih =>
    have := Taylm.times_scaled h0 h1 (Taylm.pow_maxOrder T k) ih hT
    rw [show 4 * ((4 * B) ^ k * B) = (4 * B) ^ (k + 1) by ring] at this
    exact this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
