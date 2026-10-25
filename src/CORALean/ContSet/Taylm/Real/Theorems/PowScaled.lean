module

public import CORALean.ContSet.Taylm.Real.Theorems.TimesScaled
public import CORALean.ContSet.Taylm.Real.Theorems.PowMaxOrder
public import CORALean.ContSet.Taylm.Real.Operations.Pow

@[expose] public section

/-!
# `Taylm.pow` keeps the scaling

`k` factors of a model scaled by `B`, each a `times` at the same order, give one scaled by
`(4B)ᵏ`; the constant is independent of `h`, which is what [1, Thm. 1] needs of the powers its
intrinsics are made of.

## Inputs
* `T` – Taylor model
* `h` – domain radius
* `B` – scaling constant
* `k` – exponent

## Hypotheses
* `h0` – radius is positive
* `h1` – radius is at most one
* `hT` – the model is scaled by the constant

## Conclusion
* the power is scaled by a constant built from it

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion Methods".
      International Journal of Pure and Applied Mathematics, 2003.
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
    (hT : T.IsScaled h B) (k : ℕ) : -- --- CONCL ---
    (T.pow k).IsScaled h ((4 * B) ^ k) := by -- --- PROOF ---
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
