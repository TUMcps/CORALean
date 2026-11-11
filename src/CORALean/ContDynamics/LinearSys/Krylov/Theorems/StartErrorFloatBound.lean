module

public import CORALean.ContDynamics.LinearSys.Krylov.Operations.StartErrorFloat
public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.Global.EuclideanNorm
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# The computed start error covers the distance of the scaled first vector from the start vector

The start vector's share of the error of [1, Thm. 3]'s bound: entry `r` of `c - ν v` lies between
`subDown c_r (ν v_r)↑` and `subUp c_r (ν v_r)↓`, so its magnitude is at most the larger of the two,
and the Euclidean norm at most `normUp` of those.

## Inputs
* `p` – Newton steps per norm
* `c` – start vector
* `ν` – scale
* `v` – first basis vector

## Hypotheses
* none

## Conclusion
* the real distance is at most the float bound

## References

* [1] [T. Jawecki, W. Auzinger and O. Koch. "Computable upper error bounds for Krylov approximations
      to matrix exponentials and associated φ-functions". BIT Numerical Mathematics,
      2020.](../../../../../../references/2020/jawecki-bit-krylov-error-bounds.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Krylov.startError_le_startErrorFloat (p : ℕ) (c : Vec 𝕋 n) (ν : 𝕋)
    (v : Vector 𝕋 n) : -- --- CONCL ---
    ‖fun r => toReal (c r) - toReal ν * toReal v[r]‖₂ ≤
      toReal (Krylov.startErrorFloat p c ν v) := by -- --- PROOF ---
  refine norm₂_le_normUp p fun r => ?_
  set d : ℝ := toReal (c r) - toReal ν * toReal v[r] with hd
  have hlo := subDown_le_sub (c r) (mulUp ν v[r])
  have hhi := sub_le_subUp (c r) (mulDown ν v[r])
  have h1 := mul_le_mulUp ν v[r]
  have h2 := mulDown_le_mul ν v[r]
  have hl : toReal (subDown (c r) (mulUp ν v[r])) ≤ d := by rw [hd]; linarith
  have hh : d ≤ toReal (subUp (c r) (mulDown ν v[r])) := by rw [hd]; linarith
  show |d| ≤ |toReal (maximum _ _)|
  rw [toReal_maximum, toReal_absolute, toReal_absolute]
  refine le_trans ?_ (le_abs_self _)
  rcases le_total 0 d with h | h
  · rw [abs_of_nonneg h]
    exact le_max_of_le_right ((by linarith : d ≤ _).trans (le_abs_self _))
  · rw [abs_of_nonpos h]
    exact le_max_of_le_left ((by linarith : -d ≤ _).trans (neg_le_abs _))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
