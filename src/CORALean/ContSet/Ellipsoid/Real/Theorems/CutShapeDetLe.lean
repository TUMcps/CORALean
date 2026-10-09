import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
import CORALean.ContSet.Ellipsoid.Real.Theorems.CutShapeDet
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The determinant of the cut ellipsoid at the Goffin cut depth

At the depth `γ = 1/√(n(1+ε))` of [1, Lemma 4.4], `det E ≤ exp(2/√(1+ε) − 2 + ε/(1+ε))`. With
`a = n(1−γ²)/(n−1) = 1 + x`, `x = ε/((1+ε)(n−1))`, and `a(1 − κ) = nγ² = 1/(1+ε)`, the
determinant is `(1+x)^(n−1)/(1+ε)`; `1 + x ≤ eˣ` gives `(1+x)^(n−1) ≤ e^(ε/(1+ε))`, and
`1/(1+ε) = (1/√(1+ε))² ≤ (e^(1/√(1+ε) − 1))²`.

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 4.4]: `det E ≤ exp(2/√(1+ε) − 2 + ε/(1+ε))` at `γ = 1/√(n(1+ε))`. -/
theorem Ellipsoid.cutShape_det_le {c : Vec ℝ n} (hc : c ⬝ᵥ c = 1) (hn : 2 ≤ n) {ε : ℝ}
    (hε : 0 < ε) :
    (Ellipsoid.cutShape n c (1 / Real.sqrt ((n : ℝ) * (1 + ε)))).det
      ≤ Real.exp (2 * (1 / Real.sqrt (1 + ε)) - 2 + ε / (1 + ε)) := by -- --- PROOF ---
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (0:ℝ) < (n:ℝ) - 1 := by linarith
  have hε1 : 0 < 1 + ε := by linarith
  set γ := 1 / Real.sqrt ((n : ℝ) * (1 + ε)) with hγ
  have hγ2 : γ ^ 2 = 1 / ((n : ℝ) * (1 + ε)) := by
    rw [hγ, div_pow, Real.sq_sqrt (by positivity)]; simp
  rw [Ellipsoid.cutShape_det hc, hγ2]
  -- the base is `1 + x` and the last factor `1/(1+ε)`
  set d : ℝ := (n : ℝ) - 1 with hd
  set x : ℝ := ε / ((1 + ε) * d) with hx
  have hx0 : 0 ≤ x := by positivity
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hd0 : (n : ℝ) - 1 ≠ 0 := h2.ne'
  have hd0' : -1 + (n : ℝ) ≠ 0 := by linarith
  have hε0 : 1 + ε ≠ 0 := hε1.ne'
  have hnε : (n : ℝ) * (1 + ε) - 1 ≠ 0 := by nlinarith
  have hbase : (n : ℝ) * (1 - 1 / ((n : ℝ) * (1 + ε))) / ((n : ℝ) - 1) = 1 + x := by
    rw [hx, hd]; field_simp; ring
  have hlast : (1 - (1 - (n : ℝ) * (1 / ((n : ℝ) * (1 + ε)))) / (1 - 1 / ((n : ℝ) * (1 + ε))))
      * (1 + x) = 1 / (1 + ε) := by
    rw [hx, hd]; field_simp; ring
  rw [hbase]
  -- one factor of the base joins the last factor, which is `1/(1+ε)`
  have hpow : (1 + x) ^ n = (1 + x) ^ (n - 1) * (1 + x) := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  rw [hpow]
  generalize hL : (1 - (1 - (n : ℝ) * (1 / ((n : ℝ) * (1 + ε)))) / (1 - 1 / ((n : ℝ) * (1 + ε))))
    = L at hlast ⊢
  -- `1 + x ≤ eˣ`, to the power `n − 1`
  have hexp : (1 + x) ^ (n - 1) ≤ Real.exp (ε / (1 + ε)) := by
    have h1 : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
    calc (1 + x) ^ (n - 1) ≤ Real.exp x ^ (n - 1) := pow_le_pow_left₀ (by linarith) h1 _
      _ = Real.exp (((n - 1 : ℕ) : ℝ) * x) := by rw [← Real.exp_nat_mul]
      _ = Real.exp (ε / (1 + ε)) := by
        congr 1
        rw [Nat.cast_sub (by omega), hx, Nat.cast_one, ← hd]
        field_simp
  -- `1/(1+ε) = (1/√(1+ε))²`, and `1/√(1+ε) ≤ e^(1/√(1+ε) − 1)`
  have hs : 1 / (1 + ε) ≤ Real.exp (2 * (1 / Real.sqrt (1 + ε)) - 2) := by
    have hu : 0 < Real.sqrt (1 + ε) := Real.sqrt_pos.2 hε1
    have hsq : (1 / Real.sqrt (1 + ε)) ^ 2 = 1 / (1 + ε) := by
      rw [div_pow, Real.sq_sqrt hε1.le]; simp
    have h1 : 1 / Real.sqrt (1 + ε) ≤ Real.exp (1 / Real.sqrt (1 + ε) - 1) := by
      linarith [Real.add_one_le_exp (1 / Real.sqrt (1 + ε) - 1)]
    calc 1 / (1 + ε) = (1 / Real.sqrt (1 + ε)) ^ 2 := hsq.symm
      _ ≤ Real.exp (1 / Real.sqrt (1 + ε) - 1) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h1 2
      _ = Real.exp (2 * (1 / Real.sqrt (1 + ε)) - 2) := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc (1 + x) ^ (n - 1) * (1 + x) * L = (1 + x) ^ (n - 1) * (1 / (1 + ε)) := by
        rw [mul_assoc, mul_comm (1 + x) L, hlast]
    _ ≤ Real.exp (ε / (1 + ε)) * Real.exp (2 * (1 / Real.sqrt (1 + ε)) - 2) :=
        mul_le_mul hexp hs (by positivity) (Real.exp_pos _).le
    _ = Real.exp (2 * (1 / Real.sqrt (1 + ε)) - 2 + ε / (1 + ε)) := by
        rw [← Real.exp_add]; congr 1; ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
