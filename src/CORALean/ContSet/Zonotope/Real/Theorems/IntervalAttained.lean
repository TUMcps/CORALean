import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The box of a zonotope is attained

In every coordinate `i` the bounds `cᵢ ± Σⱼ |Gᵢⱼ|` of `Zonotope.interval` are values of points
of the zonotope: the coefficients `βⱼ = ±1`, the sign of `Gᵢⱼ`, reach the upper bound and their
negatives the lower one. With `interval_contains` this makes the box the zonotope's interval
hull, [1, Property 4], and it is how a box sum built from zonotopes is compared with another
enclosure in [1, Thm. 6], [1, Thm. 7] and [1, Thm. 8].

## References

* [1] W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control,
      64(11):4717-4724, 2019.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.interval_attained (Z : Zonotope (Vec ℝ n)) (i : Fin n) :
    (∃ z ∈ Z.construct, z i = Z.interval.sup i) ∧
      ∃ z ∈ Z.construct, z i = Z.interval.inf i := by -- --- PROOF ---
  -- the sign of each generator's `i`-th entry
  set s : Fin Z.h → ℝ := fun j => if 0 ≤ Z.G j i then 1 else -1 with hs
  have hs1 : ∀ j, |s j| ≤ 1 := fun j => by simp only [hs]; split_ifs <;> norm_num
  have hsG : ∀ j, s j * Z.G j i = |Z.G j i| := fun j => by
    simp only [hs]
    split_ifs with h
    · rw [one_mul, abs_of_nonneg h]
    · rw [abs_of_neg (not_le.mp h)]; ring
  have hval : ∀ c : ℝ, (Z.c + ∑ j, (c * s j) • Z.G j) i = Z.c i + c * ∑ j, |Z.G j i| := by
    intro c
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => by rw [← hsG j]; ring)
  refine ⟨⟨_, ⟨fun j => 1 * s j, fun j => by simpa using hs1 j, rfl⟩, ?_⟩,
    ⟨_, ⟨fun j => -1 * s j, fun j => by simpa using hs1 j, rfl⟩, ?_⟩⟩
  · rw [hval]
    show _ = Z.c i + ∑ j, |Z.G j i|
    ring
  · rw [hval]
    show _ = Z.c i - ∑ j, |Z.G j i|
    ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
