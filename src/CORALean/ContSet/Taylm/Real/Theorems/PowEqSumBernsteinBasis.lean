module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Algebra.BigOperators.Intervals
public import CORALean.ContSet.Taylm.Real.Operations.BernsteinBasis
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# A monomial in the Bernstein basis

For `i ≤ N`, `uⁱ = Σⱼ C(j, i) / C(N, i) · B_{j,N}(u)`: the entries of `Ux⁻¹` in [1]. Multiplied
by `C(N, i)` the sum starts at `j = i`, where `C(j, i) C(N, j) = C(N, i) C(N - i, j - i)`, and
what is left is the binomial theorem at `(u + (1 - u))^(N - i)`.

## Inputs
* `N` – degree
* `i` – exponent
* `u` – point of the unit interval

## Hypotheses
* `hi` – exponent is at most the degree

## Conclusion
* the monomial is a combination of Bernstein basis polynomials

## References

* [1] `global/functions/helper/sets/contSet/polyZonotope/poly2bernstein.m`, CORA (Sep. 2025).
      No paper behind the rule was confirmed.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.pow_eq_sum_bernsteinBasis (N i : ℕ) (hi : i ≤ N) (u : ℝ) :
    u ^ i = ∑ j ∈ Finset.range (N + 1),
      ((j.choose i : ℝ) / (N.choose i : ℝ)) * Taylm.bernsteinBasis N j u := by -- --- PROOF ---
  have hpos : (0 : ℝ) < N.choose i := Nat.cast_pos.mpr (Nat.choose_pos hi)
  -- clear the denominator: `C(N, i) uⁱ = Σⱼ C(j, i) B_j(u)`
  suffices h : (N.choose i : ℝ) * u ^ i =
      ∑ j ∈ Finset.range (N + 1), (j.choose i : ℝ) * Taylm.bernsteinBasis N j u by
    rw [eq_comm, ← mul_right_inj' hpos.ne', Finset.mul_sum]
    rw [h]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  -- the terms below `i` vanish, the rest start at `i`
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le i) (Nat.le_succ_of_le hi),
    Finset.sum_eq_zero (s := Finset.Ico 0 i) fun j hj => by
      rw [Nat.choose_eq_zero_of_lt (Finset.mem_Ico.mp hj).2]; simp, zero_add,
    Finset.sum_Ico_eq_sum_range]
  -- shift by `i`; `C(j, i) C(N, j) = C(N, i) C(N - i, j - i)` splits off `C(N, i) uⁱ`
  have hterm : ∀ m ∈ Finset.range (N + 1 - i), ((i + m).choose i : ℝ) *
      Taylm.bernsteinBasis N (i + m) u =
      (N.choose i : ℝ) * u ^ i * (((N - i).choose m : ℝ) * u ^ m * (1 - u) ^ (N - i - m)) := by
    intro m hm
    have hmN : i + m ≤ N := by
      have := Finset.mem_range.mp hm; omega
    have hc := Nat.choose_mul (n := N) (Nat.le_add_right i m)
    have hc' : ((i + m).choose i : ℝ) * (N.choose (i + m) : ℝ) =
        (N.choose i : ℝ) * ((N - i).choose m : ℝ) := by
      have := congrArg (Nat.cast (R := ℝ)) hc
      push_cast at this
      rw [Nat.add_sub_cancel_left] at this
      linarith [this, mul_comm ((N.choose (i + m)) : ℝ) ((i + m).choose i : ℝ)]
    unfold Taylm.bernsteinBasis
    have hexp : N - (i + m) = N - i - m := by omega
    rw [hexp, pow_add]
    calc ((i + m).choose i : ℝ) * ((N.choose (i + m) : ℝ) * (u ^ i * u ^ m) * (1 - u) ^ (N - i - m))
        = (((i + m).choose i : ℝ) * (N.choose (i + m) : ℝ)) * (u ^ i * u ^ m) *
          (1 - u) ^ (N - i - m) := by ring
      _ = _ := by rw [hc']; ring
  -- what is left is the binomial theorem at `(u + (1 - u))^(N - i)`
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hbin := add_pow u (1 - u) (N - i)
  simp only [add_sub_cancel, one_pow] at hbin
  have hlen : N + 1 - i = N - i + 1 := by omega
  rw [hlen]
  have hsum : ∑ m ∈ Finset.range (N - i + 1),
      ((N - i).choose m : ℝ) * u ^ m * (1 - u) ^ (N - i - m) = 1 :=
    (Finset.sum_congr rfl fun m _ => by ring).trans hbin.symm
  rw [hsum]
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
