module

public import CORALean.ContSet.Taylm.Real.Operations.BernsteinEntry
public import CORALean.ContSet.Taylm.Real.Theorems.PowEqSumBernsteinBasis

@[expose] public section

/-!
# A monomial on `[-1, 1]` in the Bernstein basis

For `e ≤ N` and any `x`, `xᵉ = Σⱼ M(j, e) · B_{j,N}((x + 1) / 2)` with `M = bernsteinEntry`: the
one-variable case of what `poly2bernstein` [1] computes. With `x = 2u - 1` the binomial theorem
expands `xᵉ` in powers of `u`, and `pow_eq_sum_bernsteinBasis` takes each power to the Bernstein
basis.

## Inputs
* `N` – degree
* `e` – exponent
* `x` – point of the symmetric interval

## Hypotheses
* `he` – exponent is at most the degree

## Conclusion
* the monomial on the symmetric interval is a Bernstein combination

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

theorem Taylm.pow_eq_sum_bernsteinEntry (N e : ℕ) (he : e ≤ N) (x : ℝ) :
    x ^ e = ∑ j ∈ Finset.range (N + 1),
      Taylm.bernsteinEntry N e j * Taylm.bernsteinBasis N j ((x + 1) / 2) := by -- --- PROOF ---
  -- `x = 2u + (-1)`, expanded in powers of `u`
  have hx : x = 2 * ((x + 1) / 2) + (-1) := by ring
  set u := (x + 1) / 2 with hu
  have hexp : x ^ e = ∑ i ∈ Finset.range (e + 1),
      ((e.choose i : ℝ) * 2 ^ i * (-1) ^ (e - i)) * u ^ i := by
    rw [hx, add_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow]
    ring
  -- each power in the Bernstein basis, then swap the two sums
  calc x ^ e = ∑ i ∈ Finset.range (e + 1), ((e.choose i : ℝ) * 2 ^ i * (-1) ^ (e - i)) *
        ∑ j ∈ Finset.range (N + 1),
          ((j.choose i : ℝ) / (N.choose i : ℝ)) * Taylm.bernsteinBasis N j u := by
        rw [hexp]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [← Taylm.pow_eq_sum_bernsteinBasis N i
          (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) he) u]
    _ = ∑ j ∈ Finset.range (N + 1), Taylm.bernsteinEntry N e j * Taylm.bernsteinBasis N j u := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        unfold Taylm.bernsteinEntry
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
