module

public import CORALean.ContSet.Zonotope.Real.Complexity.Time.ExhaustiveSearch

@[expose] public section

/-!
# [1, Prop. 11]: searching the `n + κ` longest generators is `O(κⁿ⁺¹)`

The exhaustive search of [1, Prop. 10] run on a shortlist of `p̃ = n + κ` generators,
as method B and C do, costs `O(C(n + κ, n)(n + κ)) = O((n + κ)ⁿ(n + κ)) = O(κⁿ⁺¹)` for
fixed `n`, the proposition's chain. Read off `exhaustiveSearchCost` at `p = n + κ`
through `exhaustiveSearchCost_ops_le`, then `C(n + κ, n) ≤ (n + κ)ⁿ` and
`n + κ ≤ 2κ` once `κ ≥ n`.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Computing Reachable Sets of Hybrid
      Systems Using a Combination of Zonotopes and Polytopes". Nonlinear
      Analysis: Hybrid Systems, 4(2):233-249, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 11]: for fixed `n`, the search over the `n + κ` longest generators is
`O(κⁿ⁺¹)` in `κ`. -/
theorem Zonotope.exhaustiveSearchCost_filtered_isBigO (n : ℕ) :
    (fun κ : ℕ => ((Zonotope.exhaustiveSearchCost n (n + κ)).ops : ℝ))
      =O[Filter.atTop] fun κ : ℕ => (κ : ℝ) ^ (n + 1) := by -- --- PROOF ---
  apply Asymptotics.IsBigO.of_bound ((3 * 2 ^ (n + 1) : ℕ) : ℝ)
  filter_upwards [Filter.eventually_ge_atTop (max n 1)] with κ hκ
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  have h1 : 1 ≤ n + κ := by omega
  -- `C(n + κ, n)(n + κ) ≤ (n + κ)ⁿ⁺¹ ≤ (2κ)ⁿ⁺¹`
  have hc : (n + κ).choose n * (n + κ) ≤ 2 ^ (n + 1) * κ ^ (n + 1) := by
    calc (n + κ).choose n * (n + κ) ≤ (n + κ) ^ n * (n + κ) := by
          gcongr; exact Nat.choose_le_pow _ _
      _ = (n + κ) ^ (n + 1) := by ring
      _ ≤ (2 * κ) ^ (n + 1) := by gcongr; omega
      _ = 2 ^ (n + 1) * κ ^ (n + 1) := by ring
  have hops := Zonotope.exhaustiveSearchCost_ops_le n (n + κ) h1
  have : (Zonotope.exhaustiveSearchCost n (n + κ)).ops ≤ 3 * 2 ^ (n + 1) * κ ^ (n + 1) := by
    calc _ ≤ 3 * ((n + κ).choose n * (n + κ)) := hops
      _ ≤ 3 * (2 ^ (n + 1) * κ ^ (n + 1)) := by gcongr
      _ = 3 * 2 ^ (n + 1) * κ ^ (n + 1) := by ring
  exact_mod_cast this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
