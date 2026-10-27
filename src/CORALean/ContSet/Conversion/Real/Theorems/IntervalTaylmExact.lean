module

public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Taylm.Real.Taylm
public import CORALean.ContSet.Taylm.Real.Theorems.Basic
public import CORALean.ContSet.Taylm.Real.Theorems.MonomialSingle
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalTaylmContains

@[expose] public section

/-!
# A box as an array of Taylor models

CORA's constructor `taylm(int, max_order)`: coordinate `i` is the model
`mid i + rad i · tᵢ` in its own variable, with no remainder. It encloses that affine map
(`taylm_outer`), its range set contains the box (`taylm_contains`), and is the box when the
box is nonempty (`taylm_exact`): an empty box (`sup < inf` somewhere) still yields the
swapped interval, as CORA's does short of its own emptiness check.

[1, Eq. 11]: `T = 0.5(a̅ + a̲) + 0.5(a̅ - a̲)x + [0, 0]` with `x ∈ [-1, 1]`, whose range is the
interval (`taylm_exact`).

## Inputs
* `I` – interval
* `N` – Taylor order

## Hypotheses
* `hI` – lower end below upper end per coordinate

## Conclusion
* Taylor model equals the interval

## References

* [1] [M. Althoff, D. Grebenyuk and N. Kochdumper. "Implementation of Taylor Models in CORA 2018".
      ARCH18. 5th International Workshop on Applied Verification of Continuous and Hybrid Systems,
      2018.](../../../../../../references/2018/althoff-arch-taylor-models.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.taylm_exact (I : Interval (Vec ℝ n)) (N : ℕ)
    (hI : ∀ i, I.inf i ≤ I.sup i) : -- --- CONCL ---
    Taylm.construct (I.taylm N) = I.construct := by -- --- PROOF ---
  refine Set.Subset.antisymm ?_ (Interval.taylm_contains I N)
  rintro x ⟨t, ht, hx⟩ i
  have hxi := hx i
  simp only [Interval.taylm, Taylm.poly, Taylm.polyOf_cons, Taylm.polyOf_nil,
    Taylm.monomial_zero, Taylm.monomial_single] at hxi
  -- `x i = mid + rad · tᵢ` with `|tᵢ| ≤ 1` and `rad ≥ 0`
  have hr : 0 ≤ (I.sup i - I.inf i) / 2 := by linarith [hI i]
  have ht' := abs_le.1 (ht i)
  have h1 : -((I.sup i - I.inf i) / 2) ≤ (I.sup i - I.inf i) / 2 * t i := by nlinarith
  have h2 : (I.sup i - I.inf i) / 2 * t i ≤ (I.sup i - I.inf i) / 2 := by nlinarith
  exact ⟨by show I.inf i ≤ x i; linarith [hxi.1, hxi.2],
    by show x i ≤ I.sup i; linarith [hxi.1, hxi.2]⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
