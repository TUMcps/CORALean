module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Logic.Function.CompTypeclasses
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope

@[expose] public section

/-!
# A polynomial zonotope as a zonotope

Two enclosures, the cheaper first. `zonotope` reads every dependent generator as an independent one
([1, Prop. 2.6]), a monomial in factors of `[-1,1]` being itself in `[-1,1]`; what is lost is the
*sharing*, so every non-convexity goes and so does the exactness of a quadratic map. `zonotopeEven`
is [2, Prop. 1], restated as [3, Prop. 5], and CORA's own `zonotope(polyZonotope)`: an all-even
column has its monomial in `[0,1]`, so half of that generator moves into the center. A column of
zeros is the paper's `N`; CORA reads it as merely even. That freeing is why `zonotope_not_mono`
holds: the result is a function of the representation, not of the set, so [4]'s property (6),
assumed by [4, Lemma 3], is false here.

## Inputs
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* set is contained in its even-column zonotope

## References

* [1] [T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control,
      2023.](../../../../../../references/2023/ladner-hscc-abstraction-refinement.md)
* [2] [M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative Polynomialization
      and Non-Convex Sets". Proceedings of the 16th international conference on Hybrid systems:
      computation and control,
      2013.](../../../../../../references/2013/althoff-hscc-conservative-polynomialization.md)
* [3] [N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set Representation for
      Reachability Analysis". IEEE Transactions on Automatic Control,
      2021.](../../../../../../references/2021/kochdumper-tac-sparse-polyzonotopes.md)
* [4] [N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to Obtain Subsets of
      Reachable Sets". Proceedings of the 23rd International Conference on Hybrid Systems:
      Computation and Control,
      2020.](../../../../../../references/2020/kochdumper-hscc-utilizing-dependencies.md)
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   13-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The coefficient that free generator is given, so that what the center already
holds plus this much of the generator is the monomial. -/
private noncomputable def PolyZonotope.aux_evenCoeff {p h : ℕ} (E : Fin p → Fin h → ℕ)
    (a : Fin p → ℝ) (i : Fin h) : ℝ :=
  if ∀ k, E k i = 0 then 0
  else if ∀ k, E k i % 2 = 0 then 2 * PolyZonotope.monomial E a i - 1
  else PolyZonotope.monomial E a i

/-- A column of zeros reads every factor at exponent zero, so its monomial is
`1` whatever the factors are. -/
private theorem PolyZonotope.aux_monomial_eq_one {p h : ℕ} {E : Fin p → Fin h → ℕ} {i : Fin h}
    (hE : ∀ k, E k i = 0) (a : Fin p → ℝ) : PolyZonotope.monomial E a i = 1 :=
  Finset.prod_eq_one fun k _ => by rw [hE k, pow_zero]

/-- An all-even column's monomial is a product of even powers, so it never goes
below zero — which is what lets its generator be halved. -/
private theorem PolyZonotope.aux_monomial_nonneg {p h : ℕ} {E : Fin p → Fin h → ℕ} {i : Fin h}
    (hE : ∀ k, E k i % 2 = 0) (a : Fin p → ℝ) : 0 ≤ PolyZonotope.monomial E a i :=
  Finset.prod_nonneg fun k _ => Even.pow_nonneg (Nat.even_iff.mpr (hE k)) (a k)

/-- What the center keeps plus what the free generator reaches is the monomial,
in each of the three cases. -/
private theorem PolyZonotope.aux_evenWeight_smul {p h : ℕ} (E : Fin p → Fin h → ℕ) (a : Fin p → ℝ)
    (i : Fin h) : -- --- CONCL ---
    (1 - PolyZonotope.evenWeight E i)
        + PolyZonotope.aux_evenCoeff E a i * PolyZonotope.evenWeight E i
      = PolyZonotope.monomial E a i := by -- --- PROOF ---
  rw [PolyZonotope.evenWeight, PolyZonotope.aux_evenCoeff]
  split_ifs with hz he
  · -- a constant column: the center takes all of it
    rw [PolyZonotope.aux_monomial_eq_one hz a]
    ring
  · -- an all-even column: half in the center, half left free
    ring
  · -- anything else: the center takes none of it
    ring

/-- Every coefficient a free generator is given is admissible, an all-even
column because its monomial lies in `[0,1]`. -/
private theorem PolyZonotope.aux_abs_evenCoeff_le_one {p h : ℕ} (E : Fin p → Fin h → ℕ)
    {a : Fin p → ℝ} (ha : ∀ k, |a k| ≤ 1) (i : Fin h) : -- --- CONCL ---
    |PolyZonotope.aux_evenCoeff E a i| ≤ 1 := by -- --- PROOF ---
  rw [PolyZonotope.aux_evenCoeff]
  split_ifs with hz he
  · rw [abs_zero]
    exact zero_le_one
  · -- `[0,1]` on the nose, so `2m - 1` stays inside `[-1,1]`
    have h₀ : 0 ≤ PolyZonotope.monomial E a i := PolyZonotope.aux_monomial_nonneg he a
    have h₁ : PolyZonotope.monomial E a i ≤ 1 :=
      le_trans (le_abs_self _) (PolyZonotope.abs_monomial_le_one E ha i)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · exact PolyZonotope.abs_monomial_le_one E ha i

/-- `Fin.sum_univ_add` at the generator count the tighter conversion produces,
the binder ascribed so that it matches the goal. -/
private theorem PolyZonotope.aux_sum_univ_zonotopeEven {pZ : PolyZonotope α}
    (f : Fin (pZ.h + pZ.q) → α) :
    ∑ l : Fin pZ.zonotopeEven.h, f l
      = ∑ i, f (Fin.castAdd pZ.q i) + ∑ j, f (Fin.natAdd pZ.h j) :=
  Fin.sum_univ_add f


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.zonotopeEven_contains (pZ : PolyZonotope α) : -- --- CONCL ---
    pZ.construct ⊆ pZ.zonotopeEven.construct := by -- --- PROOF ---
  rintro _ ⟨a, b, ha, hb, rfl⟩
  refine ⟨Fin.append (fun i => PolyZonotope.aux_evenCoeff pZ.E a i) b, ?_, ?_⟩
  · refine Fin.addCases ?_ ?_
    · intro i
      simpa using PolyZonotope.aux_abs_evenCoeff_le_one pZ.E ha i
    · intro j
      simpa using hb j
  · -- the center's share and the free generator's share add back to the monomial
    have hsum : ∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i
        = ∑ i, (1 - PolyZonotope.evenWeight pZ.E i) • pZ.G i
          + ∑ i, PolyZonotope.aux_evenCoeff pZ.E a i
              • (PolyZonotope.evenWeight pZ.E i • pZ.G i) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, ← add_smul, PolyZonotope.aux_evenWeight_smul]
    rw [PolyZonotope.aux_sum_univ_zonotopeEven]
    simp only [PolyZonotope.zonotopeEven, Fin.append_left, Fin.append_right]
    rw [hsum]
    abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
