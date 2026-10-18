module

public import CORALean.ContSet.PolyZonotope.Real.Operations.GetSubset
public import CORALean.ContSet.PolyZonotope.Real.Operations.Point
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

/-!
# `getSubset`'s point is the original's at the re-parametrized factor

The whole content of the construction, and an *equality*: the new factor vector
`b` names the point the old one named at `αₖ = cen + rad·βₖ`, every other factor
left alone. Nothing is over-approximated, because the binomial expansion of
`(cen + rad·βₖ)^e` is a polynomial identity — a monomial above degree one is
re-parametrized exactly, not merely enclosed.

Stated over `point` rather than over `construct`, like `map_point` and
`bilin_point`: the independent block takes no part in a change of *dependent*
variables, and only the set-level statements need it back.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open PolyZonotope

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The binomial theorem over a range padded past the degree: the surplus terms
carry `Nat.choose e j = 0` and so contribute nothing. -/
theorem PolyZonotope.aux_getSubset_binom (x y : ℝ) {e d : ℕ} (hed : e ≤ d) :
    ∑ j : Fin (d + 1), ((e.choose j : ℝ) * x ^ (e - (j : ℕ)) * y ^ (j : ℕ))
      = (x + y) ^ e := by -- --- PROOF ---
  rw [Fin.sum_univ_eq_sum_range (fun j => ((e.choose j : ℝ) * x ^ (e - j) * y ^ j)) (d + 1),
    add_comm x y, add_pow]
  -- the terms `range (e + 1)` is short of are zero, so the two ranges agree
  have hsub : Finset.range (e + 1) ⊆ Finset.range (d + 1) :=
    fun j hj => Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega)
  have hzero : ∀ j ∈ Finset.range (d + 1), j ∉ Finset.range (e + 1) →
      y ^ j * x ^ (e - j) * (e.choose j : ℝ) = 0 := by
    intro j _ hj
    rw [Finset.mem_range] at hj
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
  rw [Finset.sum_subset hsub hzero]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- One expanded column, its monomial and its generator: the substituted factor
pulled out of both, the rest of the monomial left standing. -/
theorem PolyZonotope.aux_getSubset_col (pZ : PolyZonotope α) (k : Fin pZ.p) (cen rad : ℝ)
    (b : Fin pZ.p → ℝ) (i : Fin pZ.h) (j : Fin (pZ.maxExp k + 1)) : -- --- STMT ---
    monomial (pZ.getSubsetE k) b (finProdFinEquiv (i, j))
        • pZ.getSubsetG k cen rad (finProdFinEquiv (i, j))
      = (((pZ.E k i).choose j : ℝ) * cen ^ (pZ.E k i - (j : ℕ)) * (rad * b k) ^ (j : ℕ)
          * ∏ k' ∈ Finset.univ.erase k, b k' ^ pZ.E k' i) • pZ.G i := by -- --- PROOF ---
  have h0 : monomial (pZ.getSubsetE k) b (finProdFinEquiv (i, j))
      = ∏ k' : Fin pZ.p, b k' ^ (if k' = k then (j : ℕ) else pZ.E k' i) := by
    simp only [monomial, PolyZonotope.getSubsetE, Equiv.symm_apply_apply]
  -- the substituted factor comes out of the product, the other factors stay
  have hmon : monomial (pZ.getSubsetE k) b (finProdFinEquiv (i, j))
      = b k ^ (j : ℕ) * ∏ k' ∈ Finset.univ.erase k, b k' ^ pZ.E k' i := by
    rw [h0, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), if_pos rfl]
    exact congrArg _ (Finset.prod_congr rfl fun k' hk' => by
      rw [if_neg (Finset.mem_erase.mp hk').1])
  have hgen : pZ.getSubsetG k cen rad (finProdFinEquiv (i, j))
      = (((pZ.E k i).choose j : ℝ) * cen ^ (pZ.E k i - (j : ℕ)) * rad ^ (j : ℕ)) • pZ.G i := by
    simp only [PolyZonotope.getSubsetG, Equiv.symm_apply_apply]
  rw [hmon, hgen, smul_smul, mul_pow]
  ring_nf


-- =======================================  MAIN THEOREM  ======================================= --

/-- `getSubset`'s point at `b` is the original's at the factor vector `b` with
its `k`-th entry sent through `βₖ ↦ cen + rad·βₖ`. -/
theorem PolyZonotope.getSubset_point (pZ : PolyZonotope α) (k : Fin pZ.p) (cen rad : ℝ)
    (b : Fin pZ.p → ℝ) : (pZ.getSubset k cen rad).point b
      = pZ.point (Function.update b k (cen + rad * b k)) := by -- --- PROOF ---
  have hle : ∀ i : Fin pZ.h, pZ.E k i ≤ pZ.maxExp k := fun i => Finset.le_sup (Finset.mem_univ i)
  -- the pairs and the flat generator index are the same sum, reindexed
  have hpair : ∑ pr : Fin pZ.h × Fin (pZ.maxExp k + 1),
        monomial (pZ.getSubsetE k) b (finProdFinEquiv pr)
          • pZ.getSubsetG k cen rad (finProdFinEquiv pr)
      = ∑ l, monomial (pZ.getSubsetE k) b l • pZ.getSubsetG k cen rad l :=
    Fintype.sum_equiv finProdFinEquiv _ _ fun _ => rfl
  show pZ.c + ∑ l, monomial (pZ.getSubsetE k) b l • pZ.getSubsetG k cen rad l
    = pZ.c + ∑ i, monomial pZ.E (Function.update b k (cen + rad * b k)) i • pZ.G i
  rw [← hpair, Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  -- the substituted factor leaves the same tail product on either side
  have hrest : monomial pZ.E (Function.update b k (cen + rad * b k)) i
      = (cen + rad * b k) ^ pZ.E k i * ∏ k' ∈ Finset.univ.erase k, b k' ^ pZ.E k' i := by
    simp only [monomial]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), Function.update_self]
    exact congrArg _ (Finset.prod_congr rfl fun k' hk' => by
      rw [Function.update_of_ne (Finset.mem_erase.mp hk').1])
  -- the expanded columns sum to the substituted monomial, by the binomial theorem
  rw [hrest, ← PolyZonotope.aux_getSubset_binom cen (rad * b k) (hle i), Finset.sum_mul,
    Finset.sum_smul]
  exact Finset.sum_congr rfl fun j _ => PolyZonotope.aux_getSubset_col pZ k cen rad b i j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
