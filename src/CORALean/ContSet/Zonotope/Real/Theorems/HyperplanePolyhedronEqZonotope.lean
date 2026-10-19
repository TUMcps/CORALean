module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.ContSet.ContSet.Definitions.HyperplanePolyhedron
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# A box in orthonormal directions is a zonotope

[1, Sec. 3.4]: if the normals of the polyhedron `{x | ∀ ℓ ∈ D, m_ℓ ≤ x·ℓ ≤ M_ℓ}` are the
rows `ℓᵢ` of an orthogonal matrix `L`, it is a hyper-rectangle, hence a zonotope: with
`yᵢ = x·ℓᵢ` the coordinates of `x` in that basis, it is the zonotope of center
`∑ ((m + M)/2) ℓᵢ` and generators `((M − m)/2) ℓᵢ`. The paper chooses the normals so that the
over-approximation can be used as the next initial set, which needs a zonotope.

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 3.4]: with orthonormal rows `L i`, the polyhedron is a zonotope. -/
theorem Zonotope.hyperplanePolyhedron_eq (L : Mat ℝ n n) (hL : L * Lᵀ = 1)
    (m M : Vec ℝ n → ℝ) (hmM : ∀ i, m (L i) ≤ M (L i)) : -- --- CONCL ---
    ContSet.hyperplanePolyhedron (Finset.univ.image fun i => L i) m M
      = (Zonotope.mk n (∑ i, ((m (L i) + M (L i)) / 2) • L i)
          (fun i => ((M (L i) - m (L i)) / 2) • L i)).construct := by -- --- PROOF ---
  have hLT : Lᵀ * L = 1 := mul_eq_one_comm.1 hL
  -- the rows are orthonormal
  have hrow : ∀ i j, L i ⬝ᵥ L j = if i = j then 1 else 0 := by
    intro i j
    have := congrFun (congrFun hL i) j
    simpa [Matrix.mul_apply, Matrix.one_apply, dotProduct] using this
  -- a point is the combination of its coordinates along the rows
  have hrec : ∀ x : Vec ℝ n, x = ∑ i, (x ⬝ᵥ L i) • L i := by
    intro x
    have h1 : Lᵀ *ᵥ (L *ᵥ x) = x := by rw [mulVec_mulVec, hLT, one_mulVec]
    funext k
    conv_lhs => rw [← h1]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
    congr 1
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  -- the box has midpoint `mid` and radius `rad` along each row
  ext x
  set mid : Fin n → ℝ := fun i => (m (L i) + M (L i)) / 2 with hmid
  set rad : Fin n → ℝ := fun i => (M (L i) - m (L i)) / 2 with hrad
  have hrad0 : ∀ i, 0 ≤ rad i := fun i => by simp only [hrad]; linarith [hmM i]
  -- the coordinate of a zonotope point along `L k` is `mid k + β k * rad k`
  have hdot : ∀ (β : Fin n → ℝ) (k : Fin n),
      ((∑ i, mid i • L i) + ∑ j, β j • (rad j • L j)) ⬝ᵥ L k = mid k + β k * rad k := by
    intro β k
    rw [add_dotProduct, sum_dotProduct, sum_dotProduct]
    simp only [smul_dotProduct, hrow, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [ContSet.hyperplanePolyhedron, Set.mem_setOf_eq, Finset.mem_image, Finset.mem_univ,
    true_and, forall_exists_index, forall_apply_eq_imp_iff, Zonotope.construct]
  constructor
  · -- a point of the box is a point of the zonotope
    intro hx
    -- coefficients `(yₖ − midₖ) / radₖ`, or `0` on a degenerate axis
    set β : Fin n → ℝ := fun k => if rad k = 0 then 0 else (x ⬝ᵥ L k - mid k) / rad k with hβ
    -- the coordinate is the midpoint plus `β` radii, also on a degenerate axis
    have hy : ∀ k, x ⬝ᵥ L k = mid k + β k * rad k := by
      intro k
      -- a degenerate axis pins the coordinate to the midpoint
      by_cases h0 : rad k = 0
      · have h1 := hx k
        have h2 : m (L k) = M (L k) := by simp only [hrad] at h0; linarith [hmM k]
        simp only [hβ, h0, if_true, hmid, zero_mul, add_zero]
        linarith [h1.1, h1.2]
      · simp only [hβ, h0, if_false]
        field_simp
        ring
    refine ⟨β, fun k => ?_, ?_⟩
    · -- the coefficients are in `[−1, 1]`, as the coordinate is in `[m, M]`
      by_cases h0 : rad k = 0
      · simp [hβ, h0]
      · have hr : 0 < rad k := lt_of_le_of_ne (hrad0 k) (Ne.symm h0)
        have h1 := hx k
        simp only [hβ, h0, if_false]
        rw [abs_div, abs_of_pos hr, div_le_one hr, abs_le]
        simp only [hmid, hrad] at hr ⊢
        constructor <;> linarith [h1.1, h1.2]
    · conv_lhs => rw [hrec x]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul, ← add_smul, hy k]
  · -- and conversely
    rintro ⟨β, hβ, rfl⟩ k
    rw [hdot β k]
    have := abs_le.1 (hβ k)
    have h1 : β k * rad k ≤ rad k := mul_le_of_le_one_left (hrad0 k) this.2
    have h2 : -rad k ≤ β k * rad k := by nlinarith [hrad0 k]
    simp only [hmid, hrad] at h1 h2 ⊢
    constructor <;> linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
