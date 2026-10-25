module

public import CORALean.ContSet.ConZonotope.Real.Operations.QuadMap
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

@[expose] public section

/-!
# The quadratic map of a constrained zonotope is enclosed by `ConZonotope.quadMap`

The coefficients of [1, Lemma 1], `βⱼ`, `2βⱼ² - 1` and `βⱼβₖ`, are the same as for a zonotope.
The first block is the point's own coefficient vector, so it meets the constraints, and the
two new blocks are unconstrained.

## Inputs
* `Q` – quadratic form matrices
* `cZ` – constrained zonotope

## Hypotheses
* none

## Conclusion
* the quadratic image is contained in the result

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in Reachability
      Analysis of Hybrid Systems". Proceedings of the 15th ACM international conference on Hybrid
      Systems: Computation and Control, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ} {V : Type} [AddCommGroup V] [Module ℝ V]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `b(c + Σ pⱼgⱼ, c + Σ pⱼgⱼ)` expanded: constant, linear, and every ordered pair. -/
theorem ConZonotope.aux_quadMap_sq {h : ℕ} (b : LinearMap.BilinForm ℝ V) (c : V)
    (g : Fin h → V) (p : Fin h → ℝ) : -- --- CONCL ---
    b (c + ∑ j, p j • g j) (c + ∑ j, p j • g j)
      = b c c + ∑ j, p j * (b c (g j) + b (g j) c)
        + ∑ j, ∑ k, (p j * p k) * b (g j) (g k) := by -- --- PROOF ---
  simp only [map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.coe_sum,
    Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  have h3 : ∑ x, p x * (b c (g x) + ∑ y, p y * b (g y) (g x))
      = ∑ x, p x * b c (g x) + ∑ j, ∑ k, (p j * p k) * b (g j) (g k) := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    congr 1
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [h3]
  have hlin : ∑ j, p j * b c (g j) + ∑ j, p j * b (g j) c
      = ∑ j, p j * (b c (g j) + b (g j) c) := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => (mul_add _ _ _).symm
  rw [← hlin]
  ring

/-- The ordered pairs split into the diagonal and one term per unordered pair `j < k`. -/
theorem ConZonotope.aux_quadMap_diagpair {h : ℕ} (b : LinearMap.BilinForm ℝ V) (g : Fin h → V)
    (p : Fin h → ℝ) : -- --- CONCL ---
    ∑ j, ∑ k, (p j * p k) * b (g j) (g k)
      = ∑ j, (p j * p j) * b (g j) (g j)
        + ∑ j, ∑ k, (if j < k then
            (p j * p k) * (b (g j) (g k) + b (g k) (g j)) else 0) := by -- --- PROOF ---
  have hswap : ∑ j : Fin h, ∑ k, (if j < k then (p j * p k) * b (g k) (g j) else 0)
      = ∑ j : Fin h, ∑ k, (if k < j then (p j * p k) * b (g j) (g k) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm (p k) (p j)]
  have hite : ∀ j k : Fin h, (if j < k then (p j * p k) * (b (g j) (g k) + b (g k) (g j)) else 0)
      = (if j < k then (p j * p k) * b (g j) (g k) else 0)
        + (if j < k then (p j * p k) * b (g k) (g j) else 0) := fun j k => by
    split_ifs <;> ring
  simp only [hite, Finset.sum_add_distrib, hswap]
  -- every `(j, k)` is diagonal, `j < k` or `j > k`, exactly once
  have hdiag : ∀ j k : Fin h, (p j * p k) * b (g j) (g k)
      = (if j = k then (p j * p k) * b (g j) (g k) else 0)
        + (if j < k then (p j * p k) * b (g j) (g k) else 0)
        + (if k < j then (p j * p k) * b (g j) (g k) else 0) := fun j k => by
    rcases lt_trichotomy j k with hjk | hjk | hjk
    · rw [if_neg hjk.ne, if_pos hjk, if_neg (asymm hjk)]; ring
    · subst hjk; rw [if_pos rfl, if_neg (lt_irrefl j)]; ring
    · rw [if_neg hjk.ne', if_neg (asymm hjk), if_pos hjk]; ring
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hdiag j k]
  simp only [Finset.sum_add_distrib]
  rw [show (∑ j : Fin h, ∑ k, (if j = k then (p j * p k) * b (g j) (g k) else 0))
      = ∑ j, (p j * p j) * b (g j) (g j) from
    Finset.sum_congr rfl fun j _ =>
      (Finset.sum_eq_single j (fun k _ hk => if_neg (Ne.symm hk))
        (fun hj => absurd (Finset.mem_univ j) hj)).trans (if_pos rfl)]
  ring

/-- The pair block, read over `Fin (h * h)` through `finProdFinEquiv`. -/
theorem ConZonotope.aux_quadMap_pairblock {h : ℕ} (f : Fin h → Fin h → ℝ) :
    ∑ l : Fin (h * h), f (finProdFinEquiv.symm l).1 (finProdFinEquiv.symm l).2
      = ∑ j, ∑ k, f j k := by
  rw [Fintype.sum_equiv finProdFinEquiv.symm _ (fun jk : Fin h × Fin h => f jk.1 jk.2)
    fun _ => rfl]
  exact Fintype.sum_prod_type _


-- =======================================  MAIN THEOREM  ======================================= --

/-- Outer only: the new factors are free. -/
theorem ConZonotope.quadMap_outer (Q : Fin m → Mat ℝ n n)
    (cZ : ConZonotope (Vec ℝ n)) : -- --- CONCL ---
    (fun x : Vec ℝ n => fun i => x ⬝ᵥ (Q i *ᵥ x)) '' cZ.construct
      ⊆ (cZ.quadMap Q).construct := by -- --- PROOF ---
  -- the square's coefficient `2pⱼ² - 1`, `pⱼ²`'s image of `[-1, 1]`
  rintro _ ⟨x, ⟨p, hp, hP, rfl⟩, rfl⟩
  have hq : ∀ j, |2 * (p j) ^ 2 - 1| ≤ 1 := fun j => by
    have h1 := abs_le.mp (hp j)
    rw [abs_le]; constructor <;> nlinarith [h1.1, h1.2]
  -- the new coefficient vector: the point's own, the squares, the products
  set β := Fin.append (Fin.append p (fun j => 2 * (p j) ^ 2 - 1))
    (fun l => p (finProdFinEquiv.symm l).1 * p (finProdFinEquiv.symm l).2) with hβ
  refine ⟨β, Fin.addCases (Fin.addCases
      (fun j => by rw [hβ, Fin.append_left, Fin.append_left]; exact hp j)
      (fun j => by rw [hβ, Fin.append_left, Fin.append_right]; exact hq j))
    (fun l => by
      simp only [hβ, Fin.append_right, abs_mul]
      exact mul_le_one₀ (hp _) (abs_nonneg _) (hp _)), ?_, ?_⟩
  · show (blockLeft cZ.h cZ.h) ((blockLeft (cZ.h + cZ.h) (cZ.h * cZ.h)) β) ∈ cZ.P.construct
    rw [hβ, blockLeft_append, blockLeft_append]
    exact hP
  -- coordinate `i` is the bilinear form of `Q i` at `(x, x)`
  funext i
  show (cZ.c + ∑ j, p j • cZ.G j) ⬝ᵥ (Q i *ᵥ (cZ.c + ∑ j, p j • cZ.G j))
    = ((Zonotope.quadMap Q ⟨cZ.h, cZ.c, cZ.G⟩).c
        + ∑ j, β j • (Zonotope.quadMap Q ⟨cZ.h, cZ.c, cZ.G⟩).G j) i
  rw [Pi.add_apply, Finset.sum_apply, Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [Zonotope.quadMap, hβ, Fin.append_left, Fin.append_right, Pi.smul_apply, smul_eq_mul]
  have hb : ∀ u v : Vec ℝ n, u ⬝ᵥ (Q i *ᵥ v) = Matrix.toBilin' (Q i) u v := fun u v => by
    rw [Matrix.toBilin'_apply']
  simp only [hb]
  rw [ConZonotope.aux_quadMap_sq, ConZonotope.aux_quadMap_diagpair]
  rw [ConZonotope.aux_quadMap_pairblock (fun j k => p j * p k * (if j < k then
    Matrix.toBilin' (Q i) (cZ.G j) (cZ.G k) + Matrix.toBilin' (Q i) (cZ.G k) (cZ.G j) else 0))]
  have hpairs : ∀ j k : Fin cZ.h, p j * p k * (if j < k then
      Matrix.toBilin' (Q i) (cZ.G j) (cZ.G k) + Matrix.toBilin' (Q i) (cZ.G k) (cZ.G j) else 0)
      = if j < k then p j * p k * (Matrix.toBilin' (Q i) (cZ.G j) (cZ.G k)
          + Matrix.toBilin' (Q i) (cZ.G k) (cZ.G j)) else 0 := fun j k => by
    split_ifs <;> ring
  simp only [hpairs]
  -- the pairs guard their own factor, and `pⱼ² = 0.5 + 0.5(2pⱼ² - 1)` on the diagonal
  have hdiag : ∑ j, p j * p j * Matrix.toBilin' (Q i) (cZ.G j) (cZ.G j)
      = 1 / 2 * ∑ j, Matrix.toBilin' (Q i) (cZ.G j) (cZ.G j)
        + ∑ j, (2 * p j ^ 2 - 1) * (1 / 2 * Matrix.toBilin' (Q i) (cZ.G j) (cZ.G j)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hdiag]
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
