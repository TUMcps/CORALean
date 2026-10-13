module

public import CORALean.ContSet.Zonotope.Real.Operations.QuadMap
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

@[expose] public section

/-!
# The quadratic map of a zonotope is enclosed by `Zonotope.quadMap`

[1, Lemma 1], by the printed proof: insert `x = c + Σⱼ βⱼg⁽ʲ⁾` into `xᵀQ⁽ⁱ⁾x`, split the
double sum into its diagonal and its pairs `j < k`, and read each `βⱼ²` as
`0.5 + 0.5(2βⱼ² - 1)` — the constant half into the centre, the rest onto the square's
generator. The coefficients `βⱼ`, `2βⱼ² - 1` and `βⱼβₖ` all lie in `[-1, 1]`, which is
where the enclosure is lost: they are tied to each other, and a zonotope frees them.

One coordinate at a time, `xᵀQ⁽ⁱ⁾x` being the bilinear form `Matrix.toBilin' (Q i)` at
`(x, x)`; the coefficients are the same for every coordinate.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {V : Type} [AddCommGroup V] [Module ℝ V]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `b(c + Σ pⱼgⱼ, c + Σ pⱼgⱼ)` expanded: constant, linear, and every ordered pair. -/
theorem Zonotope.aux_quadMap_sq {h : ℕ} (b : LinearMap.BilinForm ℝ V) (c : V) (g : Fin h → V)
    (p : Fin h → ℝ) :
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
theorem Zonotope.aux_quadMap_diagpair {h : ℕ} (b : LinearMap.BilinForm ℝ V) (g : Fin h → V)
    (p : Fin h → ℝ) :
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
theorem Zonotope.aux_quadMap_pairblock {h : ℕ} (f : Fin h → Fin h → ℝ) :
    ∑ l : Fin (h * h), f (finProdFinEquiv.symm l).1 (finProdFinEquiv.symm l).2
      = ∑ j, ∑ k, f j k := by
  rw [Fintype.sum_equiv finProdFinEquiv.symm _ (fun jk : Fin h × Fin h => f jk.1 jk.2)
    fun _ => rfl]
  exact Fintype.sum_prod_type _


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 1]: `{λ | λᵢ = xᵀQ⁽ⁱ⁾x, x ∈ Z} ⊆ Z.quadMap Q`. -/
theorem Zonotope.quadMap_outer {n m : ℕ} (Q : Fin m → Mat ℝ n n) (Z : Zonotope (Vec ℝ n)) :
    (fun x : Vec ℝ n => fun i => x ⬝ᵥ (Q i *ᵥ x)) '' Z.construct
      ⊆ (Z.quadMap Q).construct := by -- --- PROOF ---
  rintro _ ⟨x, ⟨p, hp, rfl⟩, rfl⟩
  -- the square's coefficient `2pⱼ² - 1`, `pⱼ²`'s image of `[-1, 1]`
  have hq : ∀ j, |2 * (p j) ^ 2 - 1| ≤ 1 := fun j => by
    have h1 := abs_le.mp (hp j)
    rw [abs_le]; constructor <;> nlinarith [h1.1, h1.2]
  set β := Fin.append (Fin.append p (fun j => 2 * (p j) ^ 2 - 1))
    (fun l => p (finProdFinEquiv.symm l).1 * p (finProdFinEquiv.symm l).2) with hβ
  refine ⟨β, Fin.addCases (Fin.addCases
      (fun j => by rw [hβ, Fin.append_left, Fin.append_left]; exact hp j)
      (fun j => by rw [hβ, Fin.append_left, Fin.append_right]; exact hq j))
    (fun l => by
      simp only [hβ, Fin.append_right, abs_mul]
      exact mul_le_one₀ (hp _) (abs_nonneg _) (hp _)), ?_⟩
  funext i
  show (Z.c + ∑ j, p j • Z.G j) ⬝ᵥ (Q i *ᵥ (Z.c + ∑ j, p j • Z.G j))
    = ((Z.quadMap Q).c + ∑ j, β j • (Z.quadMap Q).G j) i
  rw [Pi.add_apply, Finset.sum_apply, Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [Zonotope.quadMap, hβ, Fin.append_left, Fin.append_right, Pi.smul_apply, smul_eq_mul]
  -- coordinate `i` is the bilinear form of `Q i` at `(x, x)`
  have hb : ∀ u v : Vec ℝ n, u ⬝ᵥ (Q i *ᵥ v) = Matrix.toBilin' (Q i) u v := fun u v => by
    rw [Matrix.toBilin'_apply']
  simp only [hb]
  rw [Zonotope.aux_quadMap_sq, Zonotope.aux_quadMap_diagpair]
  rw [Zonotope.aux_quadMap_pairblock (fun j k => p j * p k * (if j < k then
    Matrix.toBilin' (Q i) (Z.G j) (Z.G k) + Matrix.toBilin' (Q i) (Z.G k) (Z.G j) else 0))]
  -- the pairs guard their own factor, and `pⱼ² = 0.5 + 0.5(2pⱼ² - 1)` on the diagonal
  have hpairs : ∀ j k : Fin Z.h, p j * p k * (if j < k then
      Matrix.toBilin' (Q i) (Z.G j) (Z.G k) + Matrix.toBilin' (Q i) (Z.G k) (Z.G j) else 0)
      = if j < k then p j * p k * (Matrix.toBilin' (Q i) (Z.G j) (Z.G k)
          + Matrix.toBilin' (Q i) (Z.G k) (Z.G j)) else 0 := fun j k => by
    split_ifs <;> ring
  simp only [hpairs]
  have hdiag : ∑ j, p j * p j * Matrix.toBilin' (Q i) (Z.G j) (Z.G j)
      = 1 / 2 * ∑ j, Matrix.toBilin' (Q i) (Z.G j) (Z.G j)
        + ∑ j, (2 * p j ^ 2 - 1) * (1 / 2 * Matrix.toBilin' (Q i) (Z.G j) (Z.G j)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hdiag]
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
