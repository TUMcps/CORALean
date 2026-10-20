module

public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-!
# The homogeneous S-lemma

Yakubovich's S-lemma for two quadratic forms `P`, `Q` on a real vector space, under Slater's
condition `Q z₀ < 0`: `P` is non-negative wherever `Q` is negative iff `P + δ Q ≥ 0` for some
`δ ≥ 0` (the theorem of alternatives of [1, Thm. 13]). A form is given by its expansion
`P (u • x + v • y) = u² P x + v² P y + u v · pP x y`, so no finite dimension is needed. The
argument is Dines': on the plane spanned by `x` and `y`, a rotation making them `Q`-orthogonal
leaves `Q x + Q y` and `P x + P y` unchanged, and one of the diagonals `x' ± y'` keeps `Q` at the
sum and `P` at most at it. So the points dominating some `(P z, Q z)` form a convex cone missing the
open negative quadrant, and a line through the origin separates them (`geometric_hahn_banach_open`).

## Inputs
* `P` – first quadratic form
* `Q` – second quadratic form
* `pP` – polarization of the first form
* `pQ` – polarization of the second form

## Hypotheses
* `hP` – the first form obeys its expansion
* `hQ` – the second form obeys its expansion
* `h₀` – some point makes the second form negative

## Conclusion
* the first form is nonnegative where the second is negative exactly when a multiplier corrects it

## References

* [1] A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for
      Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control, 2025.
      doi:10.1109/TAC.2025.3583624. arXiv:2404.11185.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {V : Type*} [AddCommGroup V] [Module ℝ V]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Of two vectors of the plane, some unit vector makes a non-positive product with both. -/
theorem aux_exists_unit_nonpos (p q r s : ℝ) : -- --- CONCL ---
    ∃ κ μ : ℝ, κ ^ 2 + μ ^ 2 = 1 ∧ p * κ + q * μ ≤ 0 ∧ r * κ + s * μ ≤ 0 := by -- --- PROOF ---
  by_cases h0 : p ^ 2 + q ^ 2 = 0
  · have hp : p = 0 := by nlinarith [sq_nonneg p, sq_nonneg q]
    have hq : q = 0 := by nlinarith [sq_nonneg p, sq_nonneg q]
    subst hp hq
    rcases le_total 0 r with hr | hr
    · exact ⟨-1, 0, by norm_num, by norm_num, by linarith⟩
    · exact ⟨1, 0, by norm_num, by norm_num, by linarith⟩
  -- a unit normal of `(p, q)`, its sign chosen against `(r, s)`
  have hpos : 0 < p ^ 2 + q ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
  have hN : 0 < √(p ^ 2 + q ^ 2) := Real.sqrt_pos.mpr hpos
  have hN2 : √(p ^ 2 + q ^ 2) ^ 2 = p ^ 2 + q ^ 2 := Real.sq_sqrt hpos.le
  have hunit : (q / √(p ^ 2 + q ^ 2)) ^ 2 + (p / √(p ^ 2 + q ^ 2)) ^ 2 = 1 := by
    rw [div_pow, div_pow, ← add_div, hN2, add_comm, div_self h0]
  rcases le_total (r * (-q / √(p ^ 2 + q ^ 2)) + s * (p / √(p ^ 2 + q ^ 2))) 0 with h | h
  · refine ⟨-q / √(p ^ 2 + q ^ 2), p / √(p ^ 2 + q ^ 2), ?_, le_of_eq (by ring), h⟩
    rw [neg_div, neg_sq]; exact hunit
  · refine ⟨q / √(p ^ 2 + q ^ 2), -p / √(p ^ 2 + q ^ 2), ?_, le_of_eq (by ring), ?_⟩
    · rw [neg_div, neg_sq]; exact hunit
    · have : r * (q / √(p ^ 2 + q ^ 2)) + s * (-p / √(p ^ 2 + q ^ 2)) =
          -(r * (-q / √(p ^ 2 + q ^ 2)) + s * (p / √(p ^ 2 + q ^ 2))) := by ring
      rw [this]; linarith

/-- A point `(κ, μ)` of the unit circle is `(u² - 1, u v)` on the circle `u² + v² = 2`. -/
theorem aux_exists_uv {κ μ : ℝ} (h : κ ^ 2 + μ ^ 2 = 1) : -- --- CONCL ---
    ∃ u v : ℝ, u ^ 2 = 1 + κ ∧ v ^ 2 = 1 - κ ∧ u * v = μ := by -- --- PROOF ---
  have hκ : -1 ≤ κ := by nlinarith [sq_nonneg μ, sq_nonneg (κ + 1)]
  rcases hκ.lt_or_eq with hlt | heq
  · have hpos : 0 < 1 + κ := by linarith
    have hu : √(1 + κ) ^ 2 = 1 + κ := Real.sq_sqrt hpos.le
    have hu0 : √(1 + κ) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    refine ⟨√(1 + κ), μ / √(1 + κ), hu, ?_, by field_simp⟩
    rw [div_pow, hu, div_eq_iff hpos.ne']
    nlinarith
  · have hμ : μ = 0 := by rw [← heq] at h; nlinarith [sq_nonneg μ]
    refine ⟨0, √2, by rw [← heq]; ring, ?_, by rw [hμ]; ring⟩
    rw [Real.sq_sqrt (by norm_num), ← heq]; ring

/-- A form is homogeneous of degree two. -/
theorem aux_map_smul (P : V → ℝ) (pP : V → V → ℝ)
    (hP : ∀ (u v : ℝ) (x y : V), P (u • x + v • y) = u ^ 2 * P x + v ^ 2 * P y + u * v * pP x y)
    (s : ℝ) (x : V) : P (s • x) = s ^ 2 * P x := by
  simpa using hP s 0 x x

/-- Dines: some `z` has `P z ≤ P x + P y` and `Q z ≤ Q x + Q y`. -/
theorem aux_exists_le_add (P Q : V → ℝ) (pP pQ : V → V → ℝ)
    (hP : ∀ (u v : ℝ) (x y : V), P (u • x + v • y) = u ^ 2 * P x + v ^ 2 * P y + u * v * pP x y)
    (hQ : ∀ (u v : ℝ) (x y : V), Q (u • x + v • y) = u ^ 2 * Q x + v ^ 2 * Q y + u * v * pQ x y)
    (x y : V) : -- --- CONCL ---
    ∃ z, P z ≤ P x + P y ∧ Q z ≤ Q x + Q y := by -- --- PROOF ---
  obtain ⟨κ, μ, hc, h1, h2⟩ := aux_exists_unit_nonpos (P x - P y) (pP x y) (Q x - Q y) (pQ x y)
  obtain ⟨u, v, hu, hv, huv⟩ := aux_exists_uv hc
  -- `z = u x + v y`: each form moves by `κ (F x - F y) + μ · pF x y ≤ 0`
  refine ⟨u • x + v • y, ?_, ?_⟩
  · rw [hP, hu, hv, huv]; linear_combination h1
  · rw [hQ, hu, hv, huv]; linear_combination h2

/-- The S-lemma with the strict hypothesis `Q z < 0 → 0 ≤ P z`. -/
theorem aux_exists_delta (P Q : V → ℝ) (pP pQ : V → V → ℝ)
    (hP : ∀ (u v : ℝ) (x y : V), P (u • x + v • y) = u ^ 2 * P x + v ^ 2 * P y + u * v * pP x y)
    (hQ : ∀ (u v : ℝ) (x y : V), Q (u • x + v • y) = u ^ 2 * Q x + v ^ 2 * Q y + u * v * pQ x y)
    (z₀ : V) (hz₀ : Q z₀ < 0) (h : ∀ z, Q z < 0 → 0 ≤ P z) : -- --- CONCL ---
    ∃ δ : ℝ, 0 ≤ δ ∧ ∀ z, 0 ≤ P z + δ * Q z := by -- --- PROOF ---
  -- the points dominating some `(P z, Q z)`: a convex cone
  set C : Set (ℝ × ℝ) := {p | ∃ z, P z ≤ p.1 ∧ Q z ≤ p.2} with hCdef
  have hC : Convex ℝ C := by
    rintro p ⟨z, hz1, hz2⟩ p' ⟨z', hz1', hz2'⟩ a b ha hb -
    obtain ⟨w, hw1, hw2⟩ := aux_exists_le_add P Q pP pQ hP hQ (√a • z) (√b • z')
    rw [aux_map_smul P pP hP, aux_map_smul P pP hP, Real.sq_sqrt ha, Real.sq_sqrt hb] at hw1
    rw [aux_map_smul Q pQ hQ, aux_map_smul Q pQ hQ, Real.sq_sqrt ha, Real.sq_sqrt hb] at hw2
    refine ⟨w, ?_, ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_left hz1 ha, mul_le_mul_of_nonneg_left hz1' hb]
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_left hz2 ha, mul_le_mul_of_nonneg_left hz2' hb]
  -- closed under scaling, and holding the non-negative quadrant
  have hCsmul : ∀ p ∈ C, ∀ k : ℝ, 0 ≤ k → k • p ∈ C := by
    rintro p ⟨z, hz1, hz2⟩ k hk
    refine ⟨√k • z, ?_, ?_⟩
    · rw [aux_map_smul P pP hP, Real.sq_sqrt hk, Prod.smul_fst, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left hz1 hk
    · rw [aux_map_smul Q pQ hQ, Real.sq_sqrt hk, Prod.smul_snd, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left hz2 hk
  have hP0 : P 0 = 0 := by simpa using aux_map_smul P pP hP 0 0
  have hQ0 : Q 0 = 0 := by simpa using aux_map_smul Q pQ hQ 0 0
  have hCnn : ∀ t s : ℝ, 0 ≤ t → 0 ≤ s → (t, s) ∈ C := fun t s ht hs =>
    ⟨0, by rw [hP0]; exact ht, by rw [hQ0]; exact hs⟩
  -- the open negative quadrant, which `C` misses
  set N : Set (ℝ × ℝ) := {p | p.1 < 0 ∧ p.2 < 0} with hNdef
  have hNo : IsOpen N :=
    (isOpen_lt continuous_fst continuous_const).inter (isOpen_lt continuous_snd continuous_const)
  have hNc : Convex ℝ N := by
    rintro p ⟨h1, h2⟩ p' ⟨h1', h2'⟩ a b ha hb hab
    simp only [hNdef, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left (le_max_left p.1 p'.1) ha,
        mul_le_mul_of_nonneg_left (le_max_right p.1 p'.1) hb, max_lt h1 h1']
    · nlinarith [mul_le_mul_of_nonneg_left (le_max_left p.2 p'.2) ha,
        mul_le_mul_of_nonneg_left (le_max_right p.2 p'.2) hb, max_lt h2 h2']
  have hdisj : Disjoint N C := Set.disjoint_left.mpr fun p ⟨h1, h2⟩ ⟨z, hz1, hz2⟩ => by
    have := h z (by linarith); linarith
  obtain ⟨f, u, hfN, hfC⟩ := geometric_hahn_banach_open hNc hNo hC hdisj
  -- `f` is `(p₁, p₂) ↦ l p₁ + m p₂`, non-negative on the cone
  have hf : ∀ p : ℝ × ℝ, f p = f (1, 0) * p.1 + f (0, 1) * p.2 := fun p => by
    have hp : p = p.1 • ((1 : ℝ), (0 : ℝ)) + p.2 • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    conv_lhs => rw [hp]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_comm, mul_comm p.2]
  -- `0 ∈ C` puts the level `u` below zero, scaling puts `f` above it on all of `C`
  have hu0 : u ≤ 0 := by
    have := hfC (0, 0) (hCnn 0 0 le_rfl le_rfl)
    rwa [Prod.mk_zero_zero, map_zero] at this
  have hfnn : ∀ p ∈ C, 0 ≤ f p := fun p hp => by
    by_contra hneg
    push Not at hneg
    have hk : 0 ≤ (1 - u) / -f p := div_nonneg (by linarith) (by linarith)
    have := hfC _ (hCsmul p hp _ hk)
    have hval : (1 - u) / -f p * f p = u - 1 := by
      rw [div_neg, neg_mul, div_mul_cancel₀ _ hneg.ne]; ring
    rw [map_smul, smul_eq_mul, hval] at this
    linarith
  -- the normal `(l, m)` is non-negative and non-zero
  have hl : 0 ≤ f (1, 0) := hfnn _ (hCnn 1 0 zero_le_one le_rfl)
  have hm : 0 ≤ f (0, 1) := hfnn _ (hCnn 0 1 le_rfl zero_le_one)
  have hlm : 0 < f (1, 0) + f (0, 1) := by
    have := hfN (-1, -1) ⟨by norm_num, by norm_num⟩
    rw [hf] at this; linarith
  have hz : ∀ z, 0 ≤ f (1, 0) * P z + f (0, 1) * Q z := fun z => by
    have := hfnn (P z, Q z) ⟨z, le_rfl, le_rfl⟩
    rwa [hf] at this
  -- Slater's condition rules out `l = 0`
  have hlpos : 0 < f (1, 0) := by
    rcases hl.lt_or_eq with hlt | heq
    · exact hlt
    · have := hz z₀
      rw [← heq] at this hlm
      nlinarith
  refine ⟨f (0, 1) / f (1, 0), div_nonneg hm hl, fun z => ?_⟩
  have : P z + f (0, 1) / f (1, 0) * Q z = (f (1, 0) * P z + f (0, 1) * Q z) / f (1, 0) := by
    field_simp
  rw [this]
  exact div_nonneg (hz z) hlpos.le


-- =======================================  MAIN THEOREM  ======================================= --

/-- The homogeneous S-lemma: under `Q z₀ < 0`, `Q < 0 → 0 ≤ P` iff `P + δ Q ≥ 0`, `δ ≥ 0`. -/
theorem s_lemma_homogeneous (P Q : V → ℝ) (pP pQ : V → V → ℝ)
    (hP : ∀ (u v : ℝ) (x y : V), P (u • x + v • y) = u ^ 2 * P x + v ^ 2 * P y + u * v * pP x y)
    (hQ : ∀ (u v : ℝ) (x y : V), Q (u • x + v • y) = u ^ 2 * Q x + v ^ 2 * Q y + u * v * pQ x y)
    (h₀ : ∃ z₀, Q z₀ < 0) : -- --- CONCL ---
    (∀ z, Q z < 0 → 0 ≤ P z) ↔ ∃ δ : ℝ, 0 ≤ δ ∧ ∀ z, 0 ≤ P z + δ * Q z := by -- --- PROOF ---
  obtain ⟨z₀, hz₀⟩ := h₀
  refine ⟨aux_exists_delta P Q pP pQ hP hQ z₀ hz₀, fun ⟨δ, hδ, h⟩ z hz => ?_⟩
  nlinarith [h z]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
