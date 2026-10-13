import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
import CORALean.ContSet.Zonotope.Real.Theorems.SqNormLeMaxNormSq
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# A zonotope as an ellipsoid

The coefficient domains differ only in the norm they bound: a zonotope's cube is
`‖β‖∞ ≤ 1`, an ellipsoid's ball is `‖u‖₂ ≤ 1`, and the cube sits inside `√h`
times the ball. So the same generators scaled by `√h` enclose, and the only
square root is that one scalar — which is the whole reason the generator form is
worth storing.

Loose by a factor of `√h` in the worst direction and exact in none, since a
zonotope is not an ellipsoid. Tighter enclosures exist — CORA's are the
minimum-volume and minimum-trace ones — and both are optimisation problems
rather than conversions. This one is the initial ellipse `E₀ = (m/2) G Gᵀ` of [2, Sec. 4.1].

CORA's `'outer:norm'` and `'inner:norm'` are [1, Thm. 1] and [1, Thm. 3]: shape `r E₀` for a
factor `F` of the initial guess `E₀ = F Fᵀ` (`m G Gᵀ` and `G Gᵀ`) and a bound `r` on the maximum,
or below the minimum, norm of `F⁻¹ Z` ([1, Def. 3], [1, Def. 4]). `ellipsoidNorm` and
`ellipsoidInnerNorm` take `F` and `r`; the guarantees hold for every invertible `F`, the paper's
`E₀^{-1/2}` among them, and every bound — exact or `[1, Lemma 3]`'s.

## References

* [1] V. Gaßmann and M. Althoff. "Scalable Zonotope-Ellipsoid Conversions using the Euclidean
      Zonotope Norm". In Proc. of the 2020 American Control Conference (ACC), pp. 4715-4721,
      2020.
* [2] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}

noncomputable def Zonotope.ellipsoid (Z : Zonotope (Vec ℝ n)) : Ellipsoid n where
  k := Z.h
  q := Z.c
  G := Matrix.of fun i j => Real.sqrt Z.h * Z.G j i


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Each coefficient contributes at most `1/h` of the ball's budget, so `h` of
them fit exactly. -/
theorem Zonotope.aux_coeff_sq_le {Z : Zonotope (Vec ℝ n)} {β : Fin Z.h → ℝ}
    (hβ : ∀ j, |β j| ≤ 1) (j : Fin Z.h) :
    (β j / Real.sqrt Z.h) ^ 2 ≤ 1 / (Z.h : ℝ) := by -- --- PROOF ---
  have hh : (0:ℝ) < (Z.h : ℝ) := by exact_mod_cast j.pos
  have hsq : Real.sqrt (Z.h : ℝ) ^ 2 = (Z.h : ℝ) := Real.sq_sqrt (le_of_lt hh)
  have hb : β j ^ 2 ≤ 1 := by
    rw [← sq_abs]
    calc |β j| ^ 2 = |β j| * |β j| := pow_two _
      _ ≤ 1 * 1 := mul_le_mul (hβ j) (hβ j) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  rw [div_pow, hsq, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hb (le_of_lt (inv_pos.mpr hh))


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.ellipsoid_contains (Z : Zonotope (Vec ℝ n)) :
    Z.construct ⊆ Z.ellipsoid.construct := by -- --- PROOF ---
  intro x hx
  obtain ⟨β, hβ, hxeq⟩ := Zonotope.mem_construct_iff.mp hx
  refine ⟨fun j => β j / Real.sqrt Z.h, ?_, ?_⟩
  -- `h` coefficients each within `1/h` of the budget fill the ball exactly
  · have hsum : ∑ j : Fin Z.h, (β j / Real.sqrt Z.h) ^ 2 ≤ 1 := by
      calc ∑ j : Fin Z.h, (β j / Real.sqrt Z.h) ^ 2
          ≤ ∑ _j : Fin Z.h, 1 / (Z.h : ℝ) :=
            Finset.sum_le_sum fun j _ => Zonotope.aux_coeff_sq_le hβ j
        _ = (Z.h : ℝ) * (1 / (Z.h : ℝ)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ 1 := by
            rcases Nat.eq_zero_or_pos Z.h with h0 | h0
            · rw [h0]
              norm_num
            · have hh : (0:ℝ) < (Z.h : ℝ) := by exact_mod_cast h0
              refine le_of_eq ?_
              rw [mul_one_div, div_self (ne_of_gt hh)]
    calc ‖fun j => β j / Real.sqrt Z.h‖₂ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hsum
      _ = 1 := Real.sqrt_one
  -- and the value: the `√h` in the generator cancels the one in the coefficient
  · funext i
    show x i = Z.c i + ∑ j, Real.sqrt Z.h * Z.G j i * (β j / Real.sqrt Z.h)
    rw [hxeq i]
    refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun j _ => ?_)
    have hne : Real.sqrt (Z.h : ℝ) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast j.pos))
    field_simp

/-- [1, Thm. 1]: `E(r E₀, z̄)` with `E₀ = F Fᵀ`, as the generator `√r F`. -/
noncomputable def Zonotope.ellipsoidNorm (Z : Zonotope (Vec ℝ n)) (F : Mat ℝ n n) (r : ℝ) :
    Ellipsoid n where
  k := n
  q := Z.c
  G := √r • F

/-- [1, Thm. 1]: `r` bounding `⌈F⁻¹ Z⌉²` makes `E(r F Fᵀ, z̄)` enclose `Z`. -/
theorem Zonotope.ellipsoidNorm_contains (Z : Zonotope (Vec ℝ n)) (F : Mat ℝ n n) (r : ℝ)
    (hF : IsUnit F.det)
    (hr : (⟨Z.h, F⁻¹ *ᵥ Z.c, fun j => F⁻¹ *ᵥ Z.G j⟩ : Zonotope (Vec ℝ n)).maxNormSq ≤ r) :
    Z.construct ⊆ (Z.ellipsoidNorm F r).construct := by -- --- PROOF ---
  rintro _ ⟨β, hβ, rfl⟩
  -- the transformed point `v = F⁻¹ ∑ βⱼ gⱼ` is no longer than `√r`
  set v : Vec ℝ n := ∑ j, β j • (F⁻¹ *ᵥ Z.G j) with hv
  have hvle : ‖v‖₂ ^ 2 ≤ r :=
    le_trans (Zonotope.sq_norm₂_le_maxNormSq ⟨Z.h, F⁻¹ *ᵥ Z.c, fun j => F⁻¹ *ᵥ Z.G j⟩ hβ) hr
  have hFv : F *ᵥ v = ∑ j, β j • Z.G j := by
    simp only [hv, Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv F hF, Matrix.one_mulVec]
  have hr0 : 0 ≤ r := le_trans (sq_nonneg _) hvle
  rcases hr0.eq_or_lt with hr0 | hrpos
  -- `r = 0`: the point is the centre
  · subst hr0
    have hv0 : v = 0 := by
      rw [← dotProduct_self_eq_zero, dotProduct_self]
      nlinarith [norm₂_nonneg v]
    refine ⟨0, by rw [norm₂_zero]; exact zero_le_one, ?_⟩
    rw [Matrix.mulVec_zero, ← hFv, hv0, Matrix.mulVec_zero]
    rfl
  -- otherwise `u = v / √r` is in the unit ball and `√r F u = F v`
  · have hs : 0 < √r := Real.sqrt_pos.mpr hrpos
    refine ⟨(√r)⁻¹ • v, ?_, ?_⟩
    · show ‖((√r)⁻¹ • v : Vec ℝ n)‖₂ ≤ 1
      rw [norm₂_smul, abs_of_pos (inv_pos.mpr hs), inv_mul_le_iff₀ hs, mul_one]
      calc ‖v‖₂ = √(‖v‖₂ ^ 2) := (Real.sqrt_sq (norm₂_nonneg v)).symm
        _ ≤ √r := Real.sqrt_le_sqrt hvle
    · show Z.c + ∑ j, β j • Z.G j = Z.c + (√r • F) *ᵥ ((√r)⁻¹ • v)
      rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hs.ne', one_smul,
        hFv]

/-- [1, Thm. 3]: `E(l E₀, z̄)` with `E₀ = F Fᵀ`, as the generator `√l F`. -/
noncomputable def Zonotope.ellipsoidInnerNorm (Z : Zonotope (Vec ℝ n)) (F : Mat ℝ n n) (l : ℝ) :
    Ellipsoid n where
  k := n
  q := Z.c
  G := √l • F

/-- [1, Thm. 3]: a ball of radius `√l` around the centre of `F⁻¹ Z` puts `E(l F Fᵀ, z̄)` in
`Z`; `l ≤ ⌊F⁻¹ Z⌋²` is what that ball says. -/
theorem Zonotope.contains_ellipsoidInnerNorm (Z : Zonotope (Vec ℝ n)) (F : Mat ℝ n n) (l : ℝ)
    (hF : IsUnit F.det)
    (hball : ∀ x : Vec ℝ n, ‖x‖₂ ≤ √l → F⁻¹ *ᵥ Z.c + x ∈
      (⟨Z.h, F⁻¹ *ᵥ Z.c, fun j => F⁻¹ *ᵥ Z.G j⟩ : Zonotope (Vec ℝ n)).construct) :
    (Z.ellipsoidInnerNorm F l).construct ⊆ Z.construct := by -- --- PROOF ---
  rintro _ ⟨u, hu, rfl⟩
  -- `√l u` is in the ball, so a point of `F⁻¹ Z`; map it back with `F`
  have hx : ‖√l • u‖₂ ≤ √l := by
    rw [norm₂_smul, abs_of_nonneg (Real.sqrt_nonneg l)]
    exact mul_le_of_le_one_right (Real.sqrt_nonneg l) hu
  obtain ⟨β, hβ, heq⟩ := hball _ hx
  refine ⟨β, hβ, ?_⟩
  have hmap := congrArg (F *ᵥ ·) heq
  simp only [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv F hF, Matrix.one_mulVec] at hmap
  show Z.c + (√l • F) *ᵥ u = Z.c + ∑ j, β j • Z.G j
  rw [Matrix.smul_mulVec, ← Matrix.mulVec_smul]
  exact hmap

/-- [2, Sec. 4.1]: `E(n diag(β₁², …, β_n²), c)` with `βᵢ = ∑ⱼ |Gᵢⱼ|`, the box's ellipsoid. -/
noncomputable def Zonotope.ellipsoidBox (Z : Zonotope (Vec ℝ n)) : Ellipsoid n where
  k := n
  q := Z.c
  G := Matrix.diagonal fun i => Real.sqrt n * ∑ j, |Z.G j i|

/-- [2, Sec. 4.1]: the zonotope lies in the ellipsoid of its bounding box,
`Z ⊆ [c − β, c + β] ⊆ E(n diag(β²), c)`. -/
theorem Zonotope.ellipsoidBox_contains (Z : Zonotope (Vec ℝ n)) :
    Z.construct ⊆ Z.ellipsoidBox.construct := by -- --- PROOF ---
  rintro _ ⟨β, hβ, rfl⟩
  -- the offset in coordinate `i` is at most the box radius `bᵢ = ∑ⱼ |Gⱼᵢ|`
  set b : Fin n → ℝ := fun i => ∑ j, |Z.G j i| with hb
  have hoff : ∀ i, |(∑ j, β j • Z.G j) i| ≤ b i := by
    intro i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (hβ j)
  -- coordinates of the ball point: `oᵢ / (√n bᵢ)`, or `0` on a degenerate axis
  set o : Vec ℝ n := ∑ j, β j • Z.G j with ho
  refine ⟨fun i => if b i = 0 then 0 else o i / (Real.sqrt n * b i), ?_, ?_⟩
  · -- each squared coordinate is at most `1/n`
    have hu : ∀ i, (if b i = 0 then 0 else o i / (Real.sqrt n * b i)) ^ 2 ≤ 1 / (n : ℝ) := by
      intro i
      have hn : (0:ℝ) < n := by exact_mod_cast i.pos
      by_cases h0 : b i = 0
      · simp [h0]
      · have hbpos : 0 < b i := lt_of_le_of_ne
          (Finset.sum_nonneg fun j _ => abs_nonneg _) (Ne.symm h0)
        simp only [h0, if_false]
        have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn.le
        rw [div_pow, mul_pow, hsq, div_le_div_iff₀ (by positivity) hn]
        have := sq_le_sq' (abs_le.1 (hoff i)).1 (abs_le.1 (hoff i)).2
        nlinarith [mul_nonneg hn.le (sq_nonneg (b i))]
    -- so the squares sum to at most `1`
    have hsum : ∑ i, (if b i = 0 then 0 else o i / (Real.sqrt n * b i)) ^ 2 ≤ 1 := by
      calc _ ≤ ∑ _i : Fin n, 1 / (n : ℝ) := Finset.sum_le_sum fun i _ => hu i
        _ = (n : ℝ) * (1 / (n : ℝ)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ 1 := by
            rcases Nat.eq_zero_or_pos n with h0 | h0
            · rw [h0]; norm_num
            · have hh : (0:ℝ) < n := by exact_mod_cast h0
              exact le_of_eq (by rw [mul_one_div, div_self hh.ne'])
    calc ‖fun i => if b i = 0 then 0 else o i / (Real.sqrt n * b i)‖₂ ≤ Real.sqrt 1 :=
          Real.sqrt_le_sqrt hsum
      _ = 1 := Real.sqrt_one
  · -- and the diagonal generator maps it back to the offset
    funext i
    show (Z.c + o) i = Z.c i + (Matrix.diagonal (fun i => Real.sqrt n * b i) *ᵥ
      fun i => if b i = 0 then 0 else o i / (Real.sqrt n * b i)) i
    rw [Matrix.mulVec_diagonal]
    by_cases h0 : b i = 0
    · have : o i = 0 := abs_nonpos_iff.1 (by simpa [h0] using hoff i)
      simp [h0, this]
    · have hn : (0:ℝ) < n := by exact_mod_cast i.pos
      simp only [h0, if_false, Pi.add_apply]
      have : Real.sqrt n ≠ 0 := (Real.sqrt_pos.2 hn).ne'
      field_simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
