module

public import CORALean.HybridDynamics.Definitions.HitPoint
public import CORALean.HybridDynamics.Definitions.HitJacobian
public import CORALean.HybridDynamics.Definitions.HitHessianNum
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Convex.Basic

@[expose] public section

/-!
# The first-order Taylor series of `y_h` with Lagrange remainder

[1, Prop. 3, Eq. 17]: for `x₀, ξ` in a convex `R(0)` on which `Λ = nᵀ(Ax₀ + b)` does not vanish,
`y_{h,i}(x₀) = y_{h,i}(ξ) + L_i(ξ)ν + ½νᵀ(φQ⁽ⁱ⁾(x))ν`, `ν = x₀ - ξ`, for some `x ∈ R(0)` and some
`φ` in any interval `[φ̲, φ̄]` holding `{1/Λ(x₀)² | x₀ ∈ R(0)}`: the remainder lies in
`½νᵀ([φ̲, φ̄] ⊗ Q⁽ⁱ⁾)ν`. The point `x` is that of Lagrange's form, on the segment from `ξ` to `x₀`,
and is per coordinate `i`, as is `φ`: [1, Sec. 5.4] encloses all coordinates at once.

Along the segment `s ↦ ξ + sν`, `Λ` and `d - nᵀx` are affine in `s`, and `Θ(x)ᵀν =
-Λ(x)nᵀν - (d - nᵀx)Υν` does not depend on `s`; so `y_{h,i}` is a rational function of `s` whose
first two derivatives are `L_i ν` and `νᵀQ⁽ⁱ⁾ν/Λ²`, and the one-variable theorem applies.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Set

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Taylor's theorem of order one with Lagrange remainder on `[0, 1]`. -/
theorem aux_hitPoint_taylor_one {g g' g'' : ℝ → ℝ} (hg : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g (g' t) t)
    (hg' : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g' (g'' t) t) :
    ∃ e ∈ Ioo (0 : ℝ) 1, g 1 = g 0 + g' 0 + g'' e / 2 := by -- --- PROOF ---
  have hlin : ∀ t : ℝ, HasDerivAt (fun s : ℝ => s * g' 0) (g' 0) t := fun t => by
    simpa using (hasDerivAt_id t).mul_const (g' 0)
  -- Cauchy's mean value theorem for `g(s) - s g'(0)` against `s²` on `[0, 1]`
  obtain ⟨c, hc, hcauchy⟩ := exists_ratio_hasDerivAt_eq_ratio_slope
    (fun s => g s - s * g' 0) (fun s => g' s - g' 0) zero_lt_one
    (fun t ht => ((hg t ht).continuousAt.sub
      (continuous_id.mul continuous_const).continuousAt).continuousWithinAt)
    (fun t ht => (hg t (Ioo_subset_Icc_self ht)).sub (hlin t))
    (fun s => s ^ 2) (fun s => 2 * s)
    (continuous_pow 2).continuousOn (fun t _ => by simpa using hasDerivAt_pow 2 t)
  -- Lagrange's mean value theorem for `g'` on `[0, c]`
  have hsub : Icc 0 c ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl hc.2.le
  obtain ⟨e, he, hlag⟩ := exists_hasDerivAt_eq_slope g' g'' hc.1
    (fun t ht => (hg' t (hsub ht)).continuousAt.continuousWithinAt)
    (fun t ht => hg' t (hsub (Ioo_subset_Icc_self ht)))
  refine ⟨e, ⟨he.1, he.2.trans hc.2⟩, ?_⟩
  rw [sub_zero, eq_div_iff hc.1.ne'] at hlag
  simp only [one_pow, zero_pow two_ne_zero, sub_zero, one_mul, zero_mul] at hcauchy
  have key : (g 1 - g 0 - g' 0) * (2 * c) = g'' e * c := by
    rw [← hlag] at hcauchy
    linarith
  have hc0 : 0 < c := hc.1
  field_simp
  nlinarith [key]

/-- `νᵀQ⁽ⁱ⁾(x)ν = 2(Aν)ᵢ θ - 2θ(Υν)(Ax + b)ᵢ/Λ(x)`, `θ = Θ(x)ᵀν`: `Ω` is antisymmetric. -/
theorem aux_quad_hitHessianNum (A : Mat ℝ n n) (b nv : Vec ℝ n) (d : ℝ) (x ν : Vec ℝ n)
    (i : Fin n) : -- --- STMT ---
    ν ⬝ᵥ (GuardMap.hitHessianNum A b nv d x i *ᵥ ν)
      = 2 * (A *ᵥ ν) i * (-(nv ⬝ᵥ (A *ᵥ x + b)) * (nv ⬝ᵥ ν) - (d - nv ⬝ᵥ x) * (nv ⬝ᵥ (A *ᵥ ν)))
        - 2 * (-(nv ⬝ᵥ (A *ᵥ x + b)) * (nv ⬝ᵥ ν) - (d - nv ⬝ᵥ x) * (nv ⬝ᵥ (A *ᵥ ν)))
          * (nv ⬝ᵥ (A *ᵥ ν)) * (A *ᵥ x + b) i / (nv ⬝ᵥ (A *ᵥ x + b)) := by -- --- PROOF ---
  set Λ : ℝ := nv ⬝ᵥ (A *ᵥ x + b)
  set Υ : Vec ℝ n := nv ᵥ* A
  set Θ : Vec ℝ n := -(Λ • nv) - (d - nv ⬝ᵥ x) • Υ
  set F : ℝ := (A *ᵥ x + b) i
  -- the matrix as a sum of outer products
  have hQ : GuardMap.hitHessianNum A b nv d x i = vecMulVec (fun l => A i l) Θ
      + vecMulVec Θ (fun l => A i l) + F • (-vecMulVec nv Υ + vecMulVec Υ nv)
      - (2 * F / Λ) • vecMulVec Θ Υ := by
    ext l m
    simp only [GuardMap.hitHessianNum, Matrix.of_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.neg_apply, vecMulVec_apply, smul_eq_mul]
    ring
  have hΥν : Υ ⬝ᵥ ν = nv ⬝ᵥ (A *ᵥ ν) := (dotProduct_mulVec nv A ν).symm
  have hΘν : Θ ⬝ᵥ ν = -Λ * (nv ⬝ᵥ ν) - (d - nv ⬝ᵥ x) * (nv ⬝ᵥ (A *ᵥ ν)) := by
    simp only [Θ, sub_dotProduct, neg_dotProduct, smul_dotProduct, smul_eq_mul, hΥν]
    ring
  have hAν : ν ⬝ᵥ (fun l => A i l) = (A *ᵥ ν) i := by
    simp only [dotProduct, mulVec]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  -- `νᵀ(u wᵀ)ν = (νᵀu)(wᵀν)`, term by term
  have hvv : ∀ u w : Vec ℝ n, ν ⬝ᵥ (vecMulVec u w *ᵥ ν) = (ν ⬝ᵥ u) * (w ⬝ᵥ ν) := fun u w => by
    rw [vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, smul_eq_mul, mul_comm]
  rw [hQ, sub_mulVec, add_mulVec, add_mulVec, smul_mulVec, smul_mulVec, add_mulVec, neg_mulVec,
    dotProduct_sub, dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul,
    dotProduct_add, dotProduct_neg, hvv, hvv, hvv, hvv, hvv, smul_eq_mul, smul_eq_mul, hΘν, hAν,
    hΥν, dotProduct_comm ν Θ, hΘν, dotProduct_comm ν Υ, hΥν, dotProduct_comm (fun l => A i l) ν,
    hAν, dotProduct_comm ν nv]
  ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 3, Eq. 17]: `y_{h,i}(x₀) ∈ (y_{h,i}(ξ) + L_i(ξ)ν) ⊕ ½νᵀ([φ̲, φ̄] ⊗ Q⁽ⁱ⁾)ν`,
`ν = x₀ - ξ`, `Q⁽ⁱ⁾ = {Q⁽ⁱ⁾(x) | x ∈ R(0)}`. -/
theorem GuardMap.hitPoint_mem_taylor {A : Mat ℝ n n} {b nv : Vec ℝ n} {d : ℝ}
    {R₀ : Set (Vec ℝ n)} (hR₀ : Convex ℝ R₀) (hΛ : ∀ y ∈ R₀, nv ⬝ᵥ (A *ᵥ y + b) ≠ 0)
    {φlo φhi : ℝ} (hφ : ∀ y ∈ R₀, ((nv ⬝ᵥ (A *ᵥ y + b)) ^ 2)⁻¹ ∈ Icc φlo φhi)
    {ξ x₀ : Vec ℝ n} (hξ : ξ ∈ R₀) (hx₀ : x₀ ∈ R₀) (i : Fin n) : -- --- STMT ---
    ∃ φ ∈ Icc φlo φhi, ∃ y ∈ R₀,
      GuardMap.hitPoint A b nv d x₀ i = GuardMap.hitPoint A b nv d ξ i
        + (GuardMap.hitJacobian A b nv d ξ *ᵥ (x₀ - ξ)) i
        + 1 / 2 * ((x₀ - ξ) ⬝ᵥ
          ((φ • GuardMap.hitHessianNum A b nv d y i) *ᵥ (x₀ - ξ))) := by -- --- PROOF ---
  set ν : Vec ℝ n := x₀ - ξ with hνdef
  -- along `s ↦ ξ + sν`: `Λ = Λ₀ + sβ`, `d - nᵀx = D₀ - sa`, `(Ax + b)ᵢ = F₀ + sγ`
  set Λ₀ : ℝ := nv ⬝ᵥ (A *ᵥ ξ + b)
  set β : ℝ := nv ⬝ᵥ (A *ᵥ ν) with hβdef
  set D₀ : ℝ := d - nv ⬝ᵥ ξ
  set a : ℝ := nv ⬝ᵥ ν with hadef
  set F₀ : ℝ := (A *ᵥ ξ + b) i with hF₀def
  set γ : ℝ := (A *ᵥ ν) i with hγdef
  set κ : ℝ := -a * Λ₀ - D₀ * β
  -- the segment stays in `R(0)`, where `Λ ≠ 0`
  have hseg : ∀ s ∈ Icc (0 : ℝ) 1, ξ + s • ν ∈ R₀ := fun s hs =>
    hR₀.add_smul_sub_mem hξ hx₀ hs
  have hΛs : ∀ s : ℝ, nv ⬝ᵥ (A *ᵥ (ξ + s • ν) + b) = Λ₀ + s * β := fun s => by
    simp only [Λ₀, β, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul]
    ring
  -- `d - nᵀx` and `(Ax + b)ᵢ` likewise
  have hDs : ∀ s : ℝ, d - nv ⬝ᵥ (ξ + s • ν) = D₀ - s * a := fun s => by
    simp only [D₀, a, dotProduct_add, dotProduct_smul, smul_eq_mul]; ring
  have hFs : ∀ s : ℝ, (A *ᵥ (ξ + s • ν) + b) i = F₀ + s * γ := fun s => by
    simp only [F₀, γ, mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hne : ∀ s ∈ Icc (0 : ℝ) 1, Λ₀ + s * β ≠ 0 := fun s hs => by
    rw [← hΛs]; exact hΛ _ (hseg s hs)
  -- `y_{h,i}` along the segment and its first two derivatives
  let g : ℝ → ℝ := fun s => ξ i + s * ν i + (D₀ - s * a) / (Λ₀ + s * β) * (F₀ + s * γ)
  let g' : ℝ → ℝ := fun s => ν i + κ / (Λ₀ + s * β) ^ 2 * (F₀ + s * γ)
    + (D₀ - s * a) / (Λ₀ + s * β) * γ
  let g'' : ℝ → ℝ := fun s => -2 * κ * β * (F₀ + s * γ) / (Λ₀ + s * β) ^ 3
    + 2 * κ * γ / (Λ₀ + s * β) ^ 2
  -- the affine pieces, then the quotient and product rules
  have hlin : ∀ (c k t : ℝ), HasDerivAt (fun s : ℝ => c + s * k) k t := fun c k t => by
    simpa using ((hasDerivAt_id t).mul_const k).const_add c
  have hlin' : ∀ (c k t : ℝ), HasDerivAt (fun s : ℝ => c - s * k) (-k) t := fun c k t => by
    simpa using ((hasDerivAt_id t).mul_const k).const_sub c
  have hg : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g (g' t) t := fun t ht => by
    have h := ((hlin (ξ i) (ν i) t).add
      (((hlin' D₀ a t).div (hlin Λ₀ β t) (hne t ht)).mul (hlin F₀ γ t)))
    refine h.congr_deriv ?_
    have := hne t ht
    simp only [g', κ, Pi.div_apply]
    field_simp
    ring
  -- and once more for `g'`
  have hg' : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g' (g'' t) t := fun t ht => by
    have hnt := hne t ht
    have h := ((hasDerivAt_const t (ν i)).add
      (((hasDerivAt_const t κ).div ((hlin Λ₀ β t).pow 2) (pow_ne_zero 2 hnt)).mul
        (hlin F₀ γ t))).add (((hlin' D₀ a t).div (hlin Λ₀ β t) hnt).mul_const γ)
    refine h.congr_deriv ?_
    simp only [g'', κ, Pi.div_apply, Pi.pow_apply]
    field_simp
    ring
  -- Taylor at `0`, the remainder at `e`, the point `y = ξ + eν` and `φ = 1/Λ(y)²`
  obtain ⟨e, he, htay⟩ := aux_hitPoint_taylor_one hg hg'
  have heI : e ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self he
  set y : Vec ℝ n := ξ + e • ν with hydef
  refine ⟨((nv ⬝ᵥ (A *ᵥ y + b)) ^ 2)⁻¹, hφ y (hseg e heI), y, hseg e heI, ?_⟩
  -- the three terms, matched
  have hpt : ∀ s : ℝ, GuardMap.hitPoint A b nv d (ξ + s • ν) i = g s := fun s => by
    simp only [GuardMap.hitPoint, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hDs, hΛs, hFs, g]
  have h1 : g 1 = GuardMap.hitPoint A b nv d x₀ i := by
    rw [← hpt, one_smul, hνdef, add_sub_cancel]
  have h0 : g 0 = GuardMap.hitPoint A b nv d ξ i := by
    rw [← hpt, zero_smul, add_zero]
  have hΘν : (-(Λ₀ • nv) - D₀ • (nv ᵥ* A)) ⬝ᵥ ν = κ := by
    simp only [sub_dotProduct, neg_dotProduct, smul_dotProduct, smul_eq_mul, κ, a, β,
      ← dotProduct_mulVec]
    ring
  -- the first derivative at `ξ` is `L_i(ξ)ν`
  have hd1 : g' 0 = (GuardMap.hitJacobian A b nv d ξ *ᵥ ν) i := by
    -- `L = I + (D₀/Λ₀)A + Λ₀⁻² f Θᵀ`
    have hL : GuardMap.hitJacobian A b nv d ξ = 1 + (D₀ / Λ₀) • A
        + (Λ₀ ^ 2)⁻¹ • vecMulVec (A *ᵥ ξ + b) (-(Λ₀ • nv) - D₀ • (nv ᵥ* A)) := by
      ext l m
      simp only [GuardMap.hitJacobian, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
        vecMulVec_apply, smul_eq_mul, Λ₀, D₀]
      ring
    rw [hL, add_mulVec, add_mulVec, one_mulVec, smul_mulVec, smul_mulVec, vecMulVec_mulVec,
      op_smul_eq_smul, hΘν]
    simp only [g', Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_mul, add_zero, sub_zero, ← hγdef]
    have := hne 0 (by simp)
    simp only [zero_mul, add_zero] at this
    field_simp
    rw [hF₀def, Pi.add_apply]
    ring
  -- the second, at the remainder point, is `νᵀQ⁽ⁱ⁾ν/Λ²`
  have hd2 : g'' e / 2 = 1 / 2 * (ν ⬝ᵥ ((((nv ⬝ᵥ (A *ᵥ y + b)) ^ 2)⁻¹ •
      GuardMap.hitHessianNum A b nv d y i) *ᵥ ν)) := by
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul, aux_quad_hitHessianNum, hΛs, hDs, hFs,
      ← hadef, ← hβdef, ← hγdef]
    have hnt := hne e heI
    have hκ : -(Λ₀ + e * β) * a - (D₀ - e * a) * β = κ := by simp only [κ]; ring
    rw [hκ]
    simp only [g'']
    generalize Λ₀ + e * β = L at hnt ⊢
    field_simp
    ring
  rw [← h1, ← h0, htay, hd1, hd2]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
