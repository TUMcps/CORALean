import CORALean.HybridDynamics.Definitions.HitEnclosure
import CORALean.HybridDynamics.Definitions.HitSet
import CORALean.HybridDynamics.Theorems.HitHessianNumEqHitHessianMatZono
import CORALean.ContSet.Zonotope.Real.Theorems.QuadMapMatZonoOuter
import CORALean.ContSet.Zonotope.Real.Theorems.UnitIntervalMulOuter
import CORALean.ContSet.Zonotope.Real.Theorems.Convex

/-!
# `R_g` encloses every `R_h(x₀)`, with `Θ/Λ` enclosed as a vector

[1, Sec. 5.4]: `R_g = y_h(ξ) ⊕ L ⊗ (R(0) ⊕ (−ξ)) ⊕ ½[φ̲, φ̄] ⊗ R_quad ⊕ R_{h,E}(R(0))` holds the
set `R_h(x₀)` of eq. (15) for every `x₀ ∈ R(0)`, given `Λ ≠ 0` on `R(0)`, `ξ ∈ R(0)`,
`[φ̲, φ̄] ⊇ {1/Λ(x₀)² | x₀ ∈ R(0)}`, and `ψ_c`, `ψ_g` with `Θ(x₀)/Λ(x₀) ∈ ψ_c ⊕ [-1, 1]ψ_g` as
vectors, one factor for all coordinates (the reading of (19) under which [1, Prop. 3] holds).

The paper's route, `Prop. 3` coordinate by coordinate, puts each `y_{h,i}`'s remainder at its
own Lagrange point with its own `φ`, which `R_quad` (one factor per generator for all
coordinates) and the single `[φ̲, φ̄]` do not hold together. The proof goes another way: with
`ν = x₀ − ξ` the remainder is exact and shared,
`y_h(x₀) = y_h(ξ) + L(ξ)ν + ½ φ (νᵀQ⁽ⁱ⁾(ξ)ν)ᵢ`, `φ = 1/(Λ(ξ)Λ(x₀))`,
since `y_h` is a ratio whose denominator `Λ` is affine: `νᵀQ⁽ⁱ⁾(ξ)ν = 2(Θ(ξ)ᵀν)((Aν)ᵢ −
(Υν)(Aξ + b)ᵢ/Λ(ξ))`, `Ω` dropping out of the form. `Q⁽ⁱ⁾(ξ)` is one point of all the matrix
zonotopes with the same factors (`GuardMap.hitHessianNum_eq_hitHessianMatZono`), so the vector
lies in `R_quad` by [1, Thm. 1] with shared factors (`Zonotope.quadMapMatZono_outer`); `φ` is
the geometric mean of `1/Λ(ξ)²` and `1/Λ(x₀)²`, `Λ` keeping its sign on the convex `R(0)`; and
`R_{h,E}(x₀) ⊆ R_{h,E}(R(0))` at `a = Λ(x₀) ∈ I`.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `νᵀQ⁽ⁱ⁾(ξ)ν = 2(Θᵀν)(Aν)ᵢ − 2(Θᵀν)(Υν)(Aξ + b)ᵢ/Λ`: `Ω` is skew. -/
theorem aux_hitEncl_quad (A : Mat ℝ n n) (b nv : Vec ℝ n) (d : ℝ) (ξ ν : Vec ℝ n) (i : Fin n) :
    ν ⬝ᵥ (GuardMap.hitHessianNum A b nv d ξ i *ᵥ ν) =
      2 * (A *ᵥ ν) i * ((-((nv ⬝ᵥ (A *ᵥ ξ + b)) • nv) - (d - nv ⬝ᵥ ξ) • (nv ᵥ* A)) ⬝ᵥ ν)
      - 2 * ((-((nv ⬝ᵥ (A *ᵥ ξ + b)) • nv) - (d - nv ⬝ᵥ ξ) • (nv ᵥ* A)) ⬝ᵥ ν)
        * ((nv ᵥ* A) ⬝ᵥ ν) * (A *ᵥ ξ + b) i / (nv ⬝ᵥ (A *ᵥ ξ + b)) := by -- --- PROOF ---
  set Λ : ℝ := nv ⬝ᵥ (A *ᵥ ξ + b)
  set Υ : Vec ℝ n := nv ᵥ* A
  set Θ : Vec ℝ n := -(Λ • nv) - (d - nv ⬝ᵥ ξ) • Υ
  set f : Vec ℝ n := A *ᵥ ξ + b
  have hM : GuardMap.hitHessianNum A b nv d ξ i =
      vecMulVec (fun l => A i l) Θ + vecMulVec Θ (fun l => A i l)
        + f i • (-vecMulVec nv Υ + vecMulVec Υ nv) - (2 * f i / Λ) • vecMulVec Θ Υ := by
    ext l m
    simp only [GuardMap.hitHessianNum, of_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.neg_apply, vecMulVec_apply, smul_eq_mul]
    ring
  have hrow : (fun l => A i l) ⬝ᵥ ν = (A *ᵥ ν) i := rfl
  rw [hM, sub_mulVec, add_mulVec, add_mulVec, smul_mulVec, smul_mulVec, add_mulVec, neg_mulVec]
  simp only [vecMulVec_mulVec, dotProduct_sub, dotProduct_add, dotProduct_smul, dotProduct_neg,
    smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  rw [dotProduct_comm ν (fun l => A i l), hrow, dotProduct_comm ν Θ, dotProduct_comm ν nv,
    dotProduct_comm ν Υ, dotProduct_comm nv ν]
  ring

/-- The exact second-order expansion: `y_h(ξ + ν) = y_h(ξ) + L(ξ)ν + ½ φ (νᵀQ⁽ⁱ⁾(ξ)ν)ᵢ`,
`φ = 1/(Λ(ξ)Λ(ξ + ν))`. -/
theorem aux_hitEncl_eq (A : Mat ℝ n n) (b nv : Vec ℝ n) (d : ℝ) (ξ ν : Vec ℝ n)
    (hξ : nv ⬝ᵥ (A *ᵥ ξ + b) ≠ 0) (hx : nv ⬝ᵥ (A *ᵥ (ξ + ν) + b) ≠ 0) :
    GuardMap.hitPoint A b nv d (ξ + ν) = GuardMap.hitPoint A b nv d ξ
      + GuardMap.hitJacobian A b nv d ξ *ᵥ ν
      + (1 / 2 : ℝ) • ((1 / ((nv ⬝ᵥ (A *ᵥ ξ + b)) * (nv ⬝ᵥ (A *ᵥ (ξ + ν) + b)))) •
        fun i => ν ⬝ᵥ (GuardMap.hitHessianNum A b nv d ξ i *ᵥ ν)) := by -- --- PROOF ---
  -- `L(ξ) = I + (d - nᵀξ)/Λ · A + (Ax + b)Θᵀ/Λ²`
  have hJ : GuardMap.hitJacobian A b nv d ξ = 1 + ((d - nv ⬝ᵥ ξ) / nv ⬝ᵥ (A *ᵥ ξ + b)) • A
      + (1 / (nv ⬝ᵥ (A *ᵥ ξ + b)) ^ 2) • vecMulVec (A *ᵥ ξ + b)
        (-((nv ⬝ᵥ (A *ᵥ ξ + b)) • nv) - (d - nv ⬝ᵥ ξ) • (nv ᵥ* A)) := by
    ext i l
    simp only [GuardMap.hitJacobian, of_apply, Matrix.add_apply, Matrix.smul_apply,
      vecMulVec_apply, smul_eq_mul]
    ring
  -- the quadratic form and `Θ(ξ)ᵀν = -Λ(ξ)nᵀν - (d - nᵀξ)Υν`
  have hq : (fun i => ν ⬝ᵥ (GuardMap.hitHessianNum A b nv d ξ i *ᵥ ν)) = fun i =>
      2 * (A *ᵥ ν) i * ((-((nv ⬝ᵥ (A *ᵥ ξ + b)) • nv) - (d - nv ⬝ᵥ ξ) • (nv ᵥ* A)) ⬝ᵥ ν)
      - 2 * ((-((nv ⬝ᵥ (A *ᵥ ξ + b)) • nv) - (d - nv ⬝ᵥ ξ) • (nv ᵥ* A)) ⬝ᵥ ν)
        * ((nv ᵥ* A) ⬝ᵥ ν) * (A *ᵥ ξ + b) i / (nv ⬝ᵥ (A *ᵥ ξ + b)) :=
    funext fun i => aux_hitEncl_quad A b nv d ξ ν i
  have hT : (-((nv ⬝ᵥ (A *ᵥ ξ + b)) • nv) - (d - nv ⬝ᵥ ξ) • (nv ᵥ* A)) ⬝ᵥ ν
      = -((nv ⬝ᵥ (A *ᵥ ξ + b)) * (nv ⬝ᵥ ν)) - (d - nv ⬝ᵥ ξ) * ((nv ᵥ* A) ⬝ᵥ ν) := by
    rw [sub_dotProduct, neg_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul,
      smul_eq_mul]
  -- `A(ξ + ν) + b`, `nᵀ(ξ + ν)` and `Λ(ξ + ν) = Λ(ξ) + Υν`
  have e1 : A *ᵥ (ξ + ν) + b = (A *ᵥ ξ + b) + A *ᵥ ν := by rw [mulVec_add]; abel
  have e3 : nv ⬝ᵥ ((A *ᵥ ξ + b) + A *ᵥ ν) = nv ⬝ᵥ (A *ᵥ ξ + b) + (nv ᵥ* A) ⬝ᵥ ν := by
    rw [dotProduct_add, dotProduct_mulVec]
  have e2 : nv ⬝ᵥ (ξ + ν) = nv ⬝ᵥ ξ + nv ⬝ᵥ ν := dotProduct_add _ _ _
  rw [e1, e3] at hx ⊢
  rw [hJ, hq]
  funext i
  simp only [GuardMap.hitPoint, add_mulVec, smul_mulVec, one_mulVec, vecMulVec_mulVec,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, e1, e2, e3, hT, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  -- one identity of rational functions in the scalars left
  generalize nv ⬝ᵥ (A *ᵥ ξ + b) = Λ at *
  generalize (nv ᵥ* A) ⬝ᵥ ν = δ at *
  generalize nv ⬝ᵥ ξ = nξ at *
  generalize nv ⬝ᵥ ν = η at *
  generalize (A *ᵥ ν) i = Aν at *
  generalize (A *ᵥ ξ) i = f₁ at *
  field_simp
  ring

/-- `Λ` keeps its sign on `R(0)`, so `1/(Λ(ξ)Λ(x₀))` lies in `[φ̲, φ̄]`. -/
theorem aux_hitEncl_phi (A : Mat ℝ n n) (b nv : Vec ℝ n) (R₀ : Real.Zonotope (Vec ℝ n))
    {φlo φhi : ℝ} (hΛ : ∀ x ∈ R₀.construct, nv ⬝ᵥ (A *ᵥ x + b) ≠ 0)
    (hφ : ∀ x ∈ R₀.construct, φlo ≤ 1 / (nv ⬝ᵥ (A *ᵥ x + b)) ^ 2 ∧
      1 / (nv ⬝ᵥ (A *ᵥ x + b)) ^ 2 ≤ φhi)
    {ξ x₀ : Vec ℝ n} (hξ : ξ ∈ R₀.construct) (hx₀ : x₀ ∈ R₀.construct) :
    φlo ≤ 1 / ((nv ⬝ᵥ (A *ᵥ ξ + b)) * (nv ⬝ᵥ (A *ᵥ x₀ + b))) ∧
      1 / ((nv ⬝ᵥ (A *ᵥ ξ + b)) * (nv ⬝ᵥ (A *ᵥ x₀ + b))) ≤ φhi := by -- --- PROOF ---
  -- same sign: else `Λ` vanishes on the segment, which lies in the convex `R(0)`
  have hpq : 0 < (nv ⬝ᵥ (A *ᵥ ξ + b)) * (nv ⬝ᵥ (A *ᵥ x₀ + b)) := by
    have hseg : ∀ t : ℝ, nv ⬝ᵥ (A *ᵥ (t • ξ + (1 - t) • x₀) + b)
        = t * (nv ⬝ᵥ (A *ᵥ ξ + b)) + (1 - t) * (nv ⬝ᵥ (A *ᵥ x₀ + b)) := fun t => by
      simp only [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul]
      ring
    have hp0 := hΛ ξ hξ
    have hq0 := hΛ x₀ hx₀
    generalize nv ⬝ᵥ (A *ᵥ ξ + b) = p at *
    generalize nv ⬝ᵥ (A *ᵥ x₀ + b) = q at *
    rcases lt_or_gt_of_ne (mul_ne_zero hp0 hq0) with hneg | hpos
    · exfalso
      -- `t = q/(q - p)` puts `Λ` at zero on the segment
      have hqp : q - p ≠ 0 := fun h => by
        have : q = p := by linarith
        subst this; nlinarith [mul_self_nonneg q]
      have hsign : (0 < q ∧ p < 0) ∨ (q < 0 ∧ 0 < p) := by
        rcases lt_or_gt_of_ne hp0 with h | h
        · exact Or.inl ⟨by nlinarith, h⟩
        · exact Or.inr ⟨by nlinarith, h⟩
      -- `t ∈ [0, 1]` since `p`, `q` have opposite signs
      have ht0 : 0 ≤ q / (q - p) := by
        rcases hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact div_nonneg h1.le (by linarith)
        · exact div_nonneg_of_nonpos h1.le (by linarith)
      have ht1 : 0 ≤ 1 - q / (q - p) := by
        have e : 1 - q / (q - p) = -p / (q - p) := by field_simp; ring
        rw [e]
        rcases hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact div_nonneg (by linarith) (by linarith)
        · exact div_nonneg_of_nonpos (by linarith) (by linarith)
      -- the zero is a point of `R(0)`, against `Λ ≠ 0` there
      have hmem : (q / (q - p)) • ξ + (1 - q / (q - p)) • x₀ ∈ R₀.construct :=
        Real.Zonotope.convex_construct R₀ hξ hx₀ ht0 ht1 (by ring)
      apply hΛ _ hmem
      rw [hseg]
      field_simp
      ring
    · exact hpos
  -- `1/(pq)` is the geometric mean of `1/p²` and `1/q²`
  obtain ⟨hlo₁, hhi₁⟩ := hφ ξ hξ
  obtain ⟨hlo₂, hhi₂⟩ := hφ x₀ hx₀
  have hp0 := hΛ ξ hξ
  have hq0 := hΛ x₀ hx₀
  generalize nv ⬝ᵥ (A *ᵥ ξ + b) = p at *
  generalize nv ⬝ᵥ (A *ᵥ x₀ + b) = q at *
  have hm : 0 < 1 / (p * q) := by positivity
  have hsq : (1 / (p * q)) ^ 2 = 1 / p ^ 2 * (1 / q ^ 2) := by field_simp
  have h1 : 0 ≤ 1 / p ^ 2 := by positivity
  have h2 : 0 ≤ 1 / q ^ 2 := by positivity
  -- the lower and the upper bound, by squaring
  constructor
  · by_contra h
    push Not at h
    have hlo : 0 < φlo := lt_trans hm h
    have e1 : (1 / (p * q)) ^ 2 < φlo ^ 2 := by gcongr
    have e2 : φlo ^ 2 ≤ 1 / p ^ 2 * (1 / q ^ 2) := by
      rw [sq φlo]; exact mul_le_mul hlo₁ hlo₂ hlo.le h1
    linarith
  · by_contra h
    push Not at h
    have h0 : 0 ≤ φhi := le_trans h1 hhi₁
    have e1 : φhi ^ 2 < (1 / (p * q)) ^ 2 := by gcongr
    have e2 : 1 / p ^ 2 * (1 / q ^ 2) ≤ φhi ^ 2 := by
      rw [sq φhi]; exact mul_le_mul hhi₁ hhi₂ h2 h0
    linarith


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 5.4]: `R_h(x₀) ⊆ R_g` for every `x₀ ∈ R(0)`, with `Θ/Λ ∈ ψ_c ⊕ [-1, 1]ψ_g` as a
vector on `R(0)`. -/
theorem GuardMap.hitSet_subset_hitEnclosure (A : Mat ℝ n n) (b nv : Vec ℝ n) (d : ℝ)
    (E : Set (Vec ℝ n)) (R₀ : Real.Zonotope (Vec ℝ n)) (ξ ψc ψg : Vec ℝ n) (φlo φhi : ℝ)
    (hΛ : ∀ x ∈ R₀.construct, nv ⬝ᵥ (A *ᵥ x + b) ≠ 0)
    (hφ : ∀ x ∈ R₀.construct, φlo ≤ 1 / (nv ⬝ᵥ (A *ᵥ x + b)) ^ 2 ∧
      1 / (nv ⬝ᵥ (A *ᵥ x + b)) ^ 2 ≤ φhi)
    (hψ : ∀ x ∈ R₀.construct, ∃ κ : ℝ, |κ| ≤ 1 ∧ (nv ⬝ᵥ (A *ᵥ x + b))⁻¹ •
      (-((nv ⬝ᵥ (A *ᵥ x + b)) • nv) - (d - nv ⬝ᵥ x) • (nv ᵥ* A)) = ψc + κ • ψg)
    (hξ : ξ ∈ R₀.construct) {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ R₀.construct) :
    GuardMap.hitSet A b nv d E x₀
      ⊆ GuardMap.hitEnclosure A b nv d E R₀ ξ ψc ψg φlo φhi := by -- --- PROOF ---
  rintro _ ⟨_, rfl, w, ⟨_, ⟨e, he, rfl⟩, e', he', rfl⟩, rfl⟩
  have hΛξ := hΛ ξ hξ
  have hΛx := hΛ x₀ hx₀
  obtain ⟨κ, hκ, hψξ⟩ := hψ ξ hξ
  obtain ⟨βξ, hβξ, hξeq⟩ := hξ
  obtain ⟨βx, hβx, hxeq⟩ := hx₀
  set ν : Vec ℝ n := x₀ - ξ with hν
  have hx₀ν : x₀ = ξ + ν := by rw [hν]; abel
  set Q := GuardMap.hitHessianMatZono A b nv d R₀ ψc ψg with hQdef
  set φ : ℝ := 1 / ((nv ⬝ᵥ (A *ᵥ ξ + b)) * (nv ⬝ᵥ (A *ᵥ x₀ + b))) with hφdef
  set q : Vec ℝ n := fun i => ν ⬝ᵥ (GuardMap.hitHessianNum A b nv d ξ i *ᵥ ν) with hqdef
  -- the exact expansion of `y_h(x₀)` around `ξ`
  have hexp := aux_hitEncl_eq A b nv d ξ ν hΛξ (by rw [← hx₀ν]; exact hΛx)
  rw [← hx₀ν] at hexp
  -- `ν ∈ R(0) ⊕ (−ξ)`
  have hνmem : ν ∈ (⟨R₀.h, R₀.c - ξ, R₀.G⟩ : Real.Zonotope (Vec ℝ n)).construct := by
    refine ⟨βx, hβx, ?_⟩
    show x₀ - ξ = (R₀.c - ξ) + ∑ j, βx j • R₀.G j
    rw [hxeq]; abel
  -- `Q⁽ⁱ⁾(ξ)` with the factors of `ξ`, shared by every `i`, so `q ∈ R_quad` by Thm. 1
  set fac : Fin (1 + R₀.h + R₀.h) → ℝ := Fin.append (Fin.append ![κ] βξ) fun α => κ * βξ α
    with hfac
  have hfac1 : ∀ j, |fac j| ≤ 1 := fun j => by
    refine Fin.addCases (fun j => ?_) (fun α => ?_) j
    · refine Fin.addCases (fun j => ?_) (fun α => ?_) j
      · rw [hfac, Fin.append_left, Fin.append_left, Fin.fin_one_eq_zero j]; simpa using hκ
      · rw [hfac, Fin.append_left, Fin.append_right]; exact hβξ α
    · rw [hfac, Fin.append_right, abs_mul]
      exact mul_le_one₀ hκ (abs_nonneg _) (hβξ α)
  have hQξ : ∀ i, GuardMap.hitHessianNum A b nv d ξ i = (Q i).c + ∑ j, fac j • (Q i).G j :=
    fun i => by
      have h := GuardMap.hitHessianNum_eq_hitHessianMatZono A b nv d R₀ ψc ψg i βξ κ
        (by rw [← hξeq]; exact hψξ)
      rw [← hξeq] at h
      exact h
  have hqmem : q ∈ (Real.Zonotope.quadMapMatZono (fun i => (Q i).c)
      (fun (j : Fin (1 + R₀.h + R₀.h)) i => (Q i).G j)
      ⟨R₀.h, R₀.c - ξ, R₀.G⟩).construct :=
    Real.Zonotope.quadMapMatZono_outer _ _ _ ⟨ν, hνmem, fac, hfac1, fun i => by
      rw [hqdef]; dsimp only; rw [hQξ i]⟩
  -- `φ ∈ [φ̲, φ̄]`, written as `0.5(φ̲ + φ̄) + 0.5(φ̄ − φ̲)s`, `|s| ≤ 1`
  obtain ⟨hlo, hhi⟩ := aux_hitEncl_phi A b nv R₀ hΛ hφ ⟨βξ, hβξ, hξeq⟩ ⟨βx, hβx, hxeq⟩
  rw [← hφdef] at hlo hhi
  obtain ⟨s, hs, hφs⟩ : ∃ s : ℝ, s ∈ Set.Icc (-1 : ℝ) 1 ∧
      φ = (φlo + φhi) / 2 + (φhi - φlo) / 2 * s := by
    rcases eq_or_lt_of_le (hlo.trans hhi) with heq | hlt
    · exact ⟨0, ⟨by norm_num, by norm_num⟩, by rw [← heq] at hhi ⊢; linarith⟩
    · refine ⟨(φ - (φlo + φhi) / 2) / ((φhi - φlo) / 2), ⟨?_, ?_⟩, ?_⟩
      · rw [le_div_iff₀ (by linarith)]; linarith
      · rw [div_le_iff₀ (by linarith)]; linarith
      · field_simp; ring
  -- assemble `y_h(x₀) + R_{h,E}(x₀)`
  simp only [GuardMap.hitEnclosure]
  have hyh : x₀ + ((d - nv ⬝ᵥ x₀) / (nv ⬝ᵥ (A *ᵥ x₀ + b))) • (A *ᵥ x₀ + b)
      = GuardMap.hitPoint A b nv d x₀ := rfl
  rw [hyh, hexp, ← hqdef, ← hφdef]
  refine Set.add_mem_add (Set.add_mem_add (Set.add_mem_add (Set.mem_singleton _)
    ⟨ν, hνmem, rfl⟩) (Set.smul_mem_smul_set ?_)) (Set.add_mem_add ?_ he')
  · rw [hφs, add_smul, mul_smul]
    exact Set.add_mem_add (Set.smul_mem_smul_set hqmem) (Set.smul_mem_smul_set
      (Real.Zonotope.unitIntervalMul_outer _ ⟨(s, q), ⟨hs, hqmem⟩, rfl⟩))
  · exact ⟨x₀, ⟨βx, hβx, hxeq⟩, e, he, _, ⟨x₀, ⟨βx, hβx, hxeq⟩, rfl⟩, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
