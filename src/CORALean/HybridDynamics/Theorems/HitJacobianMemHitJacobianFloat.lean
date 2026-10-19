module

public import CORALean.HybridDynamics.Definitions.HitJacobian
public import CORALean.HybridDynamics.Operations.HitJacobianFloat
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners
public import CORALean.ContSet.Interval.Float.Theorems.RecipOuter

@[expose] public section

/-!
# The float interval matrix holds the Jacobian of the hitting point

`GuardMap.hitJacobianFloat` returns an interval matrix only if `Λ = nᵀ(Ax₀ + b)` is certified
nonzero, and then `L(x₀)` of the floats read as reals is in it, entry by entry: each rounded
quantity brackets its real value (`dotDown_le`, `le_dotUp`, `mul_between_corners`,
`Interval.recip_outer`), and `L_il = I_il + A_il(num · Λ⁻¹) + (yᵢΘ_l)(Λ⁻¹Λ⁻¹)`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float CORALean.Float.FloatOps CORALean.Float.SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `L(x₀)` is in the interval matrix `hitJacobianFloat` returns. -/
theorem GuardMap.hitJacobian_mem_hitJacobianFloat (A : Mat 𝕋 n n) (b nv : Vec 𝕋 n) (d : 𝕋)
    (x₀ : Vec 𝕋 n) : -- --- CONCL ---
    ∀ L ∈ GuardMap.hitJacobianFloat A b nv d x₀,
      GuardMap.hitJacobian (toRealMat A) (toRealVec b) (toRealVec nv) (toReal d) (toRealVec x₀)
        ∈ L.construct := by -- --- PROOF ---
  intro L (hL : GuardMap.hitJacobianFloat A b nv d x₀ = some L)
  simp only [GuardMap.hitJacobianFloat] at hL
  split_ifs at hL with hc
  obtain rfl := Option.some.inj hL
  set yr : Vec ℝ n := toRealMat A *ᵥ toRealVec x₀ + toRealVec b with hyr
  set Λ : ℝ := toRealVec nv ⬝ᵥ yr with hΛ
  set num : ℝ := toReal d - toRealVec nv ⬝ᵥ toRealVec x₀ with hnum
  set Υ : Vec ℝ n := toRealVec nv ᵥ* toRealMat A with hΥ
  -- `Ax₀ + b`, entry by entry
  have hy : ∀ i, toReal (addDown (dotDown (A i) x₀) (b i)) ≤ yr i ∧
      yr i ≤ toReal (addUp (dotUp (A i) x₀) (b i)) := fun i => by
    have h1 := dotDown_le (A i) x₀
    have h2 := le_dotUp (A i) x₀
    have h3 := addDown_le_add (dotDown (A i) x₀) (b i)
    have h4 := add_le_addUp (dotUp (A i) x₀) (b i)
    have e : yr i = ∑ k, toReal (A i k) * toReal (x₀ k) + toReal (b i) := rfl
    rw [e]
    constructor <;> linarith
  set ΛLo := sumDown fun i => Interval.mulLo (nv i) (nv i)
    (addDown (dotDown (A i) x₀) (b i)) (addUp (dotUp (A i) x₀) (b i)) with hΛLo
  set ΛHi := sumUp fun i => Interval.mulHi (nv i) (nv i)
    (addDown (dotDown (A i) x₀) (b i)) (addUp (dotUp (A i) x₀) (b i)) with hΛHi
  -- `Λ = nᵀy`, a sum of corner products
  have hΛb : toReal ΛLo ≤ Λ ∧ Λ ≤ toReal ΛHi := by
    have hm := fun i => Interval.mul_between_corners (le_refl (toReal (nv i)))
      (le_refl (toReal (nv i))) (hy i).1 (hy i).2
    exact ⟨(sumDown_le_sum _).trans (Finset.sum_le_sum fun i _ => (hm i).1),
      (Finset.sum_le_sum fun i _ => (hm i).2).trans (sum_le_sumUp _)⟩
  -- `1/Λ` and `1/Λ²` in their boxes
  set Λinv := (⟨fun _ => ΛLo, fun _ => ΛHi⟩ : Interval (Vec 𝕋 1)).recip with hΛinv
  have hinv : toReal (Λinv.inf 0) ≤ Λ⁻¹ ∧ Λ⁻¹ ≤ toReal (Λinv.sup 0) :=
    Interval.recip_outer (⟨fun _ => ΛLo, fun _ => ΛHi⟩ : Interval (Vec 𝕋 1))
      (fun _ => Bool.or_eq_true_iff.mp hc) ⟨fun _ : Fin 1 => Λ, fun _ => hΛb, rfl⟩ 0
  have hinv2 := Interval.mul_between_corners hinv.1 hinv.2 hinv.1 hinv.2
  -- `num = d − nᵀx₀`, and `num/Λ`
  have hnum' : toReal (subDown d (dotUp nv x₀)) ≤ num ∧ num ≤ toReal (subUp d (dotDown nv x₀)) := by
    have hn1 := subDown_le_sub d (dotUp nv x₀)
    have hn2 := sub_le_subUp d (dotDown nv x₀)
    have hd1 := le_dotUp nv x₀
    have hd2 := dotDown_le nv x₀
    have e : toRealVec nv ⬝ᵥ toRealVec x₀ = ∑ k, toReal (nv k) * toReal (x₀ k) := rfl
    rw [hnum, e]
    constructor <;> linarith
  have hτ := Interval.mul_between_corners hnum'.1 hnum'.2 hinv.1 hinv.2
  -- `Υ = nᵀA` and `Θ = −nΛ − num Υ`, entry by entry
  have hΥb : ∀ l, toReal (dotDown nv fun j => A j l) ≤ Υ l ∧
      Υ l ≤ toReal (dotUp nv fun j => A j l) := fun l =>
    ⟨dotDown_le nv fun j => A j l, le_dotUp nv fun j => A j l⟩
  have hΘ : ∀ l, toReal (subDown (neg (Interval.mulHi ΛLo ΛHi (nv l) (nv l)))
      (Interval.mulHi (subDown d (dotUp nv x₀)) (subUp d (dotDown nv x₀))
        (dotDown nv fun j => A j l) (dotUp nv fun j => A j l))) ≤ -(Λ * toReal (nv l)) - num * Υ l ∧
      -(Λ * toReal (nv l)) - num * Υ l ≤ toReal (subUp (neg (Interval.mulLo ΛLo ΛHi (nv l) (nv l)))
      (Interval.mulLo (subDown d (dotUp nv x₀)) (subUp d (dotDown nv x₀))
        (dotDown nv fun j => A j l) (dotUp nv fun j => A j l))) := fun l => by
    have h1 := Interval.mul_between_corners hΛb.1 hΛb.2 (le_refl (toReal (nv l)))
      (le_refl (toReal (nv l)))
    have h2 := Interval.mul_between_corners hnum'.1 hnum'.2 (hΥb l).1 (hΥb l).2
    -- the two directed differences
    have h3 := subDown_le_sub (neg (Interval.mulHi ΛLo ΛHi (nv l) (nv l)))
      (Interval.mulHi (subDown d (dotUp nv x₀)) (subUp d (dotDown nv x₀))
        (dotDown nv fun j => A j l) (dotUp nv fun j => A j l))
    have h4 := sub_le_subUp (neg (Interval.mulLo ΛLo ΛHi (nv l) (nv l)))
      (Interval.mulLo (subDown d (dotUp nv x₀)) (subUp d (dotDown nv x₀))
        (dotDown nv fun j => A j l) (dotUp nv fun j => A j l))
    rw [toReal_neg] at h3 h4
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  refine Interval.mem_mat_iff.mpr fun i l => ?_
  dsimp only
  -- the three terms of `L_il`
  have hδ : toReal (if i = l then (one : 𝕋) else zero) = (1 : Mat ℝ n n) i l := by
    by_cases h : i = l <;> simp [h, toReal_one, toReal_zero, Matrix.one_apply]
  have ht1 := Interval.mul_between_corners (le_refl (toReal (A i l))) (le_refl (toReal (A i l)))
    hτ.1 hτ.2
  have hyΘ := Interval.mul_between_corners (hy i).1 (hy i).2 (hΘ l).1 (hΘ l).2
  have ht2 := Interval.mul_between_corners hyΘ.1 hyΘ.2 hinv2.1 hinv2.2
  have e : GuardMap.hitJacobian (toRealMat A) (toRealVec b) (toRealVec nv) (toReal d)
      (toRealVec x₀) i l = (1 : Mat ℝ n n) i l + toReal (A i l) * (num * Λ⁻¹)
        + yr i * (-(Λ * toReal (nv l)) - num * Υ l) * (Λ⁻¹ * Λ⁻¹) := by
    simp only [GuardMap.hitJacobian, Matrix.of_apply]
    change (1 : Mat ℝ n n) i l + toReal (A i l) / Λ * num
        + yr i * (-(Λ * toReal (nv l)) - num * Υ l) / Λ ^ 2 = _
    rw [div_eq_mul_inv, div_eq_mul_inv, pow_two, mul_inv]
    ring
  rw [e]
  -- each end: two directed sums of the bracketed terms
  constructor
  · refine le_trans (addDown_le_add _ _) ?_
    refine le_trans (add_le_add (addDown_le_add _ _) ht2.1) ?_
    rw [hδ]
    linarith [ht1.1]
  · refine le_trans ?_ (add_le_addUp _ _)
    refine le_trans ?_ (add_le_add (add_le_addUp _ _) ht2.2)
    rw [hδ]
    linarith [ht1.2]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
