module

public import CORALean.HybridDynamics.Definitions.HitPoint
public import CORALean.HybridDynamics.Operations.HitPointFloat
public import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners
public import CORALean.ContSet.Interval.Float.Theorems.RecipOuter

@[expose] public section

/-!
# The float box holds the hitting point

`GuardMap.hitPointFloat` returns a box only if `Λ = nᵀ(Ax₀ + b)` is certified nonzero, and then
`y_h(x₀)` of the floats read as reals is in it: each rounded quantity brackets its real value,
`Ax₀ + b` and `d − nᵀx₀` by `dotDown_le`/`le_dotUp`, `Λ` and the products by
`mul_between_corners`, `1/Λ` by `Interval.recip_outer`.
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

/-- `y_h(x₀)` is in the box `hitPointFloat` returns, and `Λ ≠ 0`. -/
theorem GuardMap.hitPoint_mem_hitPointFloat (A : Mat 𝕋 n n) (b nv : Vec 𝕋 n) (d : 𝕋)
    (x₀ : Vec 𝕋 n) : -- --- CONCL ---
    ∀ K ∈ GuardMap.hitPointFloat A b nv d x₀,
      toRealVec nv ⬝ᵥ (toRealMat A *ᵥ toRealVec x₀ + toRealVec b) ≠ 0 ∧
        GuardMap.hitPoint (toRealMat A) (toRealVec b) (toRealVec nv) (toReal d) (toRealVec x₀)
          ∈ K.construct := by -- --- PROOF ---
  intro K (hK : GuardMap.hitPointFloat A b nv d x₀ = some K)
  simp only [GuardMap.hitPointFloat] at hK
  split_ifs at hK with hc
  obtain rfl := Option.some.inj hK
  set yr : Vec ℝ n := toRealMat A *ᵥ toRealVec x₀ + toRealVec b with hyr
  set Λ : ℝ := toRealVec nv ⬝ᵥ yr with hΛ
  set num : ℝ := toReal d - toRealVec nv ⬝ᵥ toRealVec x₀ with hnum
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
  -- `Λ = nᵀy`, a sum of corner products
  have hΛb : toReal (sumDown fun i => Interval.mulLo (nv i) (nv i)
      (addDown (dotDown (A i) x₀) (b i)) (addUp (dotUp (A i) x₀) (b i))) ≤ Λ ∧
      Λ ≤ toReal (sumUp fun i => Interval.mulHi (nv i) (nv i)
        (addDown (dotDown (A i) x₀) (b i)) (addUp (dotUp (A i) x₀) (b i))) := by
    have hm := fun i => Interval.mul_between_corners (le_refl (toReal (nv i)))
      (le_refl (toReal (nv i))) (hy i).1 (hy i).2
    exact ⟨(sumDown_le_sum _).trans (Finset.sum_le_sum fun i _ => (hm i).1),
      (Finset.sum_le_sum fun i _ => (hm i).2).trans (sum_le_sumUp _)⟩
  set ΛLo := sumDown fun i => Interval.mulLo (nv i) (nv i)
    (addDown (dotDown (A i) x₀) (b i)) (addUp (dotUp (A i) x₀) (b i)) with hΛLo
  set ΛHi := sumUp fun i => Interval.mulHi (nv i) (nv i)
    (addDown (dotDown (A i) x₀) (b i)) (addUp (dotUp (A i) x₀) (b i)) with hΛHi
  -- `Λ ≠ 0`: the certificate puts its box on one side of `0`
  have hΛ0 : Λ ≠ 0 := by
    rcases Bool.or_eq_true_iff.mp hc with h | h
    · have := toReal_lt_of_ltStrict h
      rw [toReal_zero] at this
      exact (lt_of_lt_of_le this hΛb.1).ne'
    · have := toReal_lt_of_ltStrict h
      rw [toReal_zero] at this
      exact (lt_of_le_of_lt hΛb.2 this).ne
  refine ⟨hΛ0, fun i => ?_⟩
  -- `1/Λ` in the reciprocal box, `num` in its brackets, so `num/Λ` between the corners
  set Λinv := (⟨fun _ => ΛLo, fun _ => ΛHi⟩ : Interval (Vec 𝕋 1)).recip with hΛinv
  have hinv : toReal (Λinv.inf 0) ≤ Λ⁻¹ ∧ Λ⁻¹ ≤ toReal (Λinv.sup 0) :=
    Interval.recip_outer (⟨fun _ => ΛLo, fun _ => ΛHi⟩ : Interval (Vec 𝕋 1))
      (fun _ => Bool.or_eq_true_iff.mp hc) ⟨fun _ : Fin 1 => Λ, fun _ => hΛb, rfl⟩ 0
  have hn1 := subDown_le_sub d (dotUp nv x₀)
  have hn2 := sub_le_subUp d (dotDown nv x₀)
  have hd1 := le_dotUp nv x₀
  have hd2 := dotDown_le nv x₀
  have hnum' : toReal (subDown d (dotUp nv x₀)) ≤ num ∧ num ≤ toReal (subUp d (dotDown nv x₀)) := by
    have e : toRealVec nv ⬝ᵥ toRealVec x₀ = ∑ k, toReal (nv k) * toReal (x₀ k) := rfl
    rw [hnum, e]
    constructor <;> linarith
  have hτ := Interval.mul_between_corners hnum'.1 hnum'.2 hinv.1 hinv.2
  -- `(num/Λ) yᵢ` between the corners, then the directed sums with `x₀ᵢ`
  set τLo := Interval.mulLo (subDown d (dotUp nv x₀)) (subUp d (dotDown nv x₀))
    (Λinv.inf 0) (Λinv.sup 0)
  set τHi := Interval.mulHi (subDown d (dotUp nv x₀)) (subUp d (dotDown nv x₀))
    (Λinv.inf 0) (Λinv.sup 0)
  have hτy := Interval.mul_between_corners hτ.1 hτ.2 (hy i).1 (hy i).2
  have ha1 := addDown_le_add (x₀ i) (Interval.mulLo τLo τHi (addDown (dotDown (A i) x₀) (b i))
    (addUp (dotUp (A i) x₀) (b i)))
  have ha2 := add_le_addUp (x₀ i) (Interval.mulHi τLo τHi (addDown (dotDown (A i) x₀) (b i))
    (addUp (dotUp (A i) x₀) (b i)))
  -- `y_h(x₀)ᵢ = x₀ᵢ + (num/Λ) yᵢ`
  have e : GuardMap.hitPoint (toRealMat A) (toRealVec b) (toRealVec nv) (toReal d)
      (toRealVec x₀) i = toReal (x₀ i) + num * Λ⁻¹ * yr i := by
    simp only [GuardMap.hitPoint, Pi.add_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
    rfl
  show toReal (addDown (x₀ i) (Interval.mulLo τLo τHi (addDown (dotDown (A i) x₀) (b i))
      (addUp (dotUp (A i) x₀) (b i)))) ≤ GuardMap.hitPoint (toRealMat A) (toRealVec b)
      (toRealVec nv) (toReal d) (toRealVec x₀) i ∧ GuardMap.hitPoint (toRealMat A) (toRealVec b)
      (toRealVec nv) (toReal d) (toRealVec x₀) i ≤ toReal (addUp (x₀ i)
        (Interval.mulHi τLo τHi (addDown (dotDown (A i) x₀) (b i)) (addUp (dotUp (A i) x₀) (b i))))
  rw [e]
  constructor <;> linarith [hτy.1, hτy.2]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
