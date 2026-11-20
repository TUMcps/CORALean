module

public import CORALean.ContSet.Zonotope.Float.Operations.QuadMapMixed
public import CORALean.ContSet.Zonotope.Float.Theorems.AbsorbRoundingIfAnyNominal
public import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Float.Theorems.Basic
public import CORALean.ContSet.Zonotope.Float.Theorems.QuadEntryBracket
public import CORALean.ContSet.Zonotope.Float.Theorems.QuadMapFilterOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual

@[expose] public section

/-!
# Float `quadMapMixed` encloses the mixed quadratic image

With `x = Σₐ pₐ z¹ₐ` and `y = Σ_b q_b z²_b` (`p₀ = q₀ = 1`, the other coefficients in `[-1, 1]`),
`xᵀ Q y = Σₐ Σ_b pₐ q_b (z¹ₐᵀ Q z²_b)`: the entry `(0, 0)` is the center and every other entry a
generator with the coefficient `pₐ q_b`, in `[-1, 1]`. The entries are bracketed
(`quadEntry_bracket`); the box takes what the rounding down left. `quadMapFilter` keeps the set.

## Inputs
* `Q` – quadratic form per output coordinate
* `Z₁` – zonotope of the left argument
* `Z₂` – zonotope of the right argument
* `x` – point of `Z₁`
* `y` – point of `Z₂`

## Hypotheses
* `hx` – `x ∈ Z₁`
* `hy` – `y ∈ Z₂`

## Conclusion
* `(xᵀ Q⁽ⁱ⁾ y)ᵢ` lies in the computed zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point of the nominal part as a combination of `[c G]`, the first coefficient one. -/
private theorem Zonotope.aux_quadMapMixed_point {Z : Zonotope (Vec 𝕋 n)} {x : Vec ℝ n}
    (hx : x ∈ nominalSet Z) : -- --- CONCL ---
    ∃ β : Fin Z.h → ℝ, (∀ j, |β j| ≤ 1) ∧
      x = ∑ a, (Fin.cons 1 β : Fin (Z.h + 1) → ℝ) a •
        toRealVec ((Fin.cons Z.c Z.G : Fin (Z.h + 1) → Vec 𝕋 n) a) := by -- --- PROOF ---
  obtain ⟨β, hβ, hxβ⟩ := Zonotope.mem_nominalSet_iff.mp hx
  refine ⟨β, hβ, ?_⟩
  funext i
  rw [Fin.sum_univ_succ]
  simp [hxβ i, Finset.sum_apply, mul_comm, toRealVec]

/-- The mixed form of two combinations as the double sum of the entries. -/
private theorem Zonotope.aux_quadMapMixed_expand {A B : ℕ} (Qm : Mat ℝ n n)
    (z₁ : Fin A → Vec ℝ n) (z₂ : Fin B → Vec ℝ n) (p : Fin A → ℝ)
    (q : Fin B → ℝ) : -- --- CONCL ---
    (∑ a, p a • z₁ a) ⬝ᵥ (Qm *ᵥ ∑ b, q b • z₂ b)
      = ∑ ba : Fin B × Fin A,
          (p ba.2 * q ba.1) * (z₁ ba.2 ⬝ᵥ (Qm *ᵥ z₂ ba.1)) := by -- --- PROOF ---
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, sum_dotProduct,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

/-- The image of a point of each operand, where both boxes are zero, lies in the core. -/
private theorem Zonotope.aux_quadMapMixed_core (Q : Fin m → Mat 𝕋 n n)
    (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) {x y : Vec ℝ n} (hx : x ∈ nominalSet Z₁)
    (hy : y ∈ nominalSet Z₂) : -- --- CONCL ---
    (fun i => x ⬝ᵥ (toRealMat (Q i) *ᵥ y))
      ∈ (Zonotope.step_quadMapMixedCore Q Z₁ Z₂).toSet := by -- --- PROOF ---
  obtain ⟨β₁, hβ₁, rfl⟩ := Zonotope.aux_quadMapMixed_point hx
  obtain ⟨β₂, hβ₂, rfl⟩ := Zonotope.aux_quadMapMixed_point hy
  -- the coefficients and the entries of `[c₁ G₁]` and `[c₂ G₂]`, the exact entry at a place
  set p : Fin (Z₁.h + 1) → ℝ := Fin.cons 1 β₁ with hp
  set q : Fin (Z₂.h + 1) → ℝ := Fin.cons 1 β₂ with hq
  set z₁ : Fin (Z₁.h + 1) → Vec ℝ n := fun a => toRealVec ((Fin.cons Z₁.c Z₁.G :
    Fin (Z₁.h + 1) → Vec 𝕋 n) a) with hz₁
  set z₂ : Fin (Z₂.h + 1) → Vec ℝ n := fun b => toRealVec ((Fin.cons Z₂.c Z₂.G :
    Fin (Z₂.h + 1) → Vec 𝕋 n) b) with hz₂
  set idx := Zonotope.step_quadMapMixedIdx Z₁.h Z₂.h with hidx
  set Bx : Fin m → Fin (Z₁.h + Z₂.h * (Z₁.h + 1) + 1) → ℝ := fun i t =>
    z₁ (idx t).2 ⬝ᵥ (toRealMat (Q i) *ᵥ z₂ (idx t).1) with hBx
  set w : Fin (Z₁.h + Z₂.h * (Z₁.h + 1) + 1) → ℝ := fun t => p (idx t).2 * q (idx t).1 with hw
  have hp1 : ∀ a, |p a| ≤ 1 := by
    intro a
    refine Fin.cases ?_ (fun j => ?_) a
    · simp [hp]
    · simpa [hp] using hβ₁ j
  -- the same for the right operand, and their products
  have hq1 : ∀ b, |q b| ≤ 1 := by
    intro b
    refine Fin.cases ?_ (fun j => ?_) b
    · simp [hq]
    · simpa [hq] using hβ₂ j
  have hw1 : ∀ t, |w t| ≤ 1 := fun t => by
    simp only [hw, abs_mul]
    exact mul_le_one₀ (hp1 _) (abs_nonneg _) (hq1 _)
  -- the place `0` is the entry `(0, 0)`
  have hidx0 : idx 0 = (0, 0) := by
    simp only [hidx, Zonotope.step_quadMapMixedIdx]
    apply finProdFinEquiv.injective
    simp only [Equiv.apply_symm_apply]
    ext; simp
  have hw0 : w 0 = 1 := by simp [hw, hidx0, hp, hq]
  -- the entries, bracketed
  have hent : ∀ i t, toReal (Zonotope.step_quadMapMixedEntryDown (Q i) Z₁ Z₂ t) ≤ Bx i t
      ∧ Bx i t ≤ toReal (Zonotope.step_quadMapMixedEntryUp (Q i) Z₁ Z₂ t) := fun i t =>
    Zonotope.quadEntry_bracket (Q i) _ _
  -- the form as the sum over the places
  have hsum : ∀ i, (∑ a, p a • z₁ a) ⬝ᵥ (toRealMat (Q i) *ᵥ ∑ b, q b • z₂ b)
      = Bx i 0 + ∑ l : Fin (Z₁.h + Z₂.h * (Z₁.h + 1)), w l.succ * Bx i l.succ := by
    intro i
    rw [Zonotope.aux_quadMapMixed_expand]
    have he : ∀ ba : Fin (Z₂.h + 1) × Fin (Z₁.h + 1),
        (p ba.2 * q ba.1) * (z₁ ba.2 ⬝ᵥ (toRealMat (Q i) *ᵥ z₂ ba.1))
          = (fun t => w t * Bx i t) (Fin.cast (by ring) (finProdFinEquiv ba)) := by
      intro ba
      have : idx (Fin.cast (by ring) (finProdFinEquiv ba)) = ba := by
        simp [hidx, Zonotope.step_quadMapMixedIdx]
      simp only [hw, hBx, this]
    rw [Finset.sum_congr rfl fun ba _ => he ba]
    have hc := Equiv.sum_comp (finProdFinEquiv.trans (finCongr (by ring :
      (Z₂.h + 1) * (Z₁.h + 1) = Z₁.h + Z₂.h * (Z₁.h + 1) + 1))) (fun t => w t * Bx i t)
    simp only [Equiv.trans_apply, finCongr_apply] at hc
    rw [hc, Fin.sum_univ_succ, hw0, one_mul]
  -- the box: the shortfall of the center and, per coefficient, of the generators
  set D := Zonotope.step_quadMapMixedCore Q Z₁ Z₂ with hD
  have hd₁ : (fun i => Bx i 0 - toReal (D.c i))
      ∈ (Interval.residual (fun i => Zonotope.step_quadMapMixedEntryDown (Q i) Z₁ Z₂ 0)
        (fun i => Zonotope.step_quadMapMixedEntryUp (Q i) Z₁ Z₂ 0)
        (fun i => Zonotope.step_quadMapMixedEntryDown (Q i) Z₁ Z₂ 0)).toSet :=
    Interval.sub_mem_residual fun i => hent i 0
  have hd₂ : (fun i => ∑ l : Fin D.h, (Bx i l.succ - toReal (D.G l i)) * w l.succ)
      ∈ (Zonotope.generatorError fun i l =>
        subUp (Zonotope.step_quadMapMixedEntryUp (Q i) Z₁ Z₂ l.succ)
          (Zonotope.step_quadMapMixedEntryDown (Q i) Z₁ Z₂ l.succ)).toSet := by
    refine Zonotope.mem_generatorError (fun i l => ?_) fun l => hw1 l.succ
    have hgap := sub_le_subUp (Zonotope.step_quadMapMixedEntryUp (Q i) Z₁ Z₂ l.succ)
      (Zonotope.step_quadMapMixedEntryDown (Q i) Z₁ Z₂ l.succ)
    show |Bx i l.succ - toReal (Zonotope.step_quadMapMixedEntryDown (Q i) Z₁ Z₂ l.succ)| ≤ _
    rw [abs_of_nonneg (sub_nonneg.2 (hent i l.succ).1)]
    linarith [(hent i l.succ).2]
  -- the point: the generators at the products of the coefficients, the box as above
  refine ⟨_, Zonotope.mem_nominalSet_iff.mpr ⟨fun l => w l.succ, fun l => hw1 l.succ,
    fun _ => rfl⟩, _, Interval.plus_outer _ _ ⟨_, hd₁, _, hd₂, rfl⟩, ?_⟩
  funext i
  show _ = (∑ a, p a • z₁ a) ⬝ᵥ (toRealMat (Q i) *ᵥ ∑ b, q b • z₂ b)
  rw [hsum i]
  have hs : ∑ l : Fin D.h, toReal (D.G l i) * w l.succ
      + ∑ l : Fin D.h, (Bx i l.succ - toReal (D.G l i)) * w l.succ
      = ∑ l : Fin (Z₁.h + Z₂.h * (Z₁.h + 1)), w l.succ * Bx i l.succ := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by rw [← add_mul, add_sub_cancel, mul_comm]; rfl
  show toReal (D.c i) + ∑ l : Fin D.h, toReal (D.G l i) * w l.succ
      + (Bx i 0 - toReal (D.c i)
        + ∑ l : Fin D.h, (Bx i l.succ - toReal (D.G l i)) * w l.succ) = _
  linarith [hs]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `x ∈ Z₁`, `y ∈ Z₂` give `(xᵀ Q⁽ⁱ⁾ y)ᵢ ∈ Z₁.quadMapMixed Q Z₂`. -/
theorem Zonotope.quadMapMixed_outer (Q : Fin m → Mat 𝕋 n n) (Z₁ Z₂ : Zonotope (Vec 𝕋 n))
    {x y : Vec ℝ n} (hx : x ∈ Z₁.toSet) (hy : y ∈ Z₂.toSet) :
    (fun i => x ⬝ᵥ (toRealMat (Q i) *ᵥ y)) ∈ (Z₁.quadMapMixed Q Z₂).toSet :=
  Zonotope.quadMapFilter_outer Q _ ((Zonotope.materialise_eq _).symm ▸
    Zonotope.aux_quadMapMixed_core Q _ _ (Zonotope.absorbRoundingIfAny_nominal Z₁ hx)
      (Zonotope.absorbRoundingIfAny_nominal Z₂ hy))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
