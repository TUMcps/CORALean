module

public import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
public import CORALean.ContSet.Interval.Float.Theorems.MatPlusOuter
public import CORALean.ContSet.PolyZonotope.Float.Operations.MatMap
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MatMulDownClose
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemMatGeneratorError
public import CORALean.ContSet.PolyZonotope.Float.Theorems.RealImageExtGens
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MatMapOuter
public import CORALean.ContSet.PolyZonotope.Real.Theorems.SumExtEqPoint

@[expose] public section

/-!
# `matMap` encloses the matrix product at shared factors, over a floating-point scalar

`Real.PolyZonotope.matMap_outer` read through the refinement, with the operands' error boxes:
a point of each operand at one factor vector, plus any point of its error box, multiplies into
the float result. The exact product of the nominal points is a point of the exact `matMap` of
the nominal sets, whose generators the stored ones miss by at most the rounding gaps
(`aux_matMap_refines`); the error boxes' share is `N₁e₂ + e₁(N₂ + e₂)`, bounded by
interval-matrix products against the operands' hulls (`aux_matMap_hull`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n k m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point of the nominal set lies in the box of all its generators, the center included. -/
theorem PolyZonotope.aux_matMap_hull {n k : ℕ} (pZ : PolyZonotope (Mat 𝕋 n k))
    {a : Fin pZ.p → ℝ} (ha : ∀ i, |a i| ≤ 1) {β : Fin pZ.q → ℝ}
    (hβ : ∀ j, |β j| ≤ 1) : -- --- STMT ---
    (PolyZonotope.nominal pZ).point a + ∑ j, β j • (PolyZonotope.nominal pZ).GI j
      ∈ (PolyZonotope.matGeneratorError
          (Fin.append (PolyZonotope.extGens pZ) pZ.GI)).construct := by -- --- PROOF ---
  -- the coefficients: the extended monomials, then `β`
  have ht : ∀ s, |Fin.append (Real.PolyZonotope.extM (PolyZonotope.nominal pZ) a) β s| ≤ 1 := by
    intro s
    refine Fin.addCases (fun l => ?_) (fun j => ?_) s
    · rw [Fin.append_left]
      exact Real.PolyZonotope.abs_monomial_le_one _ ha l
    · rw [Fin.append_right]
      exact hβ j
  have h := PolyZonotope.mem_matGeneratorError
    (G := Fin.append (PolyZonotope.extGens pZ) pZ.GI)
    (Δ := fun s => toRealMat (Fin.append (PolyZonotope.extGens pZ) pZ.GI s))
    (fun _ _ _ => le_refl _) ht
  -- the point is the extended sum, then the independent one
  convert h using 1
  rw [Fin.sum_univ_add, Real.PolyZonotope.point, ← Real.PolyZonotope.sum_ext_eq_point]
  simp only [Fin.append_left, Fin.append_right]
  congr 1
  exact Finset.sum_congr rfl fun l _ => by
    rw [← PolyZonotope.realImage_extGens]
    rfl

/-- The exact `matMap` of the nominal sets: each point is a point of the float result's nominal
set plus a share of the rounding box. -/
theorem PolyZonotope.aux_matMap_refines (pZ₁ : PolyZonotope (Mat 𝕋 n k))
    (pZ₂ : PolyZonotope (Mat 𝕋 k m)) (hp : pZ₁.p = pZ₂.p) {X : Mat ℝ n m}
    (hX : X ∈ (Real.PolyZonotope.matMap (PolyZonotope.nominal pZ₁)
      (PolyZonotope.nominal pZ₂) hp).construct) : -- --- STMT ---
    ∃ P ∈ (PolyZonotope.nominal (PolyZonotope.matMap pZ₁ pZ₂ hp)).construct,
      X - P ∈ (PolyZonotope.matGeneratorError (Fin.append (PolyZonotope.pairG matMulDiff pZ₁ pZ₂)
        (PolyZonotope.pairGI matMulDiff pZ₁ pZ₂))).construct := by -- --- PROOF ---
  obtain ⟨a, b, ha, hb, hX⟩ := hX
  -- a stored product and its exact counterpart differ by at most the gap
  have close : ∀ (A : Mat 𝕋 n k) (B : Mat 𝕋 k m) (D : Mat ℝ n m),
      D = toRealMat A * toRealMat B →
        ∀ i j, |(D - toRealMat (matMulDown A B)) i j| ≤ |toReal (matMulDiff A B i j)| := by
    rintro A B D rfl i j
    exact (PolyZonotope.matMulDown_close A B i j).trans (le_abs_self _)
  -- the exact pairs, read as products of the stored generators read back
  have hG : ∀ l, Real.PolyZonotope.bilinG matMulBilin (PolyZonotope.nominal pZ₁)
      (PolyZonotope.nominal pZ₂) l
        = toRealMat (PolyZonotope.extGens pZ₁ (finProdFinEquiv.symm l).1)
          * toRealMat (PolyZonotope.extGens pZ₂ (finProdFinEquiv.symm l).2) := fun l => by
    show matMulBilin (Real.PolyZonotope.extG _ _) (Real.PolyZonotope.extG _ _) = _
    rw [← PolyZonotope.realImage_extGens, ← PolyZonotope.realImage_extGens]
    rfl
  have hGI : ∀ t, ∃ (A : Mat 𝕋 n k) (B : Mat 𝕋 k m),
      Real.PolyZonotope.bilinGI matMulBilin (PolyZonotope.nominal pZ₁)
        (PolyZonotope.nominal pZ₂) t = toRealMat A * toRealMat B
      ∧ PolyZonotope.pairGI matMulDown pZ₁ pZ₂ t = matMulDown A B
      ∧ PolyZonotope.pairGI matMulDiff pZ₁ pZ₂ t = matMulDiff A B := by
    -- block by block, as `bilinGI` orders them
    intro t
    refine Fin.addCases (fun t => ?_) (fun t => ?_) t
    · refine Fin.addCases (fun t => ?_) (fun t => ?_) t
      · refine ⟨pZ₁.GI (finProdFinEquiv.symm t).1,
          PolyZonotope.extGens pZ₂ (finProdFinEquiv.symm t).2, ?_, ?_, ?_⟩
        · simp only [Real.PolyZonotope.bilinGI, Fin.append_left]
          rw [← PolyZonotope.realImage_extGens]
          rfl
        all_goals simp only [PolyZonotope.pairGI, Fin.append_left]
      -- the middle block reads no extended generator
      · refine ⟨pZ₁.GI (finProdFinEquiv.symm t).1, pZ₂.GI (finProdFinEquiv.symm t).2, ?_, ?_, ?_⟩
        · simp only [Real.PolyZonotope.bilinGI, Fin.append_left, Fin.append_right]
          rfl
        all_goals simp only [PolyZonotope.pairGI, Fin.append_left, Fin.append_right]
    · refine ⟨PolyZonotope.extGens pZ₁ (finProdFinEquiv.symm t).1,
        pZ₂.GI (finProdFinEquiv.symm t).2, ?_, ?_, ?_⟩
      · simp only [Real.PolyZonotope.bilinGI, Fin.append_right]
        rw [← PolyZonotope.realImage_extGens]
        rfl
      all_goals simp only [PolyZonotope.pairGI, Fin.append_right]
  -- the float result's nominal point at the same factors and coefficients
  refine ⟨_, ⟨a, b, ha, hb, rfl⟩, ?_⟩
  have h := PolyZonotope.mem_matGeneratorError
    (G := Fin.append (PolyZonotope.pairG matMulDiff pZ₁ pZ₂)
      (PolyZonotope.pairGI matMulDiff pZ₁ pZ₂))
    (Δ := Fin.append
      (fun l => Real.PolyZonotope.bilinG matMulBilin (PolyZonotope.nominal pZ₁)
        (PolyZonotope.nominal pZ₂) l - toRealMat (PolyZonotope.pairG matMulDown pZ₁ pZ₂ l))
      (fun t => Real.PolyZonotope.bilinGI matMulBilin (PolyZonotope.nominal pZ₁)
        (PolyZonotope.nominal pZ₂) t - toRealMat (PolyZonotope.pairGI matMulDown pZ₁ pZ₂ t)))
    (t := Fin.append (Real.PolyZonotope.monomial (PolyZonotope.bilinE pZ₁ pZ₂ hp) a) b)
    -- each shortfall within its gap
    (fun s => by
      refine Fin.addCases (fun l => ?_) (fun t => ?_) s
      · simp only [Fin.append_left]
        exact close _ _ _ (hG l)
      · obtain ⟨A, B, hD, hdown, hdiff⟩ := hGI t
        simp only [Fin.append_right, hdown, hdiff]
        exact close A B _ hD)
    -- the monomials, then the coefficients, in [-1, 1]
    (fun s => by
      refine Fin.addCases (fun l => ?_) (fun t => ?_) s
      · rw [Fin.append_left]
        exact Real.PolyZonotope.abs_monomial_le_one _ ha l
      · rw [Fin.append_right]
        exact hb t)
  -- the difference is the gaps at the monomials, then at the independent coefficients
  convert h using 1
  rw [hX, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  -- both sides at the same index types, the exact center `0`, the stored one `zero`
  change (0 + (∑ l : Fin ((pZ₁.h + 1) * (pZ₂.h + 1)),
        Real.PolyZonotope.monomial (PolyZonotope.bilinE pZ₁ pZ₂ hp) a l
          • Real.PolyZonotope.bilinG matMulBilin (PolyZonotope.nominal pZ₁)
            (PolyZonotope.nominal pZ₂) l)
      + ∑ j : Fin (pZ₁.q * (pZ₂.h + 1) + pZ₁.q * pZ₂.q + (pZ₁.h + 1) * pZ₂.q),
        b j • Real.PolyZonotope.bilinGI matMulBilin (PolyZonotope.nominal pZ₁)
          (PolyZonotope.nominal pZ₂) j)
    -- the float result's nominal point
    - (toRealMat (fun _ _ => (zero : 𝕋) : Mat 𝕋 n m)
      + (∑ l : Fin ((pZ₁.h + 1) * (pZ₂.h + 1)),
        Real.PolyZonotope.monomial (PolyZonotope.bilinE pZ₁ pZ₂ hp) a l
          • toRealMat (PolyZonotope.pairG matMulDown pZ₁ pZ₂ l))
      + ∑ j : Fin (pZ₁.q * (pZ₂.h + 1) + pZ₁.q * pZ₂.q + (pZ₁.h + 1) * pZ₂.q),
        b j • toRealMat (PolyZonotope.pairGI matMulDown pZ₁ pZ₂ j))
    -- the shortfalls at their coefficients
    = (∑ l : Fin ((pZ₁.h + 1) * (pZ₂.h + 1)),
        Real.PolyZonotope.monomial (PolyZonotope.bilinE pZ₁ pZ₂ hp) a l
          • (Real.PolyZonotope.bilinG matMulBilin (PolyZonotope.nominal pZ₁)
            (PolyZonotope.nominal pZ₂) l - toRealMat (PolyZonotope.pairG matMulDown pZ₁ pZ₂ l)))
      + ∑ j : Fin (pZ₁.q * (pZ₂.h + 1) + pZ₁.q * pZ₂.q + (pZ₁.h + 1) * pZ₂.q),
        b j • (Real.PolyZonotope.bilinGI matMulBilin (PolyZonotope.nominal pZ₁)
          (PolyZonotope.nominal pZ₂) j - toRealMat (PolyZonotope.pairGI matMulDown pZ₁ pZ₂ j))
  have h0 : toRealMat (fun _ _ => (zero : 𝕋) : Mat 𝕋 n m) = 0 := by
    funext i j
    exact toReal_zero
  simp only [smul_sub, Finset.sum_sub_distrib, h0]
  abel


-- =======================================  MAIN THEOREM  ======================================= --

/-- At one factor vector, a point of each operand plus a point of its error box: their product
is a point of the float `matMap`. -/
theorem PolyZonotope.matMap_outer (pZ₁ : PolyZonotope (Mat 𝕋 n k))
    (pZ₂ : PolyZonotope (Mat 𝕋 k m)) (hp : pZ₁.p = pZ₂.p) (a : Fin pZ₁.p → ℝ)
    (ha : ∀ i, |a i| ≤ 1) (β₁ : Fin pZ₁.q → ℝ) (β₂ : Fin pZ₂.q → ℝ) (hβ₁ : ∀ j, |β₁ j| ≤ 1)
    (hβ₂ : ∀ j, |β₂ j| ≤ 1) {e₁ : Mat ℝ n k} (he₁ : e₁ ∈ pZ₁.I_error.construct) {e₂ : Mat ℝ k m}
    (he₂ : e₂ ∈ pZ₂.I_error.construct) : -- --- STMT ---
    ((PolyZonotope.nominal pZ₁).point a + ∑ j, β₁ j • (PolyZonotope.nominal pZ₁).GI j + e₁) *
        ((PolyZonotope.nominal pZ₂).point (fun i => a (Fin.cast hp.symm i))
          + ∑ j, β₂ j • (PolyZonotope.nominal pZ₂).GI j + e₂)
      ∈ InflatedContSet.construct (PolyZonotope.matMap pZ₁ pZ₂ hp) := by -- --- PROOF ---
  -- the nominal product: a nominal point of the result plus a share of the rounding box
  obtain ⟨P, hP, hg⟩ := PolyZonotope.aux_matMap_refines pZ₁ pZ₂ hp
    (Real.PolyZonotope.matMap_outer (PolyZonotope.nominal pZ₁) (PolyZonotope.nominal pZ₂) hp
      a ha β₁ β₂ hβ₁ hβ₂)
  -- the error boxes' share, against the operands' hulls
  have h₁ := PolyZonotope.aux_matMap_hull pZ₁ ha hβ₁
  have h₂ := PolyZonotope.aux_matMap_hull pZ₂ (a := fun i => a (Fin.cast hp.symm i))
    (fun i => ha _) hβ₂
  have hE := Interval.matPlus_outer _ _ hg (Interval.matPlus_outer _ _
    (Interval.matMul_outer _ _ h₁ he₂)
    (Interval.matMul_outer _ _ he₁ (Interval.matPlus_outer _ _ h₂ he₂)))
  refine Set.mem_add.mpr ⟨P, hP, _, hE, ?_⟩
  -- `(N₁ + e₁)(N₂ + e₂) = N₁N₂ + N₁e₂ + e₁(N₂ + e₂)`
  have key : ∀ (X₁ E₁ : Mat ℝ n k) (X₂ E₂ : Mat ℝ k m) (Q : Mat ℝ n m),
      Q + ((X₁ * X₂ - Q) + (X₁ * E₂ + E₁ * (X₂ + E₂))) = (X₁ + E₁) * (X₂ + E₂) := by
    intro X₁ E₁ X₂ E₂ Q
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    abel
  exact key _ _ _ _ _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
