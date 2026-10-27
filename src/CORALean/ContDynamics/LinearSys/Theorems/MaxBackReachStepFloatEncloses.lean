module

public import CORALean.ContDynamics.LinearSys.Definitions.MaxBackReachStateFloatEncloses
public import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachStep
public import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachStepFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMemAdaptiveIntegralFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpIntervalFloat
public import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionSubsetInputSolutionFloat
public import CORALean.ContDynamics.LinearSys.Theorems.MaxBackReachCZFloatInner
public import CORALean.ContDynamics.LinearSys.Theorems.MinkowskiDiffSubsetMaxBackReachCZ
public import CORALean.ContDynamics.LinearSys.Theorems.ReachOrderFloatSpec
public import CORALean.ContSet.ConZonotope.Float.Theorems.ConstructEqNominal
public import CORALean.ContSet.ConZonotope.Float.Operations.LinCombSameCenter
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.HPolytope.Float.Theorems.MemStackRowsNominalIff
public import CORALean.ContSet.HPolytope.Float.Theorems.MulVecSingle
public import CORALean.ContSet.HPolytope.Float.Theorems.MemUnitBoxIff
public import CORALean.ContSet.HPolytope.Float.Theorems.MulVecAppendLeft
public import CORALean.Global.Float.ToRealMatMulVec
public import CORALean.ContSet.HPolytope.Float.Operations.HalfScaledLeft
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Theorems.MemStackRowsConstructIff
public import CORALean.ContSet.HPolytope.Float.Theorems.MulVecAppendLast
public import CORALean.ContSet.HPolytope.Float.Theorems.MulVecPadLeft
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
public import CORALean.ContSet.HPolytope.Float.Operations.HalfScaledRight
public import CORALean.ContSet.HPolytope.Float.Theorems.MulVecPadRight
public import CORALean.ContSet.ConZonotope.Float.Theorems.MtimesNominalErr
public import CORALean.ContSet.ConZonotope.Float.Theorems.ZeroFeasibleNonempty
public import CORALean.ContSet.ConZonotope.Real.Theorems.LinCombOuter
public import CORALean.ContSet.ConZonotope.Real.Theorems.Basic
public import CORALean.ContSet.ConZonotope.Real.Theorems.PlusExact
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeConZonotopeExact
public import CORALean.ContSet.Interval.Float.Theorems.AbsLeMagnitude
public import CORALean.ContSet.Interval.Float.Theorems.AbsMulVecLeMagnitudeMat
public import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesIntervalMatSubsetAddBox
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusSubsetAddBox
public import CORALean.ContSet.Zonotope.Float.Theorems.ZeroMemMtimesIntervalMatError
public import CORALean.ContSet.Zonotope.Float.Theorems.ZeroMemPlusError
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import CORALean.ContSet.Conversion.Float.Operations.HPolytope_to_ConZonotope
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_ConZonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Conversion.Float.Operations.HPolytope_to_ConZonotopeInner
public import CORALean.ContSet.Conversion.Float.Theorems.Basic
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ConZonotopeZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeConZonotopeExact
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# One iteration of `Alg. 3` in floats stays inside the exact one

`maxBackReachStepFloat` against `maxBackReachStep`, [1, Alg. 3] lines 7-12: the new state stands for
the exact one. The hull part is the stored hull mapped within the rounding of its lower matrix; its
distance to the exact image, the second summand's, and `Z̲_U`'s excess are carried back by
`e^{A t_{k+1}}` and held inside the margin the disturbance set was widened by, so the moved
point is in the exact hull (`Lemma 1`'s segments, `linComb_outer`).

## Inputs
* `sys` – linear system
* `Bx` – conversion box
* `P₁` – first eroded float polytope
* `P₂` – second eroded float polytope
* `U` – input float zonotope
* `W₀` – initial disturbance float zonotope
* `Zw` – center trajectory contribution over a bracket
* `Δt` – float step length
* `η` – Taylor order
* `s` – float loop state
* `ρ` – support oracle for bounded exact polytopes
* `P₁r` – first exact polytope
* `P₂r` – second exact polytope
* `Ur` – exact input zonotope
* `W₀r` – exact initial disturbance zonotope
* `Zwr` – exact center trajectory contribution
* `sr` – exact loop state

## Hypotheses
* `hs` – float state stands for the exact state
* `hΔt` – step length positive
* `hU0` – input error box contains zero
* `hU` – exact input zonotope inside the float one
* `hWE` – disturbance error box is zero
* `hW₀r` – exact disturbance zonotope inside the float one
* `hZw` – float center contribution holds the exact one
* `hP₁` – first float polytope inside the exact one
* `hP₂` – second float polytope inside the exact one
* `hP₁0` – first polytope error box contains zero
* `hP₂0` – second polytope error box contains zero
* `hker₁` – first float polytope has no equality rows
* `hker₂` – second float polytope has no equality rows
* `hkerr₁` – first exact polytope has no equality rows
* `hkerr₂` – second exact polytope has no equality rows
* `hP₁b` – the inequality rows of the first exact polytope bound it
* `hP₂b` – the inequality rows of the second exact polytope bound it

## Conclusion
* the float iteration's state stands for the exact iteration's
## References

* [1] [M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
      Linear Systems Using Set Propagation". IEEE Transactions on Automatic Control,
      2026.](../../../../../references/2026/wetzlinger-tac-backward-reachability.md)
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   26-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic ContSet InflatedContSet Matrix NormedSpace
open scoped Pointwise
open scoped CORALean.Real

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

namespace Float
section
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n₁ n₂ : ℕ}

/-- What a point of `halfScaledRight` says about its second block. -/
private theorem HPolytope.aux_mem_halfScaledRight {P : HPolytope 𝕋 (Vec 𝕋 n₂)} {z : Vec ℝ n₁}
    {y : Vec ℝ n₂} {t : ℝ}
    (h : Fin.append (Fin.append z y) (fun _ : Fin 1 => t)
      ∈ (HPolytope.halfScaledRight n₁ P).construct) : -- --- CONCL ---
    (∀ i, (toRealMat P.A *ᵥ y) i ≤ (1 - t) / 2 * toReal (P.b i) + |toReal (P.b_error i)|) ∧
      ∀ i, |(toRealMat P.Ae *ᵥ y) i - (1 - t) / 2 * toReal (P.be i)|
        ≤ |toReal (P.be_error i)| := by -- --- PROOF ---
  have hneg : toRealMat (fun i => -P.Ae i) = -toRealMat P.Ae := toRealMat_neg P.Ae
  -- the three row groups of the weighted polytope, each with its slack
  rw [HPolytope.halfScaledRight, HPolytope.mem_stackRows_iff,
    HPolytope.mem_stackRows_nominal_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  have h1 := (HPolytope.mem_nominal_iff.mp h1).1
  have h2 := (HPolytope.mem_nominal_iff.mp h2).1
  have h3 := (HPolytope.mem_nominal_iff.mp h3).1
  -- each read on the block it came from
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have : (toRealMat (fun i => Fin.append (Fin.append (fun _ : Fin n₁ => FloatOps.zero) (P.A i))
        fun _ : Fin 1 => half (P.b i)) *ᵥ _) i
          ≤ toReal (half (P.b i)) + |toReal (P.b_error i)| := h1 i
    rw [HPolytope.mulVec_append_last, HPolytope.mulVec_padRight, blockRight_append] at this
    simp only [toReal_half] at this
    linarith
  · have h2' : (toRealMat (fun i =>
        Fin.append (Fin.append (fun _ : Fin n₁ => FloatOps.zero) (P.Ae i))
          fun _ : Fin 1 => half (P.be i)) *ᵥ _) i
          ≤ toReal (half (P.be i)) + |toReal (P.be_error i)| := h2 i
    -- the equality's lower edge, read through its negated row
    have h3' : (toRealMat (fun i =>
        Fin.append (Fin.append (fun _ : Fin n₁ => FloatOps.zero) (-(P.Ae i)))
          fun _ : Fin 1 => half (neg (P.be i))) *ᵥ _) i
          ≤ toReal (half (neg (P.be i))) + |toReal (P.be_error i)| := h3 i
    rw [HPolytope.mulVec_append_last, HPolytope.mulVec_padRight, blockRight_append] at h2'
    rw [HPolytope.mulVec_append_last, HPolytope.mulVec_padRight, blockRight_append, hneg,
      Matrix.neg_mulVec] at h3'
    simp only [Pi.neg_apply, toReal_neg, toReal_half] at h2' h3'
    rw [abs_le]
    constructor <;> linarith


/-- What a point of `halfScaledLeft` says about its first block. -/
private theorem HPolytope.aux_mem_halfScaledLeft {P : HPolytope 𝕋 (Vec 𝕋 n₁)} {y : Vec ℝ n₁}
    {z : Vec ℝ n₂} {t : ℝ}
    (h : Fin.append (Fin.append y z) (fun _ : Fin 1 => t)
      ∈ (P.halfScaledLeft n₂).construct) : -- --- CONCL ---
    (∀ i, (toRealMat P.A *ᵥ y) i ≤ (t + 1) / 2 * toReal (P.b i) + |toReal (P.b_error i)|) ∧
      ∀ i, |(toRealMat P.Ae *ᵥ y) i - (t + 1) / 2 * toReal (P.be i)|
        ≤ |toReal (P.be_error i)| := by -- --- PROOF ---
  have hneg : toRealMat (fun i => -P.Ae i) = -toRealMat P.Ae := toRealMat_neg P.Ae
  -- the three row groups of the weighted polytope, each with its slack
  rw [HPolytope.halfScaledLeft, HPolytope.mem_stackRows_iff,
    HPolytope.mem_stackRows_nominal_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  have h1 := (HPolytope.mem_nominal_iff.mp h1).1
  have h2 := (HPolytope.mem_nominal_iff.mp h2).1
  have h3 := (HPolytope.mem_nominal_iff.mp h3).1
  -- each read on the block it came from
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have : (toRealMat (fun i => Fin.append (Fin.append (P.A i) fun _ : Fin n₂ => FloatOps.zero)
        fun _ : Fin 1 => neg (half (P.b i))) *ᵥ _) i
          ≤ toReal (half (P.b i)) + |toReal (P.b_error i)| := h1 i
    rw [HPolytope.mulVec_append_last, HPolytope.mulVec_padLeft, blockLeft_append] at this
    simp only [toReal_neg, toReal_half] at this
    linarith
  · have h2' : (toRealMat (fun i =>
        Fin.append (Fin.append (P.Ae i) fun _ : Fin n₂ => FloatOps.zero)
          fun _ : Fin 1 => neg (half (P.be i))) *ᵥ _) i
          ≤ toReal (half (P.be i)) + |toReal (P.be_error i)| := h2 i
    -- the equality's lower edge, read through its negated row
    have h3' : (toRealMat (fun i =>
        Fin.append (Fin.append (-(P.Ae i)) fun _ : Fin n₂ => FloatOps.zero)
          fun _ : Fin 1 => neg (half (neg (P.be i)))) *ᵥ _) i
          ≤ toReal (half (neg (P.be i))) + |toReal (P.be_error i)| := h3 i
    rw [HPolytope.mulVec_append_last, HPolytope.mulVec_padLeft, blockLeft_append] at h2'
    rw [HPolytope.mulVec_append_last, HPolytope.mulVec_padLeft, blockLeft_append, hneg,
      Matrix.neg_mulVec] at h3'
    simp only [Pi.neg_apply, toReal_neg, toReal_half] at h2' h3'
    rw [abs_le]
    constructor <;> linarith

end
end Float


namespace Float
section
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- A block meeting a polytope's rows and the unit box's at weight `lam` is `lam` times a
coefficient vector of the polytope inside the unit box, the polytope being nonempty there. -/
private theorem ConZonotope.aux_blockCoeff {k : ℕ} (P : HPolytope 𝕋 (Vec 𝕋 k))
    (hne : ∃ β : Vec ℝ k, (∀ j, |β j| ≤ 1) ∧ β ∈ P.nominal.construct) {γ : Vec ℝ k} {lam : ℝ}
    {Q : HPolytope 𝕋 (Vec 𝕋 k)} (hQ : Q = P.stackRows (HPolytope.unitBox 𝕋 k))
    (hl0 : 0 ≤ lam)
    (hA : ∀ i, (toRealMat Q.A *ᵥ γ) i ≤ lam * toReal (Q.b i))
    (hE : ∀ i, (toRealMat Q.Ae *ᵥ γ) i = lam * toReal (Q.be i)) : -- --- CONCL ---
    ∃ β : Vec ℝ k, (∀ j, |β j| ≤ 1) ∧ β ∈ P.nominal.construct ∧ lam • β = γ := by -- --- PROOF ---
  obtain rfl | hpos := hl0.eq_or_lt
  · -- zero weight: the unit-box rows pin the block to the origin
    obtain ⟨β, hβ, hP⟩ := hne
    refine ⟨β, hβ, hP, funext fun j => ?_⟩
    -- the two unit-box rows of coordinate `j`, at weight zero, bound it by `0` both ways
    subst hQ
    have hup := hA (Fin.natAdd P.m (Fin.castAdd k j))
    have hlo := hA (Fin.natAdd P.m (Fin.natAdd k j))
    simp only [HPolytope.stackRows, toRealMat_append_mulVec_natAdd, Fin.append_right,
      HPolytope.unitBox, HPolytope.mulVec_append_left, HPolytope.mulVec_single,
      toReal_one, toReal_neg, one_mul, neg_mul, zero_mul] at hup hlo
    simp only [Pi.smul_apply, zero_smul]
    linarith
  · -- positive weight: divide through, the rows then holding as stated
    refine ⟨lam⁻¹ • γ, ?_⟩
    -- the divided vector meets the rows at weight one, and the unit box
    have hmem : lam⁻¹ • γ ∈ Q.nominal.construct := by
      refine HPolytope.mem_nominal_iff.mpr ⟨fun i => ?_, fun i => ?_⟩
      · -- the inequality rows scale by `lam⁻¹`
        rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
        refine le_add_of_le_of_nonneg ?_ (abs_nonneg _)
        calc lam⁻¹ * (toRealMat Q.A *ᵥ γ) i
            ≤ lam⁻¹ * (lam * toReal (Q.b i)) :=
              mul_le_mul_of_nonneg_left (hA i) (inv_nonneg.mpr hl0)
          _ = _ := by field_simp
      · rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, hE i]
        refine le_trans (le_of_eq ?_) (abs_nonneg _)
        rw [abs_eq_zero, sub_eq_zero]
        field_simp
    rw [hQ] at hmem
    obtain ⟨hP, hbox⟩ := HPolytope.mem_stackRows_nominal_iff.mp hmem
    exact ⟨HPolytope.mem_unitBox_iff.mp ((HPolytope.mem_nominal_of_origin rfl).mpr hbox), hP,
      by rw [smul_smul, mul_inv_cancel₀ hpos.ne',
      one_smul]⟩


/-- `linCombSameCenter` is no larger than the hull. -/
private theorem ConZonotope.aux_linCombSameCenter_subset (cZ₁ cZ₂ : ConZonotope 𝕋 (Vec 𝕋 n))
    (hc : cZ₂.c = cZ₁.c) (hs₁ : cZ₁.P.IsSlackFree) (hs₂ : cZ₂.P.IsSlackFree)
    (hne₁ : (nominalSet cZ₁).Nonempty) (hne₂ : (nominalSet cZ₂).Nonempty) : -- --- CONCL ---
    nominalSet (cZ₁.linCombSameCenter cZ₂) ⊆
      Set.linComb (nominalSet cZ₁) (nominalSet cZ₂) := by -- --- PROOF ---
  intro x hx
  -- the nominal point, at its coefficients
  obtain ⟨β, hβ, hP, hval⟩ := ConZonotope.mem_nominalSet_iff.mp hx
  -- the coefficient vector in its three blocks
  set γ₁ : Vec ℝ cZ₁.h := fun j => β (Fin.castAdd 1 (Fin.castAdd cZ₂.h j)) with hγ₁
  set γ₂ : Vec ℝ cZ₂.h := fun j => β (Fin.castAdd 1 (Fin.natAdd cZ₁.h j)) with hγ₂
  set ν : ℝ := β (Fin.natAdd (cZ₁.h + cZ₂.h) 0) with hν
  have hβeq : β = Fin.append (Fin.append γ₁ γ₂) fun _ : Fin 1 => ν := by
    funext j
    refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j
    · refine Fin.addCases (fun j'' => ?_) (fun j'' => ?_) j'
      · simp [hγ₁]
      · simp [hγ₂]
    · have : j' = 0 := Subsingleton.elim _ _
      subst this
      simp [hν]
  -- the three row groups of the hull's coefficient polytope
  have hP' : β ∈ (((cZ₁.P.stackRows (HPolytope.unitBox 𝕋 cZ₁.h)).halfScaledLeft
      cZ₂.h).stackRows (HPolytope.halfScaledRight cZ₁.h
        (cZ₂.P.stackRows (HPolytope.unitBox 𝕋 cZ₂.h)))).nominal.construct := hP
  obtain ⟨hL, hR⟩ := HPolytope.mem_stackRows_nominal_iff.mp hP'
  rw [hβeq] at hL hR
  replace hL := (HPolytope.mem_nominal_of_origin rfl).mpr hL
  replace hR := (HPolytope.mem_nominal_of_origin rfl).mpr hR
  obtain ⟨hA₁, hE₁⟩ := HPolytope.aux_mem_halfScaledLeft hL
  obtain ⟨hA₂, hE₂⟩ := HPolytope.aux_mem_halfScaledRight hR
  -- a slack-free block stays slack-free with its unit box stacked on, so the rows read exactly
  have hstack : ∀ {k : ℕ} (Q : HPolytope 𝕋 (Vec 𝕋 k)), Q.IsSlackFree →
      (Q.stackRows (HPolytope.unitBox 𝕋 k)).IsSlackFree := fun Q hs =>
    ⟨fun i => Fin.addCases (fun i => by simpa [HPolytope.stackRows] using hs.1 i)
      (fun i => by simp [HPolytope.stackRows, HPolytope.unitBox, toReal_zero]) i,
     fun i => Fin.addCases (fun i => by simpa [HPolytope.stackRows] using hs.2 i)
      (fun i => i.elim0) i⟩
  obtain ⟨hb₁, he₁⟩ := hstack cZ₁.P hs₁
  obtain ⟨hb₂, he₂⟩ := hstack cZ₂.P hs₂
  simp only [hb₁, hb₂, he₁, he₂, abs_zero, add_zero, abs_nonpos_iff, sub_eq_zero]
    at hA₁ hE₁ hA₂ hE₂
  -- the weight, and the second block's
  have hν1 : |ν| ≤ 1 := by
    have := hβ (Fin.natAdd (cZ₁.h + cZ₂.h) 0)
    exact this
  obtain ⟨hνl, hνu⟩ := abs_le.mp hν1
  set lam : ℝ := (ν + 1) / 2 with hlam
  have hl0 : 0 ≤ lam := by rw [hlam]; linarith
  have hl1 : lam ≤ 1 := by rw [hlam]; linarith
  have hw : (1 - ν) / 2 = 1 - lam := by rw [hlam]; ring
  rw [hw] at hA₂ hE₂
  -- each block is its weight times a coefficient vector of its own set
  obtain ⟨β₁, hβ₁, hP₁, hγ₁eq⟩ := ConZonotope.aux_blockCoeff cZ₁.P
    (by obtain ⟨y, hy⟩ := hne₁
        obtain ⟨b, hb, hbP, -⟩ := ConZonotope.mem_nominalSet_iff.mp hy
        exact ⟨b, hb, hbP⟩) rfl hl0 hA₁ hE₁
  obtain ⟨β₂, hβ₂, hP₂, hγ₂eq⟩ := ConZonotope.aux_blockCoeff cZ₂.P
    (by obtain ⟨y, hy⟩ := hne₂
        obtain ⟨b, hb, hbP, -⟩ := ConZonotope.mem_nominalSet_iff.mp hy
        exact ⟨b, hb, hbP⟩) rfl (by linarith) hA₂ hE₂
  refine ⟨fun i => toReal (cZ₁.c i) + ∑ j, toReal (cZ₁.G j i) * β₁ j,
    ConZonotope.mem_nominalSet_iff.mpr ⟨β₁, hβ₁, hP₁, fun _ => rfl⟩,
    fun i => toReal (cZ₂.c i) + ∑ j, toReal (cZ₂.G j i) * β₂ j,
    ConZonotope.mem_nominalSet_iff.mpr ⟨β₂, hβ₂, hP₂, fun _ => rfl⟩, lam, ⟨hl0, hl1⟩, ?_⟩
  funext i
  have hxi := hval i
  -- the value of the stored hull at the coefficients, in three blocks
  change x i = toReal (cZ₁.c i) + ∑ j : Fin (cZ₁.h + cZ₂.h + 1),
    toReal (Fin.append (Fin.append cZ₁.G cZ₂.G) (fun _ : Fin 1 => fun _ => (zero : 𝕋)) j i)
      * β j at hxi
  rw [hβeq, Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_one] at hxi
  simp only [Fin.append_left, Fin.append_right, toReal_zero, zero_mul, add_zero] at hxi
  -- the blocks, as their weights times the coefficients of their own sets
  have e₁ : ∑ j, toReal (cZ₁.G j i) * γ₁ j = lam * ∑ j, toReal (cZ₁.G j i) * β₁ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hγ₁eq]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  -- likewise the second block, with the weight `1 - lam`
  have e₂ : ∑ j, toReal (cZ₂.G j i) * γ₂ j = (1 - lam) * ∑ j, toReal (cZ₂.G j i) * β₂ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hγ₂eq]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hci : toReal (cZ₂.c i) = toReal (cZ₁.c i) := by rw [hc]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hxi, e₁, e₂, hci]
  ring

end
end Float


namespace Float
section
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- A point of the tightened conversion reaches no further than `|c| + Σ|G|` of the zonotope it is
taken at, whatever the polytope. -/
private theorem HPolytope.aux_abs_nominal_conZonotopeInnerOf_le (P : HPolytope 𝕋 (Vec 𝕋 n))
    (Z : Zonotope (Vec 𝕋 n))
    {y : Vec ℝ n} (hy : y ∈ nominalSet (P.conZonotopeInnerOf Z)) (k : Fin n) : -- --- CONCL ---
    |y k| ≤
      toReal (addUp (absolute (Z.c k)) (radius (fun i j => Z.G j i) k)) := by -- --- PROOF ---
  obtain ⟨β, hβ, -, hval⟩ := ConZonotope.mem_nominalSet_iff.mp hy
  have hgen := abs_sum_le_radius (d := fun i j => Z.G j i) (Δ := fun i j => toReal (Z.G j i))
    (fun _ _ => le_refl _) hβ k
  have hup := add_le_addUp (absolute (Z.c k)) (radius (fun i j => Z.G j i) k)
  rw [toReal_absolute] at hup
  have hk : y k = toReal (Z.c k) + ∑ j, toReal (Z.G j k) * β j := hval k
  rw [hk]
  exact le_trans (abs_add_le _ _) (by linarith)

end
end Float


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.maxBackReachStepFloat_encloses (sys : LinearSys 𝕋 n) (Bx : Interval (Vec 𝕋 n))
    (P₁ P₂ : HPolytope 𝕋 (Vec 𝕋 n)) {U W₀ : Zonotope (Vec 𝕋 n)} {Zw : 𝕋 → 𝕋 → Zonotope (Vec 𝕋 n)}
    {Δt : 𝕋} {η : ℕ} {s : LinearSys.MaxBackReachStateFloat 𝕋 n}
    (ρ : ∀ (P : CORALean.Real.HPolytope (Vec ℝ n)) (_ : Bornology.IsBounded P.construct)
      (c : Vec ℝ n →ₗ[ℝ] ℝ), SupportBound P.construct c)
    (P₁r P₂r : CORALean.Real.HPolytope (Vec ℝ n))
    (Ur W₀r : CORALean.Real.Zonotope (Vec ℝ n)) (Zwr : ℝ → CORALean.Real.Zonotope (Vec ℝ n))
    (sr : LinearSys.MaxBackReachState n) (hs : s.Encloses sr) (hΔt : 0 < toReal Δt)
    (hU0 : (0 : Vec ℝ n) ∈ U.I_error.construct) (hU : U.construct ⊆ construct Ur)
    (hWE : W₀.I_error = Interval.point fun _ => FloatOps.zero) (hW₀r : W₀r.construct ⊆ W₀.construct)
    (hZw : construct (Zwr sr.t) ⊆ (Zw s.tEnc.inf s.tEnc.sup).construct)
    (hP₁ : P₁.construct ⊆ P₁r.construct)
    (hP₂ : P₂.construct ⊆ P₂r.construct) (hP₁0 : (0 : Vec ℝ n) ∈ P₁.I_error.construct)
    (hP₂0 : (0 : Vec ℝ n) ∈ P₂.I_error.construct)
    (hker₁ : ∀ i (y : Vec ℝ n), (toRealMat P₁.Ae *ᵥ y) i = 0)
    (hker₂ : ∀ i (y : Vec ℝ n), (toRealMat P₂.Ae *ᵥ y) i = 0)
    (hkerr₁ : ∀ (i : Fin P₁r.me) (y : Vec ℝ n), P₁r.Ae i y = 0)
    (hkerr₂ : ∀ (i : Fin P₂r.me) (y : Vec ℝ n), P₂r.Ae i y = 0)
    (hP₁b : Bornology.IsBounded P₁r.dropEqs.construct)
    (hP₂b : Bornology.IsBounded P₂r.dropEqs.construct) : -- --- CONCL ---
    ∀ η' ∈ sys.reachOrderFloat Δt Δt η,
      ∀ s' ∈ sys.maxBackReachStepFloat Bx P₁ P₂ U W₀ Zw Δt η s,
        s'.Encloses
          (sys.maxBackReachStep ρ P₁r P₂r hP₁b hP₂b Ur W₀r Zwr (toReal Δt) η'
            sr) := by -- --- PROOF ---
  intro η' (hη' : sys.reachOrderFloat Δt Δt η = some η') s' (h : sys.maxBackReachStepFloat Bx P₁ P₂
      U W₀ Zw Δt η s = some s')
  unfold LinearSys.maxBackReachStepFloat at h
  extract_lets tk1Lo tk1Hi Z₀ ζ Hs at h
  simp (config := { zeta := false }) only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨ηk, hηk, ηk1, hηk1, ηn, hηn, η'', hη'', h⟩ := h
  obtain rfl : η' = η'' := Option.some.inj (hη'.symm.trans hη'')
  extract_lets Φk Ψ Φn I M T ZU UErr ZW₀ ZW DU ρe ZWe C₁ C₂ H at h
  split_ifs at h with hc
  simp only [Option.pure_def, Option.some.injEq] at h
  subst h
  -- the exact objects of the step, named
  set A := Scalar.toRealMat sys.A with hA
  set Δ := toReal Δt with hΔ
  set Φk' : Mat ℝ n n := exp (sr.t • A) with hΦk'
  set Ξ : Mat ℝ n n := Real.MatExp.expIntegral A Δ with hΞ
  have hadmk := (LinearSys.reachOrderFloat_spec _ hηk).1
  have hadmk1 := (LinearSys.reachOrderFloat_spec _ hηk1).1
  have hadmn := (LinearSys.reachOrderFloat_spec _ hηn).1
  have hadm' := (LinearSys.reachOrderFloat_spec _ hη').1
  have hW := sys.inputSolution_subset_inputSolutionFloat hΔt.le hadm' hWE hW₀r
  -- the brackets of `t_{k+1}`
  have h1lo : toReal tk1Lo ≤ sr.t + Δ := by
    have := addDown_le_add s.tEnc.inf Δt
    linarith [hs.tEnc_inf_le]
  have h1hi : sr.t + Δ ≤ toReal tk1Hi := by
    have := add_le_addUp s.tEnc.sup Δt
    linarith [hs.le_tEnc_sup]
  -- the matrices are in their interval matrices
  have hΦk : Φk' ∈ Φk.construct := sys.exp_mem_expIntervalFloat hadmk hs.tEnc_inf_le hs.le_tEnc_sup
  have hI : Ξ ∈ I.construct := sys.expIntegral_mem_adaptiveIntegralFloat hΔt.le hadm'
  have hM : Φk' * Ξ ∈ M.construct := Interval.matMul_outer _ _ hΦk hI
  have hT0 : (0 : Vec ℝ n) ∈ T.I_error.construct := by
    show (0 : Vec ℝ n) ∈ ((Zonotope.mtimesIntervalMat M U).materialise).I_error.construct
    rw [Zonotope.materialise_eq]
    exact Zonotope.zero_mem_mtimesIntervalMat_error hM hU0
  -- the disturbance sets: the exact `Ẑ_{W₀}` is inside the float one
  have h5 : construct (sys.maxBackReachStep ρ P₁r P₂r hP₁b hP₂b Ur W₀r Zwr Δ η' sr).ZW₀ ⊆
      ZW₀.construct := by
    show (CORALean.Real.Zonotope.plus sr.ZW₀ (CORALean.Real.Zonotope.mtimes Φk'
      (sys.inputSolution (S := 𝒵) Δ η' W₀r))).construct
      ⊆ ZW₀.construct
    rw [← CORALean.Real.Zonotope.plus_exact]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    rw [← CORALean.Real.Zonotope.mtimes_exact] at hb
    obtain ⟨b', hb', rfl⟩ := hb
    exact Plus.plus_outer s.ZW₀ _ (Set.add_mem_add (hs.ZW₀ ha)
      (Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋]) Φk _
        (Set.mem_biUnion hΦk (Set.mem_image_of_mem _ (hW hb')))))
  -- and so is the new `Ẑ_W`: the new `Ẑ_{W₀}` plus the disturbance part
  have h6 : construct (sys.maxBackReachStep ρ P₁r P₂r hP₁b hP₂b Ur W₀r Zwr Δ η' sr).ZW ⊆
      ZW.construct := by
    intro x hx
    have hx2 : x ∈ (CORALean.Real.Zonotope.plus
        (sys.maxBackReachStep ρ P₁r P₂r hP₁b hP₂b Ur W₀r Zwr Δ η' sr).ZW₀
          (Zwr sr.t)).construct := hx
    rw [← CORALean.Real.Zonotope.plus_exact] at hx2
    obtain ⟨a, ha, b, hb, rfl⟩ := hx2
    exact Plus.plus_outer ZW₀ _ (Set.add_mem_add (h5 ha) (hZw hb))
  refine ⟨h1lo, h1hi, ?_, ?_, h5, h6, ?_⟩
  -- the error box of the new `Z̲_U` holds `0`
  · show (0 : Vec ℝ n) ∈ ((Zonotope.plus s.ZU T).materialise).I_error.construct
    rw [Zonotope.materialise_eq]
    exact Zonotope.zero_mem_plus_error hs.zero_mem hT0
  -- a point of the new `Z̲_U`: the old one's, plus the new term's, plus the boxes
  · intro x hx
    have hx' : x ∈ (Zonotope.plus s.ZU T).construct := by
      have h := hx
      simp only [ZU, Plus.plus, Zonotope.materialise_eq] at h
      exact h
    obtain ⟨_, ⟨sa, hsa, tb, htb, rfl⟩, p, hp, rfl⟩ :=
      Zonotope.plus_subset_add_box s.ZU T hs.zero_mem hT0 hx'
    -- the old point is an exact one plus its error, the new term an exact image plus the box
    obtain ⟨u₁, hu₁, e₁, he₁, rfl⟩ := hs.ZU sa hsa
    have htb' : tb ∈ (Zonotope.mtimesIntervalMat M U).construct := by
      have h := htb
      simp only [T, Mtimes.mtimes, Zonotope.materialise_eq] at h
      exact h
    obtain ⟨_, ⟨u, hu, rfl⟩, b, hb, rfl⟩ :=
      Zonotope.mtimesIntervalMat_subset_add_box M U hU0 hM htb'
    -- the exact point is `u₁` plus the exact term, the error the three together
    refine ⟨u₁ + Φk' *ᵥ (Ξ *ᵥ u), ?_, e₁ + b + p, fun i => ?_, ?_⟩
    · show _ ∈ (CORALean.Real.Zonotope.plus sr.ZU (CORALean.Real.Zonotope.mtimes Φk'
        (CORALean.Real.Zonotope.mtimes Ξ Ur))).construct
      rw [← CORALean.Real.Zonotope.plus_exact]
      refine ⟨u₁, hu₁, _, ?_, rfl⟩
      rw [← CORALean.Real.Zonotope.mtimes_exact]
      refine ⟨Ξ *ᵥ u, ?_, rfl⟩
      rw [← CORALean.Real.Zonotope.mtimes_exact]
      exact ⟨u, hU hu, rfl⟩
    · -- the three errors, each within its bound, add up within the new `UErr`
      have h1 := he₁ i
      have h2 := Interval.abs_le_magnitude hb i
      have h3 := Interval.abs_le_magnitude hp i
      have h4 := add_le_addUp (s.UErr i) ((Zonotope.mtimesIntervalMatBox M U).magnitude i)
      have h5 := add_le_addUp (addUp (s.UErr i) ((Zonotope.mtimesIntervalMatBox M U).magnitude i))
        ((s.ZU.plusBox T).magnitude i)
      show |(e₁ + b + p) i| ≤ toReal (addUp (addUp (s.UErr i) _) _)
      simp only [Pi.add_apply]
      calc |e₁ i + b i + p i| ≤ |e₁ i| + |b i| + |p i| := by
            refine le_trans (abs_add_le _ _) ?_
            linarith [abs_add_le (e₁ i) (b i)]
        _ ≤ _ := by linarith
    · show u₁ + e₁ + ((Φk' * Ξ) *ᵥ u + b) + p = u₁ + Φk' *ᵥ (Ξ *ᵥ u) + (e₁ + b + p)
      rw [← Matrix.mulVec_mulVec]
      abel
  -- the inner approximation
  · intro p hp
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hp
    -- the exact matrices of line 12, and their intervals
    set Φ : Mat ℝ n n := exp ((-(sr.t + Δ)) • A) with hΦ
    set Ψ' : Mat ℝ n n := exp ((sr.t + Δ) • A) with hΨ'
    have hΦn : Φ ∈ Φn.construct := sys.exp_mem_expIntervalFloat hadmn
      (by rw [toReal_neg]; linarith) (by rw [toReal_neg]; linarith)
    have hΨ : Ψ' ∈ Ψ.construct := sys.exp_mem_expIntervalFloat hadmk1 h1lo h1hi
    have hΦΨ : Φ * Ψ' = 1 := by
      have hcomm : Commute ((-(sr.t + Δ)) • A) ((sr.t + Δ) • A) :=
        ((Commute.refl _).smul_left _).smul_right _
      have h := (NormedSpace.exp_add_of_commute hcomm).symm
      rw [← add_smul, neg_add_cancel, zero_smul, NormedSpace.exp_zero] at h
      exact h
    -- the hull part: a point `z` of the stored hull, mapped within the rounding of `Φ̄ z`
    have ha' : a ∈ nominalSet (ConZonotope.mtimesNominal Φn.inf H) :=
      (ConZonotope.construct_eq_nominal rfl).subset ha
    obtain ⟨z, hz, hzerr⟩ := ConZonotope.mtimesNominal_err Φn.inf H ha'
    have hne₁ : (nominalSet C₁).Nonempty :=
      ConZonotope.zeroFeasible_nonempty (Bool.and_eq_true_iff.mp hc).1
    have hne₂ : (nominalSet C₂).Nonempty :=
      ConZonotope.zeroFeasible_nonempty (Bool.and_eq_true_iff.mp hc).2
    -- both constraint polytopes are carried onto the coefficients without slack
    have hsf : ∀ (Q : HPolytope 𝕋 (Vec 𝕋 n)) (Z : Zonotope (Vec 𝕋 n)),
        (Q.onCoefficientsInner Z).IsSlackFree := fun Q Z => by
      unfold HPolytope.onCoefficientsInner
      split <;> exact ⟨fun _ => toReal_zero, fun _ => toReal_zero⟩
    obtain ⟨y₁, hy₁, y₂, hy₂, lam, ⟨hl0, hl1⟩, hzeq⟩ :=
      ConZonotope.aux_linCombSameCenter_subset C₁ C₂ rfl (hsf _ _) (hsf _ _) hne₁ hne₂ hz
    -- its points are within `ζ` of the origin
    have hζ₁ : ∀ k, |y₁ k| ≤ toReal (ζ k) := fun k =>
      HPolytope.aux_abs_nominal_conZonotopeInnerOf_le _ Bx.zonotope hy₁ k
    have hζ₂ : ∀ k, |y₂ k| ≤ toReal (ζ k) := fun k =>
      HPolytope.aux_abs_nominal_conZonotopeInnerOf_le _ Bx.zonotope hy₂ k
    have hζ : ∀ k, |z k| ≤ toReal (ζ k) := fun k => by
      rw [hzeq]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      calc |lam * y₁ k + (1 - lam) * y₂ k| ≤ |lam * y₁ k| + |(1 - lam) * y₂ k| := abs_add_le _ _
        _ = lam * |y₁ k| + (1 - lam) * |y₂ k| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hl0,
              abs_of_nonneg (show (0 : ℝ) ≤ 1 - lam by linarith)]
        _ ≤ lam * toReal (ζ k) + (1 - lam) * toReal (ζ k) :=
            add_le_add (mul_le_mul_of_nonneg_left (hζ₁ k) hl0)
              (mul_le_mul_of_nonneg_left (hζ₂ k) (by linarith))
        _ = toReal (ζ k) := by ring
    -- the second summand: `Φ` applied to a point of `Z̲_U(t_k)`, within `DU`
    have hb' : -b ∈ (Zonotope.mtimesIntervalMat Φn s.ZU).construct := by
      have h := Set.mem_neg.mp hb
      simp only [Mtimes.mtimes, Zonotope.materialise_eq] at h
      exact h
    obtain ⟨_, ⟨w, hw, rfl⟩, bm, hbm, hbeq⟩ :=
      Zonotope.mtimesIntervalMat_subset_add_box Φn s.ZU hs.zero_mem hΦn hb'
    obtain ⟨u, hu, e, he, rfl⟩ := hs.ZU w hw
    -- `b` is `Φ` of an exact point plus the error `bU` of the old `Z̲_U` and the box
    set bU : Vec ℝ n := -(Φ *ᵥ e) - bm with hbU
    have hbsplit : b = Φ *ᵥ (-u) + bU := by
      have hbeq' : Φ *ᵥ (u + e) + bm = -b := hbeq
      have h := congrArg Neg.neg hbeq'.symm
      rw [neg_neg] at h
      rw [h, hbU, Matrix.mulVec_neg, Matrix.mulVec_add]
      abel
    have hbU_le : ∀ i, |bU i| ≤ toReal (DU i) := fun i => by
      have h1 := Interval.abs_mulVec_le_magnitudeMat hΦn he i
      have h2 := Interval.abs_le_magnitude hbm i
      have h3 := add_le_addUp ((Zonotope.mtimesIntervalMatBox Φn s.ZU).magnitude i)
        (dotUp (Φn.magnitudeMat i) s.UErr)
      show |(-(Φ *ᵥ e) - bm) i| ≤ toReal (addUp _ _)
      simp only [Pi.sub_apply, Pi.neg_apply]
      calc |-(Φ *ᵥ e) i - bm i| ≤ |-(Φ *ᵥ e) i| + |bm i| := abs_sub _ _
        _ = |(Φ *ᵥ e) i| + |bm i| := by rw [abs_neg]
        _ ≤ _ := by linarith
    -- the hull part's distance to the exact image: `d = a - Φ z`
    set d : Vec ℝ n := a - Φ *ᵥ z with hd
    have hWb : ∀ i k, |(toRealMat Φn.inf - Φ) i k|
        ≤ toReal (subUp (Φn.sup i k) (Φn.inf i k)) := fun i k => by
      have hk := Interval.mem_mat_iff.mp hΦn i k
      have hs' := sub_le_subUp (Φn.sup i k) (Φn.inf i k)
      rw [Matrix.sub_apply, abs_sub_comm,
        abs_of_nonneg (sub_nonneg.mpr (by simpa [toRealMat] using hk.1))]
      show Φ i k - toReal (Φn.inf i k) ≤ _
      linarith [hk.2]
    have hdle : ∀ i, |d i| ≤ toReal (addUp (dotUp (fun k => subUp (Φn.sup i k) (Φn.inf i k)) ζ)
        (ConZonotope.mtimesNominalErr Φn.inf Hs i)) := fun i => by
      -- the hull and its shape have the same center and generators, which are all the error reads
      have hshape : ConZonotope.mtimesNominalErr Φn.inf H
          = ConZonotope.mtimesNominalErr Φn.inf Hs := by
        have hc : H.c = Hs.c := rfl
        have hG : H.G = Hs.G := rfl
        unfold ConZonotope.mtimesNominalErr
        rw [hc, hG]
        rfl
      have h1 : |a i - (toRealMat Φn.inf *ᵥ z) i|
          ≤ toReal (ConZonotope.mtimesNominalErr Φn.inf Hs i) := by
        rw [← hshape]
        exact hzerr i
      have h2 := abs_mulVec_le_dotUp hWb hζ i
      have h3 := add_le_addUp (dotUp (fun k => subUp (Φn.sup i k) (Φn.inf i k)) ζ)
        (ConZonotope.mtimesNominalErr Φn.inf Hs i)
      have h4 : d i = (a i - (toRealMat Φn.inf *ᵥ z) i) + ((toRealMat Φn.inf - Φ) *ᵥ z) i := by
        rw [Matrix.sub_mulVec, hd]
        simp only [Pi.sub_apply]
        ring
      rw [h4]
      exact le_trans (abs_add_le _ _) (by linarith)
    -- carried back by `Ψ = e^{A t_{k+1}}`, the two distances together stay within the erosion
    set δ : Vec ℝ n := Ψ' *ᵥ (d + bU) with hδ
    have hδle : ∀ i, |δ i| ≤ toReal (ρe i) := fun i => by
      have hdd : ∀ k, |(d + bU) k| ≤ toReal (addUp (addUp (dotUp (fun k' => subUp (Φn.sup k k')
          (Φn.inf k k')) ζ) (ConZonotope.mtimesNominalErr Φn.inf Hs k)) (DU k)) := fun k => by
        have h1 := hdle k
        have h2 := hbU_le k
        have h3 := add_le_addUp (addUp (dotUp (fun k' => subUp (Φn.sup k k') (Φn.inf k k')) ζ)
          (ConZonotope.mtimesNominalErr Φn.inf Hs k)) (DU k)
        simp only [Pi.add_apply]
        exact le_trans (abs_add_le _ _) (by linarith)
      exact Interval.abs_mulVec_le_magnitudeMat hΨ hdd i
    -- each converted set, moved by that distance, stays in the exact one
    have hδmem : δ ∈ (Interval.mk (-ρe) ρe).construct := fun i => by
      have h := abs_le.mp (hδle i)
      show toReal (neg (ρe i)) ≤ δ i ∧ δ i ≤ toReal (ρe i)
      rw [toReal_neg]
      exact ⟨h.1, h.2⟩
    have hblock : ∀ (P : HPolytope 𝕋 (Vec 𝕋 n)) (Pr : CORALean.Real.HPolytope (Vec ℝ n)),
        P.construct ⊆ Pr.construct → (0 : Vec ℝ n) ∈ P.I_error.construct →
        (∀ i (y : Vec ℝ n), (toRealMat P.Ae *ᵥ y) i = 0) →
        (∀ (i : Fin Pr.me) (y : Vec ℝ n), Pr.Ae i y = 0) →
        ∀ hPrb : Bornology.IsBounded Pr.dropEqs.construct,
        ∀ y ∈ nominalSet (LinearSys.maxBackReachCZFloat Bx P ZWe),
          y + δ ∈ (LinearSys.maxBackReachCZ ρ Pr hPrb
            (sys.maxBackReachStep ρ P₁r P₂r hP₁b hP₂b Ur W₀r Zwr Δ η' sr).ZW).construct := by
      intro P Pr hP hP0 hker hkerr hPrb y hy
      have hyc : y ∈ (LinearSys.maxBackReachCZFloat Bx P ZWe).construct :=
        ⟨y, hy, 0, hP0, add_zero y⟩
      have hin := LinearSys.maxBackReachCZFloat_inner Bx P ZWe (fun i y _ => hker i y) hyc
      refine LinearSys.minkowskiDiff_subset_maxBackReachCZ ρ Pr _ hPrb hkerr (fun w hw => ?_)
      -- the widened disturbance set holds `w` moved by `δ`, which `y` survives
      have hwδ : w + δ ∈ ZWe.construct :=
        Plus.plus_outer ZW _ (Set.add_mem_add (h6 hw) (Interval.zonotope_contains _ hδmem))
      have h := hin (w + δ) hwδ
      have h' : y + δ + w ∈ P.construct := by
        rw [show y + δ + w = y + (w + δ) by abel]
        exact h
      exact hP h'
    -- the moved point is a segment between the two exact sets, so in their hull
    have hyseg : z + δ ∈ Set.linComb (LinearSys.maxBackReachCZ ρ P₁r hP₁b
          (sys.maxBackReachStep ρ P₁r P₂r hP₁b hP₂b Ur W₀r Zwr Δ η' sr).ZW).construct
        (LinearSys.maxBackReachCZ ρ P₂r hP₂b
          (sys.maxBackReachStep ρ P₁r P₂r hP₁b hP₂b Ur W₀r Zwr Δ η' sr).ZW).construct :=
      ⟨y₁ + δ, hblock P₁ P₁r hP₁ hP₁0 hker₁ hkerr₁ hP₁b y₁ hy₁, y₂ + δ,
        hblock P₂ P₂r hP₂ hP₂0 hker₂ hkerr₂ hP₂b y₂ hy₂, lam, ⟨hl0, hl1⟩, by rw [hzeq]; module⟩
    have hlin := CORALean.Real.ConZonotope.linComb_outer _ _ hyseg
    -- line 12: the map of the hull and the negated `Z̲_U`, spelled out
    have hR : (sys.maxBackReachStep ρ P₁r P₂r hP₁b hP₂b Ur W₀r Zwr Δ η' sr).R
        = CORALean.Real.ConZonotope.mtimes Φ (CORALean.Real.ConZonotope.plus
          (CORALean.Real.ConZonotope.linComb (LinearSys.maxBackReachCZ ρ P₁r hP₁b
            (sys.maxBackReachStep ρ P₁r P₂r hP₁b hP₂b Ur W₀r Zwr Δ η' sr).ZW)
            (LinearSys.maxBackReachCZ ρ P₂r hP₂b
              (sys.maxBackReachStep ρ P₁r P₂r hP₁b hP₂b Ur W₀r Zwr Δ η' sr).ZW))
          (CORALean.Real.Zonotope.conZonotope
            (CORALean.Real.Zonotope.mtimes (-(1 : Mat ℝ n n)) sr.ZU))) := rfl
    change a + b ∈ (sys.maxBackReachStep ρ P₁r P₂r hP₁b hP₂b Ur W₀r Zwr Δ η' sr).R.construct
    rw [hR, ← CORALean.Real.ConZonotope.mtimes_exact, ← CORALean.Real.ConZonotope.plus_exact,
      ← CORALean.Real.Zonotope.conZonotope_exact, ← CORALean.Real.Zonotope.mtimes_exact]
    refine ⟨z + δ + (-(1 : Mat ℝ n n)) *ᵥ u, Set.add_mem_add hlin ⟨u, hu, rfl⟩, ?_⟩
    -- `Φ (z + Ψ (d + bU) - u) = a + b`
    have e1 : Φ *ᵥ δ = d + bU := by
      rw [hδ, Matrix.mulVec_mulVec, hΦΨ, Matrix.one_mulVec]
    have e2 : Φ *ᵥ ((-(1 : Mat ℝ n n)) *ᵥ u) = -(Φ *ᵥ u) := by
      rw [Matrix.neg_mulVec, Matrix.one_mulVec, Matrix.mulVec_neg]
    show Φ *ᵥ (z + δ + (-(1 : Mat ℝ n n)) *ᵥ u) = a + b
    rw [Matrix.mulVec_add, Matrix.mulVec_add, e1, e2, hbsplit, Matrix.mulVec_neg, hd]
    abel


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
