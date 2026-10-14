module

public import CORALean.ContSet.ConZonotope.Float.Operations.LinComb
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.ConZonotope.Real.Theorems.AbsSmulCoeffLeOne
public import CORALean.ContSet.HPolytope.Float.Operations.MemUnitBoxIff
public import CORALean.ContSet.HPolytope.Float.Operations.SmulMemHalfScaledLeft
public import CORALean.ContSet.HPolytope.Float.Operations.SmulMemHalfScaledRight
public import CORALean.ContSet.InflatedContSet.Theorems.LinCombSubset
public import CORALean.ContSet.Interval.Float.Theorems.LinCombOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError
public import CORALean.ContSet.Zonotope.Float.Theorems.MidpointMemResidual

@[expose] public section

/-!
# `ConZonotope.linComb` encloses every segment between the two

`InflatedContSet.linComb_subset` reduces this to two obligations: the nominal
part spills only by what rounded, and the box absorbs that spill along with the
segment between the two incoming boxes.

The nominal obligation is the exact argument at the same coefficients — `λ β₁`,
`(1 - λ) β₂` and `2λ - 1` — and the constraints cost nothing to carry: the
weighted rows are the incoming rows against a nonnegative weight, which is what
`smul_mem_halfScaledLeft` and its mirror say. Only the centre and the centre
generator are displaced from what ℝ would have, so only they are charged.

`aux_linCombCoeff` and `aux_linCombGReal` are `noncomputable`: both name a real
number — a real-scaled coefficient, a real-halved centre gap — only to state
what this file proves about it, and neither is read back into
`ConZonotope.linComb`, which stores no real. Inherent to arguing about ℝ, not a
gap in what runs.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   08-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The coefficients the segment supplies: each side's own, weighted, and the
interpolation parameter on the centre generator. -/
noncomputable def ConZonotope.aux_linCombCoeff {h₁ h₂ : ℕ} (β₁ : Vec ℝ h₁) (β₂ : Vec ℝ h₂)
    (lam : ℝ) : Vec ℝ (h₁ + h₂ + 1) :=
  Fin.append (Fin.append (lam • β₁) ((1 - lam) • β₂)) fun _ : Fin 1 => 2 * lam - 1

/-- The generator row `linComb` would store if nothing rounded. -/
noncomputable def ConZonotope.aux_linCombGReal (cZ₁ cZ₂ : ConZonotope 𝕋 (Vec 𝕋 n)) (i : Fin n) :
    Fin (cZ₁.h + cZ₂.h + 1) → ℝ :=
  Fin.append (Fin.append (fun j => toReal (cZ₁.G j i)) fun j => toReal (cZ₂.G j i))
    fun _ : Fin 1 => (toReal (cZ₁.c i) - toReal (cZ₂.c i)) / 2

/-- Every weighted coefficient is admissible, the fresh one because `2λ - 1` is
in `[-1, 1]`. -/
theorem ConZonotope.aux_abs_linCombCoeff {h₁ h₂ : ℕ} {β₁ : Vec ℝ h₁} {β₂ : Vec ℝ h₂} {lam : ℝ}
    (hβ₁ : ∀ j, |β₁ j| ≤ 1) (hβ₂ : ∀ j, |β₂ j| ≤ 1) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) :
    ∀ j, |ConZonotope.aux_linCombCoeff β₁ β₂ lam j| ≤ 1 := by -- --- PROOF ---
  have hm0 : (0:ℝ) ≤ 1 - lam := by linarith
  have hm1 : (1:ℝ) - lam ≤ 1 := by linarith
  simp only [ConZonotope.aux_linCombCoeff]
  refine Fin.addCases ?_ ?_
  · refine Fin.addCases ?_ ?_
    · intro j
      simpa using Real.ConZonotope.abs_smul_coeff_le_one hl0 hl1 hβ₁ j
    · intro j
      simpa using Real.ConZonotope.abs_smul_coeff_le_one hm0 hm1 hβ₂ j
  · intro _
    simp only [Fin.append_right]
    rw [abs_le]
    constructor <;> linarith

/-- Each block answers to its own constraints, and to its own unit box, at the
weight the trailing coefficient names. -/
theorem ConZonotope.aux_mem_linComb_P (cZ₁ cZ₂ : ConZonotope 𝕋 (Vec 𝕋 n)) {β₁ : Vec ℝ cZ₁.h}
    {β₂ : Vec ℝ cZ₂.h} {lam : ℝ} (hβ₁ : ∀ j, |β₁ j| ≤ 1) (hP₁ : β₁ ∈ cZ₁.P.construct)
    (hβ₂ : ∀ j, |β₂ j| ≤ 1) (hP₂ : β₂ ∈ cZ₂.P.construct) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) :
    ConZonotope.aux_linCombCoeff β₁ β₂ lam ∈ (cZ₁.linComb cZ₂).P.construct := by -- --- PROOF ---
  have hd₁ : β₁ ∈ (cZ₁.P.intersection (HPolytope.unitBox 𝕋 cZ₁.h)).construct :=
    HPolytope.mem_intersection_iff.mpr ⟨hP₁, HPolytope.mem_unitBox_iff.mpr hβ₁⟩
  have hd₂ : β₂ ∈ (cZ₂.P.intersection (HPolytope.unitBox 𝕋 cZ₂.h)).construct :=
    HPolytope.mem_intersection_iff.mpr ⟨hP₂, HPolytope.mem_unitBox_iff.mpr hβ₂⟩
  refine HPolytope.mem_intersection_iff.mpr
    ⟨HPolytope.smul_mem_halfScaledLeft (by ring) hl0 hd₁,
      HPolytope.smul_mem_halfScaledRight (by ring) (by linarith) hd₂⟩

/-- What the stored generators are wrong by, entrywise: nothing on the copied
blocks, and on the centre generator the gap `linCombGDiff` records. -/
theorem ConZonotope.aux_linCombG_error (cZ₁ cZ₂ : ConZonotope 𝕋 (Vec 𝕋 n)) (i : Fin n)
    (j : Fin (cZ₁.h + cZ₂.h + 1)) :
    |ConZonotope.aux_linCombGReal cZ₁ cZ₂ i j - toReal ((cZ₁.linComb cZ₂).G j i)|
      ≤ toReal (ConZonotope.linCombGDiff cZ₁ cZ₂ i j) := by -- --- PROOF ---
  simp only [ConZonotope.aux_linCombGReal, ConZonotope.linCombGDiff, ConZonotope.linComb]
  refine Fin.addCases ?_ ?_ j
  · refine Fin.addCases ?_ ?_
    · intro k
      simp only [Fin.append_left]
      rw [sub_self, abs_zero, toReal_zero]
    · intro k
      simp only [Fin.append_left, Fin.append_right]
      rw [sub_self, abs_zero, toReal_zero]
  -- the centre generator, the one column the two directed roundings differ on
  · intro _
    simp only [Fin.append_right]
    rw [toReal_half, abs_le]
    have hlo := subDown_le_sub (cZ₁.c i) (cZ₂.c i)
    have hhi := sub_le_subUp (cZ₁.c i) (cZ₂.c i)
    have hgap := sub_le_subUp (half (subUp (cZ₁.c i) (cZ₂.c i)))
      (half (subDown (cZ₁.c i) (cZ₂.c i)))
    rw [toReal_half, toReal_half] at hgap
    constructor <;> linarith

/-- One row of the exact generators against the coefficients the segment
supplies. -/
theorem ConZonotope.aux_linComb_row (cZ₁ cZ₂ : ConZonotope 𝕋 (Vec 𝕋 n)) (i : Fin n)
    (β₁ : Vec ℝ cZ₁.h)
    (β₂ : Vec ℝ cZ₂.h) (lam : ℝ) :
    (∑ j, ConZonotope.aux_linCombGReal cZ₁ cZ₂ i j * ConZonotope.aux_linCombCoeff β₁ β₂ lam j)
      = lam * (∑ j, toReal (cZ₁.G j i) * β₁ j) + (1 - lam) * (∑ j, toReal (cZ₂.G j i) * β₂ j)
        + (2 * lam - 1) * ((toReal (cZ₁.c i) - toReal (cZ₂.c i)) / 2) := by -- --- PROOF ---
  rw [Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_one]
  simp only [ConZonotope.aux_linCombGReal, ConZonotope.aux_linCombCoeff, Fin.append_left,
    Fin.append_right, Pi.smul_apply, smul_eq_mul]
  have e₁ : (∑ j, toReal (cZ₁.G j i) * (lam * β₁ j)) = lam * ∑ j, toReal (cZ₁.G j i) * β₁ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e₂ : (∑ j, toReal (cZ₂.G j i) * ((1 - lam) * β₂ j))
      = (1 - lam) * ∑ j, toReal (cZ₂.G j i) * β₂ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e₁, e₂]
  ring

/-- The nominal part spills only by what the centre and the centre generator
rounded. -/
theorem ConZonotope.aux_linComb_nominal (cZ₁ cZ₂ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    segments (nominalSet cZ₁) (nominalSet cZ₂) ⊆
      nominalSet (cZ₁.linComb cZ₂)
        + ((Zonotope.midpointResidual cZ₁.c cZ₂.c).construct
            + (Zonotope.generatorError
              (ConZonotope.linCombGDiff cZ₁ cZ₂)).construct) := by -- --- PROOF ---
  rintro _ ⟨y₁, hy₁', y₂, hy₂', lam, ⟨hl0, hl1⟩, rfl⟩
  obtain ⟨β₁, hβ₁, hP₁, hy₁⟩ := ConZonotope.mem_nominalSet_iff.mp hy₁'
  obtain ⟨β₂, hβ₂, hP₂, hy₂⟩ := ConZonotope.mem_nominalSet_iff.mp hy₂'
  have hβ := ConZonotope.aux_abs_linCombCoeff hβ₁ hβ₂ hl0 hl1
  -- the witness: the stored midpoint and generators at those coefficients
  refine ⟨fun i => toReal (Zonotope.midpoint cZ₁.c cZ₂.c i)
            + ∑ j : Fin (cZ₁.h + cZ₂.h + 1), toReal ((cZ₁.linComb cZ₂).G j i)
                * ConZonotope.aux_linCombCoeff β₁ β₂ lam j,
          ConZonotope.mem_nominalSet_iff.mpr ⟨ConZonotope.aux_linCombCoeff β₁ β₂ lam, hβ,
            ConZonotope.aux_mem_linComb_P cZ₁ cZ₂ hβ₁ hP₁ hβ₂ hP₂ hl0 hl1, fun _ => rfl⟩,
          _, ⟨_, Zonotope.midpoint_mem_residual cZ₁.c cZ₂.c,
              _, Zonotope.mem_generatorError (ConZonotope.aux_linCombG_error cZ₁ cZ₂) hβ, rfl⟩, ?_⟩
  funext i
  -- the stored generators and their shortfalls recombine into the exact ones
  have hsum : (∑ j : Fin (cZ₁.h + cZ₂.h + 1), toReal ((cZ₁.linComb cZ₂).G j i)
          * ConZonotope.aux_linCombCoeff β₁ β₂ lam j)
      + (∑ j, (ConZonotope.aux_linCombGReal cZ₁ cZ₂ i j - toReal ((cZ₁.linComb cZ₂).G j i))
          * ConZonotope.aux_linCombCoeff β₁ β₂ lam j)
      = ∑ j, ConZonotope.aux_linCombGReal cZ₁ cZ₂ i j
          * ConZonotope.aux_linCombCoeff β₁ β₂ lam j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hy₁ i, hy₂ i]
  rw [ConZonotope.aux_linComb_row cZ₁ cZ₂ i β₁ β₂ lam] at hsum
  linarith [hsum]

/-- The box absorbs the two incoming boxes, the centre rounding and the centre
generator's. -/
theorem ConZonotope.aux_linComb_error (cZ₁ cZ₂ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    segments cZ₁.I_error.construct cZ₂.I_error.construct
        + ((Zonotope.midpointResidual cZ₁.c cZ₂.c).construct
            + (Zonotope.generatorError (ConZonotope.linCombGDiff cZ₁ cZ₂)).construct)
      ⊆ (cZ₁.linComb cZ₂).I_error.construct :=
  subset_trans
    (Set.add_subset_add (Interval.linComb_outer cZ₁.I_error cZ₂.I_error) (Interval.plus_outer _ _))
    (Interval.plus_outer _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.linComb_outer (cZ₁ cZ₂ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    segments cZ₁.construct cZ₂.construct ⊆ (cZ₁.linComb cZ₂).construct :=
  InflatedContSet.linComb_subset (ConZonotope.aux_linComb_nominal cZ₁ cZ₂)
    (ConZonotope.aux_linComb_error cZ₁ cZ₂)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
