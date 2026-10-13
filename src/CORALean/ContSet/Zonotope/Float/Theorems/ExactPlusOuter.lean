module

public import CORALean.ContSet.Zonotope.Float.Operations.ExactPlus
public import CORALean.ContSet.Zonotope.Float.Operations.ExactPlusGap
public import CORALean.ContSet.Zonotope.Real.Theorems.ExactPlusExact
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError
public import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter

@[expose] public section

/-!
# `Zonotope.exactPlus` encloses the exact one

The exact layer's `exactPlus` of the stored operands' nominal parts, plus the two error boxes, lies
in the rounded `exactPlus`. The shared columns' stored sums sit within the gap `subUp` computes of
the exact sums, the copied columns are exact, and the centre's rounding is its residual, as in
`Zonotope.plus_outer`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A pairwise sum stored rounded down is within the gap `subUp` of the sum rounded up. -/
theorem Zonotope.aux_pairSum_gap (a b : 𝕋) :
    |toReal a + toReal b - toReal (addDown a b)| ≤
      toReal (subUp (addUp a b) (addDown a b)) := by -- --- PROOF ---
  have h1 := addDown_le_add a b
  have h2 := add_le_addUp a b
  have h3 := sub_le_subUp (addUp a b) (addDown a b)
  rw [abs_le]
  constructor <;> linarith

/-- A stored generator entry is within its gap of the exact column. -/
theorem Zonotope.aux_exactPlus_gap (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) (k : ℕ) (i : Fin n)
    (j : Fin (min (min Z₁.h Z₂.h) k + (Z₁.h - min (min Z₁.h Z₂.h) k) +
      (Z₂.h - min (min Z₁.h Z₂.h) k))) :
    |((Real.Zonotope.exactPlus (nominal Z₁) (nominal Z₂) k).G j) i
        - toReal ((Z₁.exactPlus Z₂ k).G j i)| ≤
      toReal (Z₁.exactPlusGap Z₂ k i j) := by -- --- PROOF ---
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · -- a shared column: the stored sum is rounded down, the gap is up minus down
      have e1 : ((nominal Z₁).exactPlus (nominal Z₂) k).G (Fin.castAdd _ (Fin.castAdd _ j)) i =
          toReal (Z₁.G (Fin.castLE (min_le_left _ _ |>.trans (min_le_left _ _)) j) i) +
            toReal (Z₂.G (Fin.castLE (min_le_left _ _ |>.trans (min_le_right _ _)) j) i) := by
        simp only [Real.Zonotope.exactPlus, Fin.append_left, Pi.add_apply]
        rfl
      have e2 : (Z₁.exactPlus Z₂ k).G (Fin.castAdd _ (Fin.castAdd _ j)) i =
          addDown (Z₁.G (Fin.castLE (min_le_left _ _ |>.trans (min_le_left _ _)) j) i)
            (Z₂.G (Fin.castLE (min_le_left _ _ |>.trans (min_le_right _ _)) j) i) := by
        simp only [Zonotope.exactPlus, Fin.append_left]
      have e3 : Z₁.exactPlusGap Z₂ k i (Fin.castAdd _ (Fin.castAdd _ j)) =
          subUp (addUp (Z₁.G (Fin.castLE (min_le_left _ _ |>.trans (min_le_left _ _)) j) i)
            (Z₂.G (Fin.castLE (min_le_left _ _ |>.trans (min_le_right _ _)) j) i))
            (addDown (Z₁.G (Fin.castLE (min_le_left _ _ |>.trans (min_le_left _ _)) j) i)
              (Z₂.G (Fin.castLE (min_le_left _ _ |>.trans (min_le_right _ _)) j) i)) := by
        simp only [Zonotope.exactPlusGap, Fin.append_left]
      erw [e1, e2, e3]
      exact Zonotope.aux_pairSum_gap _ _
    · -- a copied column of the first operand: exact
      have e1 : ((nominal Z₁).exactPlus (nominal Z₂) k).G (Fin.castAdd _ (Fin.natAdd _ j)) i =
          toReal (Z₁.G ⟨min (min Z₁.h Z₂.h) k + j, by have := j.2; omega⟩ i) := by
        simp only [Real.Zonotope.exactPlus, Fin.append_left, Fin.append_right]
        rfl
      have e2 : (Z₁.exactPlus Z₂ k).G (Fin.castAdd _ (Fin.natAdd _ j)) i =
          Z₁.G ⟨min (min Z₁.h Z₂.h) k + j, by have := j.2; omega⟩ i := by
        simp only [Zonotope.exactPlus, Fin.append_left, Fin.append_right]
      have e3 : Z₁.exactPlusGap Z₂ k i (Fin.castAdd _ (Fin.natAdd _ j)) = zero := by
        simp only [Zonotope.exactPlusGap, Fin.append_left, Fin.append_right]
      erw [e1, e2, e3]
      simp [toReal_zero]
  · -- a copied column of the second operand: exact
    have e1 : ((nominal Z₁).exactPlus (nominal Z₂) k).G (Fin.natAdd _ j) i =
        toReal (Z₂.G ⟨min (min Z₁.h Z₂.h) k + j, by have := j.2; omega⟩ i) := by
      simp only [Real.Zonotope.exactPlus, Fin.append_right]
      rfl
    have e2 : (Z₁.exactPlus Z₂ k).G (Fin.natAdd _ j) i =
        Z₂.G ⟨min (min Z₁.h Z₂.h) k + j, by have := j.2; omega⟩ i := by
      simp only [Zonotope.exactPlus, Fin.append_right]
    have e3 : Z₁.exactPlusGap Z₂ k i (Fin.natAdd _ j) = zero := by
      simp only [Zonotope.exactPlusGap, Fin.append_right]
    erw [e1, e2, e3]
    simp [toReal_zero]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.exactPlus_outer (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) (k : ℕ) :
    (Real.Zonotope.exactPlus (nominal Z₁) (nominal Z₂) k).construct
      + (Z₁.E.construct + Z₂.E.construct) ⊆ (Z₁.exactPlus Z₂ k).construct := by -- --- PROOF ---
  rintro _ ⟨y, ⟨δ, hδ, rfl⟩, _, ⟨e₁, he₁, e₂, he₂, rfl⟩, rfl⟩
  set F := Z₁.exactPlus Z₂ k with hF
  -- the stored nominal point on the same coefficients
  have hp : (fun i => toReal (F.c i) + ∑ j, toReal (F.G j i) * δ j) ∈ nominalSet F :=
    Zonotope.mem_nominalSet_iff.mpr ⟨δ, hδ, fun _ => rfl⟩
  -- the centre's rounding, and the shared columns' rounding
  have hr₁ : (fun i => (toReal (Z₁.c i) + toReal (Z₂.c i)) - toReal (F.c i)) ∈
      (Zonotope.centerResidual Z₁.c Z₂.c).construct :=
    Interval.sub_mem_residual (fun i => ⟨addDown_le_add _ _, add_le_addUp _ _⟩)
  have hr₂ : (fun i => ∑ j, (((Real.Zonotope.exactPlus (nominal Z₁) (nominal Z₂) k).G j) i
      - toReal (F.G j i)) * δ j) ∈ (Zonotope.generatorError (Z₁.exactPlusGap Z₂ k)).construct :=
    Zonotope.mem_generatorError (fun i j => Zonotope.aux_exactPlus_gap Z₁ Z₂ k i j) hδ
  -- the box absorbs the two incoming boxes and both roundings
  have hE : e₁ + e₂ + (fun i => (toReal (Z₁.c i) + toReal (Z₂.c i)) - toReal (F.c i))
      + (fun i => ∑ j, (((Real.Zonotope.exactPlus (nominal Z₁) (nominal Z₂) k).G j) i
        - toReal (F.G j i)) * δ j) ∈ F.E.construct :=
    Interval.plus_outer _ _ ⟨_, Interval.plus_outer _ _ ⟨_, Interval.plus_outer _ _
      ⟨e₁, he₁, e₂, he₂, rfl⟩, _, hr₁, rfl⟩, _, hr₂, rfl⟩
  refine ⟨_, hp, _, hE, ?_⟩
  funext i
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  -- the exact centre and the exact sum of columns, split at the stored ones
  have hc : ((nominal Z₁).exactPlus (nominal Z₂) k).c i = toReal (Z₁.c i) + toReal (Z₂.c i) :=
    rfl
  have hs : ∑ x, δ x * ((nominal Z₁).exactPlus (nominal Z₂) k).G x i =
      ∑ j, toReal (F.G j i) * δ j + ∑ j, (((nominal Z₁).exactPlus (nominal Z₂) k).G j i
        - toReal (F.G j i)) * δ j := by
    erw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hc, hs]
  ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
