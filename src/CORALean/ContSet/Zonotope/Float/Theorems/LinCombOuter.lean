module

public import CORALean.ContSet.InflatedContSet.Theorems.LinCombSubset
public import CORALean.ContSet.Interval.Float.Theorems.LinCombOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
public import CORALean.ContSet.Zonotope.Float.Operations.LinComb
public import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Float.Theorems.MidpointMemResidual
public import CORALean.ContSet.Zonotope.Float.Theorems.PairDiffBracket
public import CORALean.ContSet.Zonotope.Float.Theorems.PairSumBracket
public import CORALean.ContSet.Zonotope.Float.Theorems.SumPairMul
public import CORALean.ContSet.Zonotope.Real.Theorems.LinCombOuter

@[expose] public section

/-!
# `Zonotope.linComb` contains every segment between the two zonotopes

`InflatedContSet.linComb_subset` reduces this to two obligations: the nominal
part spills only by what rounded, and the box absorbs that spill along with the
segment between the two incoming boxes.

The nominal obligation is the exact `linComb` argument at the same coefficients
— `pairCoeffSum`, `pairCoeffDiff` and `2λ-1` — with every stored value displaced
from the one ℝ would have. Nothing stored is unfolded: the center cancels
against its own residual and the generators against `linCombGDiff`, leaving the
identity the exact proof closes with, which `Zonotope.sum_pair` supplies.

The count is therefore still `h₁ + h₂ + 1`, every rounding having gone into the
box.
-/

-- Authors:       Claude Opus 5
-- Written:       19-August-2026
-- Last update:   03-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n h₁ h₂ : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The generator row `linComb` would store if nothing rounded: the exact
pairing over the real values the stored floats denote. -/
noncomputable def Zonotope.aux_linCombGReal (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) (i : Fin n) :
    Fin (Z₁.h + Z₂.h + 1) → ℝ :=
  Fin.append
    (Fin.append
      (Real.Zonotope.pairSum (fun j => toReal (Z₁.G j i)) (fun j => toReal (Z₂.G j i)))
      (Real.Zonotope.pairDiff (fun j => toReal (Z₁.G j i)) (fun j => toReal (Z₂.G j i))))
    (fun _ : Fin 1 => (toReal (Z₁.c i) - toReal (Z₂.c i)) / 2)

/-- Every stored generator sits at the low end of a bracket around its exact
value: the two blocks pair, and the center generator is one directed
difference. -/
theorem Zonotope.aux_linCombG_bracket (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) (i : Fin n) : -- --- STMT ---
    ∀ j : Fin (Z₁.h + Z₂.h + 1),
      toReal (Zonotope.linCombG addDown subDown Z₁ Z₂ i j)
          ≤ Zonotope.aux_linCombGReal Z₁ Z₂ i j
        ∧ Zonotope.aux_linCombGReal Z₁ Z₂ i j
          ≤ toReal (Zonotope.linCombG addUp subUp Z₁ Z₂ i j) := by -- --- PROOF ---
  simp only [Zonotope.linCombG, Zonotope.aux_linCombGReal]
  refine Fin.addCases ?_ ?_
  · refine Fin.addCases ?_ ?_
    · intro k
      simp only [Fin.append_left]
      exact Zonotope.pairSum_bracket (fun j => Z₁.G j i) (fun j => Z₂.G j i) k
    · intro k
      simp only [Fin.append_left, Fin.append_right]
      exact Zonotope.pairDiff_bracket (fun j => Z₁.G j i) (fun j => Z₂.G j i) k
  · intro _
    simp only [Fin.append_right]
    rw [toReal_half, toReal_half]
    exact ⟨by have := subDown_le_sub (Z₁.c i) (Z₂.c i); linarith,
           by have := sub_le_subUp (Z₁.c i) (Z₂.c i); linarith⟩

/-- What the stored generators are wrong by, entrywise, which is what
`linCombGDiff` records. -/
theorem Zonotope.aux_linCombG_error (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) (i : Fin n)
    (j : Fin (Z₁.h + Z₂.h + 1)) : -- --- STMT ---
    |Zonotope.aux_linCombGReal Z₁ Z₂ i j
        - toReal (Zonotope.linCombG addDown subDown Z₁ Z₂ i j)|
      ≤ toReal (Zonotope.linCombGDiff Z₁ Z₂ i j) := by -- --- PROOF ---
  obtain ⟨hlo, hhi⟩ := Zonotope.aux_linCombG_bracket Z₁ Z₂ i j
  have hgap := sub_le_subUp (Zonotope.linCombG addUp subUp Z₁ Z₂ i j)
    (Zonotope.linCombG addDown subDown Z₁ Z₂ i j)
  simp only [Zonotope.linCombGDiff]
  rw [abs_le]
  constructor <;> linarith

/-- One row of the exact generators against the coefficients the segment
supplies: the paired blocks give back the two sets' own sums, and the center
generator carries what is left. -/
theorem Zonotope.aux_linComb_row (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) (i : Fin n)
    (β₁ : Fin Z₁.h → ℝ) (β₂ : Fin Z₂.h → ℝ) (lam : ℝ) : -- --- STMT ---
    (∑ j, Zonotope.aux_linCombGReal Z₁ Z₂ i j
        * Fin.append (Fin.append (Real.Zonotope.pairCoeffSum β₁ β₂ lam)
            (Real.Zonotope.pairCoeffDiff β₁ β₂ lam)) (fun _ : Fin 1 => 2 * lam - 1) j)
      = lam * (∑ j, toReal (Z₁.G j i) * β₁ j)
        + (1 - lam) * (∑ j, toReal (Z₂.G j i) * β₂ j)
        + (2 * lam - 1) * ((toReal (Z₁.c i) - toReal (Z₂.c i)) / 2) := by -- --- PROOF ---
  rw [Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_one]
  simp only [Zonotope.aux_linCombGReal, Fin.append_left, Fin.append_right]
  rw [Zonotope.sum_pair_mul (fun j => toReal (Z₁.G j i)) (fun j => toReal (Z₂.G j i))
    β₁ β₂ lam]
  ring

/-- The nominal part spills only by what the center and the generators
rounded. -/
theorem Zonotope.aux_linComb_nominal (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) : -- --- STMT ---
    Set.linComb (nominalSet Z₁) (nominalSet Z₂) ⊆
      nominalSet (Z₁.linComb Z₂)
        + ((Zonotope.midpointResidual Z₁.c Z₂.c).construct
            + (Zonotope.generatorError
              (Zonotope.linCombGDiff Z₁ Z₂)).construct) := by -- --- PROOF ---
  rintro _ ⟨y₁, hy₁', y₂, hy₂', lam, ⟨hl0, hl1⟩, rfl⟩
  obtain ⟨β₁, hβ₁, hy₁⟩ := Zonotope.mem_nominalSet_iff.mp hy₁'
  obtain ⟨β₂, hβ₂, hy₂⟩ := Zonotope.mem_nominalSet_iff.mp hy₂'
  have hβ : ∀ j : Fin (Z₁.h + Z₂.h + 1),
      |Fin.append (Fin.append (Real.Zonotope.pairCoeffSum β₁ β₂ lam)
        (Real.Zonotope.pairCoeffDiff β₁ β₂ lam)) (fun _ : Fin 1 => 2 * lam - 1) j| ≤ 1 := by
    -- every appended coefficient is admissible, the fresh one because `2λ-1` is in `[-1,1]`
    refine Fin.addCases ?_ ?_
    · refine Fin.addCases ?_ ?_
      · intro j
        simpa using Real.Zonotope.abs_pairCoeffSum_le_one hβ₁ hβ₂ hl0 hl1 j
      · intro j
        simpa using Real.Zonotope.abs_pairCoeffDiff_le_one hβ₁ hβ₂ hl0 hl1 j
    · intro _
      simp only [Fin.append_right]
      rw [abs_le]
      constructor <;> linarith
  -- the witness: the stored midpoint and generators at that coefficient
  refine ⟨fun i => toReal (Zonotope.midpoint Z₁.c Z₂.c i)
            + ∑ j : Fin (Z₁.h + Z₂.h + 1),
                toReal (Zonotope.linCombG addDown subDown Z₁ Z₂ i j)
                  * Fin.append (Fin.append (Real.Zonotope.pairCoeffSum β₁ β₂ lam)
                      (Real.Zonotope.pairCoeffDiff β₁ β₂ lam))
                      (fun _ : Fin 1 => 2 * lam - 1) j,
          Zonotope.mem_nominalSet_iff.mpr ⟨_, hβ, fun _ => rfl⟩,
          _,
          ⟨_, Zonotope.midpoint_mem_residual Z₁.c Z₂.c,
           _, Zonotope.mem_generatorError
                 (fun i j => Zonotope.aux_linCombG_error Z₁ Z₂ i j) hβ, rfl⟩, ?_⟩
  funext i
  -- the stored generators and their shortfalls recombine into the exact ones
  have hsum : (∑ j : Fin (Z₁.h + Z₂.h + 1),
        toReal (Zonotope.linCombG addDown subDown Z₁ Z₂ i j)
          * Fin.append (Fin.append (Real.Zonotope.pairCoeffSum β₁ β₂ lam)
              (Real.Zonotope.pairCoeffDiff β₁ β₂ lam)) (fun _ : Fin 1 => 2 * lam - 1) j)
      + (∑ j, (Zonotope.aux_linCombGReal Z₁ Z₂ i j
            - toReal (Zonotope.linCombG addDown subDown Z₁ Z₂ i j))
          * Fin.append (Fin.append (Real.Zonotope.pairCoeffSum β₁ β₂ lam)
              (Real.Zonotope.pairCoeffDiff β₁ β₂ lam)) (fun _ : Fin 1 => 2 * lam - 1) j)
      = ∑ j, Zonotope.aux_linCombGReal Z₁ Z₂ i j
          * Fin.append (Fin.append (Real.Zonotope.pairCoeffSum β₁ β₂ lam)
              (Real.Zonotope.pairCoeffDiff β₁ β₂ lam)) (fun _ : Fin 1 => 2 * lam - 1) j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hy₁ i, hy₂ i]
  rw [Zonotope.aux_linComb_row Z₁ Z₂ i β₁ β₂ lam] at hsum
  linarith [hsum]

/-- The box absorbs the two incoming boxes, the center rounding and the
generator roundings. -/
theorem Zonotope.aux_linComb_error (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) :
    Set.linComb Z₁.I_error.construct Z₂.I_error.construct
        + ((Zonotope.midpointResidual Z₁.c Z₂.c).construct
            + (Zonotope.generatorError (Zonotope.linCombGDiff Z₁ Z₂)).construct)
      ⊆ (Z₁.linComb Z₂).I_error.construct :=
  subset_trans
    (Set.add_subset_add (Interval.linComb_outer Z₁.I_error Z₂.I_error) (Interval.plus_outer _ _))
    (Interval.plus_outer _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.linComb_outer (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) :
    Set.linComb Z₁.construct Z₂.construct ⊆ (Z₁.linComb Z₂).construct :=
  InflatedContSet.linComb_subset (Zonotope.aux_linComb_nominal Z₁ Z₂)
    (Zonotope.aux_linComb_error Z₁ Z₂)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
