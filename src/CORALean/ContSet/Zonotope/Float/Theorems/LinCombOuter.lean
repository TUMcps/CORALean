import CORALean.ContSet.InflatedContSet.Theorems.LinCombSubset
import CORALean.ContSet.Interval.Float.Theorems.LinCombOuter
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
import CORALean.ContSet.Zonotope.Float.Operations.LinComb
import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError
import CORALean.ContSet.Zonotope.Real.Theorems.LinCombOuter

/-!
# `Zonotope.linComb` contains every segment between the two zonotopes

`InflatedContSet.linComb_subset` reduces this to two obligations: the nominal
part spills only by what rounded, and the box absorbs that spill along with the
segment between the two incoming boxes.

The nominal obligation is the exact `linComb` argument at the same coefficients
— `pairCoeffSum`, `pairCoeffDiff` and `2λ-1` — with every stored value displaced
from the one ℝ would have. Nothing stored is unfolded: the centre cancels
against its own residual and the generators against `linCombGDiff`, leaving the
identity the exact proof closes with, which `Zonotope.sum_pair` supplies.

The count is therefore still `h₁ + h₂ + 1`, every rounding having gone into the
box.
-/

-- Authors:       Tobias Ladner
-- Written:       19-August-2026
-- Last update:   03-September-2026
-- Last revision: ---

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n h₁ h₂ : ℕ}

omit [SoundFloatArithmetic 𝕋] in
@[simp] theorem Zonotope.linComb_h (Z₁ Z₂ : Zonotope 𝕋 n) :
    (Z₁.linComb Z₂).h = Z₁.h + Z₂.h + 1 := rfl

/-- The generator row `linComb` would store if nothing rounded: the exact
pairing over the real values the stored floats denote. -/
noncomputable def Zonotope.linCombGReal (Z₁ Z₂ : Zonotope 𝕋 n) (i : Fin n) :
    Fin (Z₁.h + Z₂.h + 1) → ℝ :=
  Fin.append
    (Fin.append
      (Real.Zonotope.pairSum (fun j => toReal (Z₁.G i j)) (fun j => toReal (Z₂.G i j)))
      (Real.Zonotope.pairDiff (fun j => toReal (Z₁.G i j)) (fun j => toReal (Z₂.G i j))))
    (fun _ : Fin 1 => (toReal (Z₁.c i) - toReal (Z₂.c i)) / 2)

/-- The two directed midpoints bracket the exact one, halving being exact. -/
theorem Zonotope.aux_midpoint_mem_residual (a b : Vec 𝕋 n) :
    (fun i => (toReal (a i) + toReal (b i)) / 2 - toReal (Zonotope.midpoint a b i))
      ∈ (Zonotope.midpointResidual a b).construct :=
  Interval.sub_mem_residual fun i => by
    refine ⟨?_, ?_⟩
    · rw [toReal_half]
      have := addDown_le_add (a i) (b i)
      linarith
    · rw [toReal_half]
      have := add_le_addUp (a i) (b i)
      linarith

/-- A paired-sum column brackets its exact value between the two directed
roundings: halving is exact, so the directed addition is the only rounding, and
a surplus column is copied and does not round at all. -/
theorem Zonotope.pairSum_bracket (g₁ : Fin h₁ → 𝕋) (g₂ : Fin h₂ → 𝕋) (k : Fin h₁) :
    toReal (Zonotope.pairSum addDown g₁ g₂ k)
        ≤ Real.Zonotope.pairSum (fun j => toReal (g₁ j)) (fun j => toReal (g₂ j)) k
      ∧ Real.Zonotope.pairSum (fun j => toReal (g₁ j)) (fun j => toReal (g₂ j)) k
        ≤ toReal (Zonotope.pairSum addUp g₁ g₂ k) := by
  simp only [Zonotope.pairSum, Real.Zonotope.pairSum]
  by_cases hk : (k : ℕ) < h₂
  · rw [dif_pos hk, dif_pos hk, dif_pos hk, toReal_half, toReal_half, smul_eq_mul]
    exact ⟨by have := addDown_le_add (g₁ k) (g₂ ⟨k, hk⟩); linarith,
           by have := add_le_addUp (g₁ k) (g₂ ⟨k, hk⟩); linarith⟩
  · rw [dif_neg hk, dif_neg hk, dif_neg hk]
    exact ⟨le_refl _, le_refl _⟩

/-- The same at the paired-difference column. -/
theorem Zonotope.pairDiff_bracket (g₁ : Fin h₁ → 𝕋) (g₂ : Fin h₂ → 𝕋) (k : Fin h₂) :
    toReal (Zonotope.pairDiff subDown g₁ g₂ k)
        ≤ Real.Zonotope.pairDiff (fun j => toReal (g₁ j)) (fun j => toReal (g₂ j)) k
      ∧ Real.Zonotope.pairDiff (fun j => toReal (g₁ j)) (fun j => toReal (g₂ j)) k
        ≤ toReal (Zonotope.pairDiff subUp g₁ g₂ k) := by
  simp only [Zonotope.pairDiff, Real.Zonotope.pairDiff]
  by_cases hk : (k : ℕ) < h₁
  · rw [dif_pos hk, dif_pos hk, dif_pos hk, toReal_half, toReal_half, smul_eq_mul]
    exact ⟨by have := subDown_le_sub (g₁ ⟨k, hk⟩) (g₂ k); linarith,
           by have := sub_le_subUp (g₁ ⟨k, hk⟩) (g₂ k); linarith⟩
  · rw [dif_neg hk, dif_neg hk, dif_neg hk]
    exact ⟨le_refl _, le_refl _⟩

/-- Every stored generator sits at the low end of a bracket around its exact
value: the two blocks pair, and the centre generator is one directed
difference. -/
theorem Zonotope.aux_linCombG_bracket (Z₁ Z₂ : Zonotope 𝕋 n) (i : Fin n) :
    ∀ j : Fin (Z₁.h + Z₂.h + 1),
      toReal (Zonotope.linCombG addDown subDown Z₁ Z₂ i j)
          ≤ Zonotope.linCombGReal Z₁ Z₂ i j
        ∧ Zonotope.linCombGReal Z₁ Z₂ i j
          ≤ toReal (Zonotope.linCombG addUp subUp Z₁ Z₂ i j) := by
  simp only [Zonotope.linCombG, Zonotope.linCombGReal]
  refine Fin.addCases ?_ ?_
  · refine Fin.addCases ?_ ?_
    · intro k
      simp only [Fin.append_left]
      exact Zonotope.pairSum_bracket (Z₁.G i) (Z₂.G i) k
    · intro k
      simp only [Fin.append_left, Fin.append_right]
      exact Zonotope.pairDiff_bracket (Z₁.G i) (Z₂.G i) k
  · intro _
    simp only [Fin.append_right]
    rw [toReal_half, toReal_half]
    exact ⟨by have := subDown_le_sub (Z₁.c i) (Z₂.c i); linarith,
           by have := sub_le_subUp (Z₁.c i) (Z₂.c i); linarith⟩

/-- What the stored generators are wrong by, entrywise, which is what
`linCombGDiff` records. -/
theorem Zonotope.aux_linCombG_error (Z₁ Z₂ : Zonotope 𝕋 n) (i : Fin n)
    (j : Fin (Z₁.h + Z₂.h + 1)) :
    |Zonotope.linCombGReal Z₁ Z₂ i j
        - toReal (Zonotope.linCombG addDown subDown Z₁ Z₂ i j)|
      ≤ toReal (Zonotope.linCombGDiff Z₁ Z₂ i j) := by
  obtain ⟨hlo, hhi⟩ := Zonotope.aux_linCombG_bracket Z₁ Z₂ i j
  have hgap := sub_le_subUp (Zonotope.linCombG addUp subUp Z₁ Z₂ i j)
    (Zonotope.linCombG addDown subDown Z₁ Z₂ i j)
  simp only [Zonotope.linCombGDiff]
  rw [abs_le]
  constructor <;> linarith

/-- `Zonotope.sum_pair` where the coefficient follows the generator, which is
the order a stored row is read in. -/
theorem Zonotope.sum_pair_mul (g₁ : Fin h₁ → ℝ) (g₂ : Fin h₂ → ℝ)
    (β₁ : Fin h₁ → ℝ) (β₂ : Fin h₂ → ℝ) (lam : ℝ) :
    (∑ j, Real.Zonotope.pairSum g₁ g₂ j * Real.Zonotope.pairCoeffSum β₁ β₂ lam j)
        + ∑ j, Real.Zonotope.pairDiff g₁ g₂ j * Real.Zonotope.pairCoeffDiff β₁ β₂ lam j
      = lam * (∑ j, g₁ j * β₁ j) + (1 - lam) * ∑ j, g₂ j * β₂ j := by
  have key := Real.Zonotope.sum_pair g₁ g₂ β₁ β₂ lam
  simp only [smul_eq_mul] at key
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) =>
        mul_comm (Real.Zonotope.pairSum g₁ g₂ j) (Real.Zonotope.pairCoeffSum β₁ β₂ lam j)),
    Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) =>
      mul_comm (Real.Zonotope.pairDiff g₁ g₂ j) (Real.Zonotope.pairCoeffDiff β₁ β₂ lam j)),
    key, Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => mul_comm (g₁ j) (β₁ j)),
    Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => mul_comm (g₂ j) (β₂ j))]

/-- One row of the exact generators against the coefficients the segment
supplies: the paired blocks give back the two sets' own sums, and the centre
generator carries what is left. -/
theorem Zonotope.aux_linComb_row (Z₁ Z₂ : Zonotope 𝕋 n) (i : Fin n)
    (β₁ : Fin Z₁.h → ℝ) (β₂ : Fin Z₂.h → ℝ) (lam : ℝ) :
    (∑ j, Zonotope.linCombGReal Z₁ Z₂ i j
        * Fin.append (Fin.append (Real.Zonotope.pairCoeffSum β₁ β₂ lam)
            (Real.Zonotope.pairCoeffDiff β₁ β₂ lam)) (fun _ : Fin 1 => 2 * lam - 1) j)
      = lam * (∑ j, toReal (Z₁.G i j) * β₁ j)
        + (1 - lam) * (∑ j, toReal (Z₂.G i j) * β₂ j)
        + (2 * lam - 1) * ((toReal (Z₁.c i) - toReal (Z₂.c i)) / 2) := by
  rw [Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_one]
  simp only [Zonotope.linCombGReal, Fin.append_left, Fin.append_right]
  rw [Zonotope.sum_pair_mul (fun j => toReal (Z₁.G i j)) (fun j => toReal (Z₂.G i j))
    β₁ β₂ lam]
  ring

-- the doubly appended coefficient vector is re-elaborated at every `Fin.addCases` branch
set_option maxHeartbeats 400000 in
/-- The nominal part spills only by what the centre and the generators
rounded. -/
theorem Zonotope.aux_linComb_nominal (Z₁ Z₂ : Zonotope 𝕋 n) :
    segments (nominalSet Z₁) (nominalSet Z₂) ⊆
      nominalSet (Z₁.linComb Z₂)
        + ((Zonotope.midpointResidual Z₁.c Z₂.c).construct
            + (Zonotope.generatorError (Zonotope.linCombGDiff Z₁ Z₂)).construct) := by
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
          ⟨_, Zonotope.aux_midpoint_mem_residual Z₁.c Z₂.c,
           _, Zonotope.mem_generatorError
                 (fun i j => Zonotope.aux_linCombG_error Z₁ Z₂ i j) hβ, rfl⟩, ?_⟩
  funext i
  -- the stored generators and their shortfalls recombine into the exact ones
  have hsum : (∑ j : Fin (Z₁.h + Z₂.h + 1),
        toReal (Zonotope.linCombG addDown subDown Z₁ Z₂ i j)
          * Fin.append (Fin.append (Real.Zonotope.pairCoeffSum β₁ β₂ lam)
              (Real.Zonotope.pairCoeffDiff β₁ β₂ lam)) (fun _ : Fin 1 => 2 * lam - 1) j)
      + (∑ j, (Zonotope.linCombGReal Z₁ Z₂ i j
            - toReal (Zonotope.linCombG addDown subDown Z₁ Z₂ i j))
          * Fin.append (Fin.append (Real.Zonotope.pairCoeffSum β₁ β₂ lam)
              (Real.Zonotope.pairCoeffDiff β₁ β₂ lam)) (fun _ : Fin 1 => 2 * lam - 1) j)
      = ∑ j, Zonotope.linCombGReal Z₁ Z₂ i j
          * Fin.append (Fin.append (Real.Zonotope.pairCoeffSum β₁ β₂ lam)
              (Real.Zonotope.pairCoeffDiff β₁ β₂ lam)) (fun _ : Fin 1 => 2 * lam - 1) j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hy₁ i, hy₂ i]
  rw [Zonotope.aux_linComb_row Z₁ Z₂ i β₁ β₂ lam] at hsum
  linarith [hsum]

/-- The box absorbs the two incoming boxes, the centre rounding and the
generator roundings. -/
theorem Zonotope.aux_linComb_error (Z₁ Z₂ : Zonotope 𝕋 n) :
    segments Z₁.E.construct Z₂.E.construct
        + ((Zonotope.midpointResidual Z₁.c Z₂.c).construct
            + (Zonotope.generatorError (Zonotope.linCombGDiff Z₁ Z₂)).construct)
      ⊆ (Z₁.linComb Z₂).E.construct :=
  subset_trans
    (Set.add_subset_add (Interval.linComb_outer Z₁.E Z₂.E) (Interval.plus_outer _ _))
    (Interval.plus_outer _ _)

theorem Zonotope.linComb_outer (Z₁ Z₂ : Zonotope 𝕋 n) :
    segments Z₁.construct Z₂.construct ⊆ (Z₁.linComb Z₂).construct :=
  InflatedContSet.linComb_subset (Zonotope.aux_linComb_nominal Z₁ Z₂)
    (Zonotope.aux_linComb_error Z₁ Z₂)

end CORALean.Float
