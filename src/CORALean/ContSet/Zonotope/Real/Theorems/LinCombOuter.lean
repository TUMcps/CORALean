import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.Zonotope.Real.Operations.LinComb
import CORALean.ContSet.Zonotope.Real.Theorems.Coefficient

/-!
# `linComb` contains every segment between the two zonotopes

The paired blocks carry `λ β₁ ± (1-λ) β₂`, both back in `[-1,1]` because the two
weights sum to one, and the generator spanning the half-difference of the
centres carries `2λ - 1`. Past the shorter block a surplus generator carries its
own weighted coefficient alone.

The pairing is what the proof has to work for: it couples column `j` of one
block with column `j` of the other, so neither block sum closes on its own. Both
are read over the common range `h₁ + h₂` with the summand padded by zero, where
the identity is pointwise — a column both sets have, a column only one has, or
neither.

`pairCoeffSum` and `pairCoeffDiff` are proof devices and are never run; they
also serve the float layer and `PolyZonotope.linComb`'s independent block.

Nothing here asks for convexity: the claim is about the segments themselves, so
it is the statement a non-convex representation could also make.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   03-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {h₁ h₂ : ℕ}

/-- The coefficient the paired-sum generator carries: the two weighted
coefficients added, which is what records that they share one `λ`. -/
def Zonotope.pairCoeffSum (β₁ : Fin h₁ → ℝ) (β₂ : Fin h₂ → ℝ) (lam : ℝ) (j : Fin h₁) : ℝ :=
  if hj : (j : ℕ) < h₂ then lam * β₁ j + (1 - lam) * β₂ ⟨j, hj⟩ else lam * β₁ j

/-- The coefficient the paired-difference generator carries. -/
def Zonotope.pairCoeffDiff (β₁ : Fin h₁ → ℝ) (β₂ : Fin h₂ → ℝ) (lam : ℝ) (j : Fin h₂) : ℝ :=
  if hj : (j : ℕ) < h₁ then lam * β₁ ⟨j, hj⟩ - (1 - lam) * β₂ j else (1 - lam) * β₂ j

/-- A weighted coefficient reaches no further than its weight. -/
theorem Zonotope.abs_weighted_le {b w : ℝ} (hw : 0 ≤ w) (hb : |b| ≤ 1) : |w * b| ≤ w := by
  rw [abs_mul, abs_of_nonneg hw]
  exact mul_le_of_le_one_right hw hb

theorem Zonotope.abs_pairCoeffSum_le_one {β₁ : Fin h₁ → ℝ} {β₂ : Fin h₂ → ℝ} {lam : ℝ}
    (hβ₁ : ∀ j, |β₁ j| ≤ 1) (hβ₂ : ∀ j, |β₂ j| ≤ 1) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1)
    (j : Fin h₁) : |Zonotope.pairCoeffSum β₁ β₂ lam j| ≤ 1 := by
  simp only [Zonotope.pairCoeffSum]
  by_cases hj : (j : ℕ) < h₂
  · rw [dif_pos hj]
    have hA := Zonotope.abs_weighted_le hl0 (hβ₁ j)
    have hB := Zonotope.abs_weighted_le (by linarith : (0:ℝ) ≤ 1 - lam) (hβ₂ ⟨j, hj⟩)
    rw [abs_le] at hA hB ⊢
    constructor <;> linarith
  · rw [dif_neg hj]
    exact le_trans (Zonotope.abs_weighted_le hl0 (hβ₁ j)) hl1

-- the difference coefficient, the mirror of the sum one
theorem Zonotope.abs_pairCoeffDiff_le_one {β₁ : Fin h₁ → ℝ} {β₂ : Fin h₂ → ℝ} {lam : ℝ}
    (hβ₁ : ∀ j, |β₁ j| ≤ 1) (hβ₂ : ∀ j, |β₂ j| ≤ 1) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1)
    (j : Fin h₂) : |Zonotope.pairCoeffDiff β₁ β₂ lam j| ≤ 1 := by
  simp only [Zonotope.pairCoeffDiff]
  by_cases hj : (j : ℕ) < h₁
  · rw [dif_pos hj]
    have hA := Zonotope.abs_weighted_le hl0 (hβ₁ ⟨j, hj⟩)
    have hB := Zonotope.abs_weighted_le (by linarith : (0:ℝ) ≤ 1 - lam) (hβ₂ j)
    rw [abs_le] at hA hB ⊢
    constructor <;> linarith
  · rw [dif_neg hj]
    exact le_trans (Zonotope.abs_weighted_le (by linarith : (0:ℝ) ≤ 1 - lam) (hβ₂ j))
      (by linarith)

omit [Module ℝ α] in
/-- A block sum read over a longer range, the summand padded with zero. What
lets the two paired blocks meet: neither closes on its own, and over a common
range the identity is pointwise. -/
theorem Zonotope.aux_sum_pad {k N : ℕ} (hk : k ≤ N) (f : Fin k → α) :
    ∑ j, f j = ∑ i ∈ Finset.range N, (if h : i < k then f ⟨i, h⟩ else 0) := by
  have hfin : ∑ j, f j
      = ∑ i ∈ Finset.range k, (if h : i < k then f ⟨i, h⟩ else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => if h : i < k then f ⟨i, h⟩ else 0) k]
    exact Finset.sum_congr rfl fun j _ => by rw [dif_pos j.isLt]
  rw [hfin]
  refine Finset.sum_subset
    (fun i hi => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hk))
    fun i _ hi => dif_neg (by simpa using hi)

/-- A weight pulled out of a block sum: `module` cannot do this for itself, a
sum being one atom to it. -/
theorem Zonotope.aux_sum_weighted {k : ℕ} (w : ℝ) (b : Fin k → ℝ) (g : Fin k → α) :
    ∑ j, (w * b j) • g j = w • ∑ j, b j • g j := by
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => (smul_smul w (b j) (g j)).symm

/-- The paired blocks recombine into the two original ones. Over a column both
sets have, the sum and the difference generator carry `λβ₁` and `(1-λ)β₂`
between them; past the shorter block each surplus generator carries its own. -/
theorem Zonotope.sum_pair (G₁ : Fin h₁ → α) (G₂ : Fin h₂ → α)
    (β₁ : Fin h₁ → ℝ) (β₂ : Fin h₂ → ℝ) (lam : ℝ) :
    (∑ j, Zonotope.pairCoeffSum β₁ β₂ lam j • Zonotope.pairSum G₁ G₂ j)
        + ∑ j, Zonotope.pairCoeffDiff β₁ β₂ lam j • Zonotope.pairDiff G₁ G₂ j
      = lam • (∑ j, β₁ j • G₁ j) + (1 - lam) • ∑ j, β₂ j • G₂ j := by
  rw [← Zonotope.aux_sum_weighted lam β₁ G₁, ← Zonotope.aux_sum_weighted (1 - lam) β₂ G₂,
    Zonotope.aux_sum_pad (Nat.le_add_right h₁ h₂)
      (fun j => Zonotope.pairCoeffSum β₁ β₂ lam j • Zonotope.pairSum G₁ G₂ j),
    Zonotope.aux_sum_pad (Nat.le_add_left h₂ h₁)
      (fun j => Zonotope.pairCoeffDiff β₁ β₂ lam j • Zonotope.pairDiff G₁ G₂ j),
    Zonotope.aux_sum_pad (Nat.le_add_right h₁ h₂) (fun j => (lam * β₁ j) • G₁ j),
    Zonotope.aux_sum_pad (Nat.le_add_left h₂ h₁) (fun j => ((1 - lam) * β₂ j) • G₂ j),
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Zonotope.pairCoeffSum, Zonotope.pairSum, Zonotope.pairCoeffDiff,
    Zonotope.pairDiff]
  split_ifs <;> module

/-- `Fin.sum_univ_add` at this operation's generator count, stated through the
projection because that is the form the goal has and simp will not rewrite a
binder's type. -/
theorem Zonotope.aux_sum_univ_linComb {Z₁ Z₂ : Zonotope α}
    (f : Fin (Z₁.h + Z₂.h + 1) → α) :
    ∑ j : Fin (Z₁.linComb Z₂).h, f j
      = ∑ j, f (Fin.castAdd 1 j) + ∑ j, f (Fin.natAdd (Z₁.h + Z₂.h) j) :=
  Fin.sum_univ_add f

-- the closing `module` call normalises a sum over the doubly appended generator index
set_option maxHeartbeats 400000 in
theorem Zonotope.linComb_outer (Z₁ Z₂ : Zonotope α) :
    segments Z₁.construct Z₂.construct ⊆ (Z₁.linComb Z₂).construct := by
  rintro x ⟨y₁, ⟨β₁, hβ₁, rfl⟩, y₂, ⟨β₂, hβ₂, rfl⟩, lam, ⟨hl0, hl1⟩, rfl⟩
  refine ⟨Fin.append (Fin.append (Zonotope.pairCoeffSum β₁ β₂ lam)
      (Zonotope.pairCoeffDiff β₁ β₂ lam)) (fun _ : Fin 1 => 2 * lam - 1), ?_, ?_⟩
  · refine Fin.addCases ?_ ?_
    · refine Fin.addCases ?_ ?_
      · intro j
        simpa using Zonotope.abs_pairCoeffSum_le_one hβ₁ hβ₂ hl0 hl1 j
      · intro j
        simpa using Zonotope.abs_pairCoeffDiff_le_one hβ₁ hβ₂ hl0 hl1 j
    · intro _
      simp only [Fin.append_right]
      rw [abs_le]
      constructor <;> linarith
  · rw [Zonotope.aux_sum_univ_linComb, Fin.sum_univ_add]
    simp only [Zonotope.linComb, Fin.append_left, Fin.append_right, Fin.sum_univ_one]
    rw [Zonotope.sum_pair Z₁.G Z₂.G β₁ β₂ lam]
    -- what is left is the centres, which the fresh generator carries
    module

end CORALean.Real
