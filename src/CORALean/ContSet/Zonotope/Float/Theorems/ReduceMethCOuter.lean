module

public import CORALean.ContSet.Zonotope.Float.Operations.ReduceMethC
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError
public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.ContSet.Zonotope.Real.Theorems.BasisReach
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter

@[expose] public section

/-!
# `Zonotope.reduceMethC` over-approximates the zonotope

Where the check passes, `Zonotope.basis_reach` places every point `G β` of the zonotope in the
chosen basis, at coordinates of magnitude at most `2 step_methCReach`, which `ρ` rounds up. Those
coordinates over `ρ` are coefficients in `[-1,1]` of the generators `ρ P`, and the stored
generators, being rounded down, fall short of them by what `generatorError` holds. Where the check
fails, or the order is already low, the zonotope is returned and there is nothing to show.

Outer, never exact: the parallelotope contains the zonotope.

## Inputs
* `Z` – zonotope
* `o` – target order

## Hypotheses
* none

## Conclusion
* zonotope is contained in its parallelotope reduction
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n h : ℕ}

/-- `step_methCResidual` bounds `|1 - H P|`. -/
private theorem Zonotope.aux_methCResidual_bound (H P : Mat 𝕋 n n) (i j : Fin n) : -- --- CONCL ---
    |(1 - toRealMat H * toRealMat P) i j|
      ≤ toReal (Zonotope.step_methCResidual H P i j) := by -- --- PROOF ---
  -- the entry of the product, between its two directed dot products
  have hd := dotDown_le (H i) fun l => P l j
  have hu := le_dotUp (H i) fun l => P l j
  have hprod : (toRealMat H * toRealMat P) i j
      = ∑ l, toReal (H i l) * toReal (P l j) := rfl
  have hδ : toReal (if i = j then (one : 𝕋) else zero) = if i = j then (1 : ℝ) else 0 := by
    split_ifs
    · exact toReal_one
    · exact toReal_zero
  have hsub : (1 - toRealMat H * toRealMat P) i j
      = (if i = j then (1 : ℝ) else 0) - ∑ l, toReal (H i l) * toReal (P l j) := by
    rw [Matrix.sub_apply, hprod, Matrix.one_apply]
  have h1 := subDown_le_sub (if i = j then (one : 𝕋) else zero) (dotUp (H i) fun l => P l j)
  have h2 := sub_le_subUp (if i = j then (one : 𝕋) else zero) (dotDown (H i) fun l => P l j)
  rw [hδ] at h1 h2
  rw [hsub]
  simp only [Zonotope.step_methCResidual, toReal_maximum, toReal_absolute]
  exact abs_le_max_abs_abs (by linarith) (by linarith)


/-- `step_methCQ` bounds every absolute row sum of `1 - H P`. -/
private theorem Zonotope.aux_methCQ_bound (H P : Mat 𝕋 n n) (i : Fin n) :
    ∑ j, |(1 - toRealMat H * toRealMat P) i j|
      ≤ toReal (Zonotope.step_methCQ H P) := by
  refine le_trans (Finset.sum_le_sum fun j _ => Zonotope.aux_methCResidual_bound H P i j) ?_
  refine le_trans (sum_le_sumUp fun j => Zonotope.step_methCResidual H P i j) ?_
  exact le_maximumOver (fun i => sumUp fun j => Zonotope.step_methCResidual H P i j) i

end


section
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n h : ℕ}

/-- `step_methCReach` bounds `H G β`. -/
private theorem Zonotope.aux_methCReach_bound (H : Mat 𝕋 n n) (G : Mat 𝕋 n h) {β : Vec ℝ h}
    (hβ : ∀ j, |β j| ≤ 1) (i : Fin n) : -- --- CONCL ---
    |(toRealMat H *ᵥ fun l => ∑ j, toReal (G l j) * β j) i|
      ≤ toReal (Zonotope.step_methCReach H G) := by -- --- PROOF ---
  -- the product, regrouped by generator
  have hre : (toRealMat H *ᵥ fun l => ∑ j, toReal (G l j) * β j) i
      = ∑ j, (∑ l, toReal (H i l) * toReal (G l j)) * β j := by
    simp only [Matrix.mulVec, dotProduct, toRealMat, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  rw [hre]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun j _ => ?_)
    (le_trans (sum_le_sumUp fun j => maximum (absolute (dotDown (H i) fun l => G l j))
      (absolute (dotUp (H i) fun l => G l j)))
    (le_maximumOver (fun i => sumUp fun j => maximum (absolute (dotDown (H i) fun l => G l j))
      (absolute (dotUp (H i) fun l => G l j))) i))
  -- the entry of `H G` between its two roundings, times a coefficient of magnitude at most one
  have hd := dotDown_le (H i) fun l => G l j
  have hu := le_dotUp (H i) fun l => G l j
  rw [abs_mul]
  refine le_trans (mul_le_of_le_one_right (abs_nonneg _) (hβ j)) ?_
  rw [toReal_maximum, toReal_absolute, toReal_absolute]
  exact abs_le_max_abs_abs hd hu

end


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.reduceMethC_outer (Z : Zonotope (Vec 𝕋 n)) (o : ℕ) : -- --- CONCL ---
    Z.construct ⊆ (Z.reduceMethC o).construct := by -- --- PROOF ---
  by_cases hlt : o * n < Z.h
  swap
  · simp only [Zonotope.reduceMethC, if_neg hlt]
    exact subset_rfl
  by_cases hq : le (Zonotope.step_methCQ (Zonotope.basisInverse Z.methCBasis) Z.methCBasis)
      (half one) = true
  swap
  · simp only [Zonotope.reduceMethC, if_pos hlt, hq]
    exact subset_rfl
  simp only [Zonotope.reduceMethC, if_pos hlt, hq, if_true]
  rintro _ ⟨z, hz, e, he, rfl⟩
  obtain ⟨β, hβ, hzi⟩ := Zonotope.mem_nominalSet_iff.mp hz
  -- the basis, its candidate inverse, and what the check certifies
  set P := Z.methCBasis with hP
  set H := Zonotope.basisInverse P with hH
  have hqle : toReal (Zonotope.step_methCQ H P) ≤ 1 / 2 := by
    have := toReal_le_of_le hq
    rwa [toReal_half, toReal_one] at this
  -- the coordinates of the point's offset in the basis
  obtain ⟨w, hw, hwb⟩ := Real.Zonotope.basis_reach (toRealMat P) (toRealMat H) hqle
    (fun i => Zonotope.aux_methCQ_bound H P i) (fun l => ∑ j, toReal (Z.G j l) * β j)
    (fun i => Zonotope.aux_methCReach_bound H (fun i j => Z.G j i) hβ i)
  set ρ := addUp (Zonotope.step_methCReach H (fun i j => Z.G j i))
    (Zonotope.step_methCReach H (fun i j => Z.G j i)) with hρ
  have hρge : ∀ k, |w k| ≤ toReal ρ := fun k => by
    have := add_le_addUp (Zonotope.step_methCReach H (fun i j => Z.G j i))
      (Zonotope.step_methCReach H (fun i j => Z.G j i))
    linarith [hwb k]
  -- the same coordinates as coefficients over `ρ`
  set β' : Fin n → ℝ := fun k => if toReal ρ = 0 then 0 else w k / toReal ρ with hβ'
  have hβ'le : ∀ k, |β' k| ≤ 1 := fun k => by
    simp only [hβ']
    split_ifs with h0
    · simp
    · have hpos : 0 < toReal ρ := lt_of_le_of_ne (le_trans (abs_nonneg _) (hρge k)) (Ne.symm h0)
      rw [abs_div, abs_of_pos hpos, div_le_one hpos]
      exact hρge k
  have hwβ : ∀ k, w k = toReal ρ * β' k := fun k => by
    simp only [hβ']
    split_ifs with h0
    · have := hρge k
      rw [h0] at this
      simpa using abs_nonpos_iff.mp this
    · field_simp
  -- the stored zonotope's nominal point at `β'`, and what it falls short by
  have hshort : (fun i => ∑ k, (toReal ρ * toReal (P i k)
        - toReal (mulDown ρ (P i k))) * β' k)
      ∈ (Zonotope.generatorError fun i k =>
        subUp (mulUp ρ (P i k)) (mulDown ρ (P i k))).construct := by
    refine Zonotope.mem_generatorError (fun i k => ?_) hβ'le
    have h1 := mulDown_le_mul ρ (P i k)
    have h2 := mul_le_mulUp ρ (P i k)
    have h3 := sub_le_subUp (mulUp ρ (P i k)) (mulDown ρ (P i k))
    rw [abs_le]
    constructor <;> linarith
  refine ⟨_, Zonotope.mem_nominalSet_iff.mpr ⟨β', hβ'le, fun _ => rfl⟩, e + _,
    Interval.plus_outer _ _ ⟨e, he, _, hshort, rfl⟩, ?_⟩
  funext i
  -- the offset `G β` is `P w`, read at coordinate `i`
  have hPw : ∑ k, toReal (P i k) * w k = ∑ j, toReal (Z.G j i) * β j := by
    have := congrFun hw i
    simpa [Matrix.mulVec, dotProduct, toRealMat] using this
  have hsplit : ∑ k, (toReal ρ * toReal (P i k) - toReal (mulDown ρ (P i k))) * β' k
      = ∑ k, toReal (P i k) * w k - ∑ k, toReal (mulDown ρ (P i k)) * β' k := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [hwβ k]; ring
  show toReal (Z.c i) + ∑ k, toReal (mulDown ρ (P i k)) * β' k
      + (e i + ∑ k, (toReal ρ * toReal (P i k) - toReal (mulDown ρ (P i k))) * β' k)
    = z i + e i
  rw [hsplit, hPw, hzi i]
  ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
