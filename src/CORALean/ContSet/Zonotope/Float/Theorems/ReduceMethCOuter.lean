module

public import CORALean.ContSet.Zonotope.Float.Operations.ReduceMethC
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError
public import CORALean.ContSet.Zonotope.Float.Theorems.MethCQBound
public import CORALean.ContSet.Zonotope.Float.Theorems.MethCReachBound
public import CORALean.ContSet.Zonotope.Real.Theorems.BasisReach
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter

@[expose] public section

/-!
# `Zonotope.reduceMethC` over-approximates the zonotope

Where the check passes, `Zonotope.basis_reach` places every point `G β` of the zonotope in the
chosen basis, at coordinates of magnitude at most `2 methCReach`, which `ρ` rounds up. Those
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


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.reduceMethC_outer (Z : Zonotope (Vec 𝕋 n)) (o : ℕ) :
    Z.construct ⊆ (Z.reduceMethC o).construct := by -- --- PROOF ---
  by_cases hlt : o * n < Z.h
  swap
  · simp only [Zonotope.reduceMethC, if_neg hlt]
    exact subset_rfl
  by_cases hq : le (Zonotope.methCQ (Zonotope.basisInverse Z.methCBasis) Z.methCBasis)
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
  have hqle : toReal (Zonotope.methCQ H P) ≤ 1 / 2 := by
    have := toReal_le_of_le hq
    rwa [toReal_half, toReal_one] at this
  -- the coordinates of the point's offset in the basis
  obtain ⟨w, hw, hwb⟩ := Real.Zonotope.basis_reach (toRealMat P) (toRealMat H) hqle
    (fun i => Zonotope.methCQ_bound H P i) (fun l => ∑ j, toReal (Z.G j l) * β j)
    (fun i => Zonotope.methCReach_bound H (fun i j => Z.G j i) hβ i)
  set ρ := addUp (Zonotope.methCReach H (fun i j => Z.G j i))
    (Zonotope.methCReach H (fun i j => Z.G j i)) with hρ
  have hρge : ∀ k, |w k| ≤ toReal ρ := fun k => by
    have := add_le_addUp (Zonotope.methCReach H (fun i j => Z.G j i))
      (Zonotope.methCReach H (fun i j => Z.G j i))
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
