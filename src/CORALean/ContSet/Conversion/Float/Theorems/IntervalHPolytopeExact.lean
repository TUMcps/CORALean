module

public import CORALean.ContSet.HPolytope.Float.Theorems.MemStackRowsNominalIff
public import CORALean.ContSet.HPolytope.Float.Operations.Ineqs
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_HPolytope
public import CORALean.ContSet.HPolytope.Float.Operations.Intersection
public import CORALean.ContSet.Conversion.Float.Theorems.NegIdentityMatMulVec
public import CORALean.ContSet.HPolytope.Float.Theorems.MemStackRowsConstructIff
public import CORALean.ContSet.HPolytope.Float.Theorems.MemIneqsIff

@[expose] public section

/-!
# A box as halfspaces, over a floating-point scalar

Two square blocks rather than one stacked matrix: the identity against `sup`,
its negation against `-inf`, stacked. Nothing rounds — the entries are `one`
and `zero` and the bounds are the box's own — and the block form keeps the row
index out of `Fin.append`, which does not reduce on a variable.

This is the operation that needed `one` in the scalar: a constraint matrix
cannot name a coordinate without it.

## Inputs
* `I` – interval

## Hypotheses
* none

## Conclusion
* halfspace polytope equals the interval
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The identity matrix leaves entry `i` of a vector unchanged. -/
theorem aux_identityMat_mulVec (x : Vec ℝ n) (i : Fin n) : -- --- CONCL ---
    (toRealMat (identityMat 𝕋 n) *ᵥ x) i = x i := by -- --- PROOF ---
  show ∑ j, toReal (if i = j then (one : 𝕋) else zero) * x j = x i
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl, toReal_one, one_mul]
  · intro j _ hj
    rw [if_neg (Ne.symm hj), toReal_zero, zero_mul]
  · intro hc
    exact absurd (Finset.mem_univ i) hc


-- =======================================  MAIN THEOREM  ======================================= --

-- the two row blocks are exactly the two ends of the box, so nothing rounds
theorem Interval.hPolytope_exact (I : Interval (Vec 𝕋 n)) : -- --- CONCL ---
    (Interval.hPolytope I).construct = I.construct := by -- --- PROOF ---
  ext x
  simp only [Interval.hPolytope]
  rw [HPolytope.mem_stackRows_construct_iff (HPolytope.errFree_of_origin rfl rfl rfl)
    (HPolytope.errFree_of_origin rfl rfl rfl), HPolytope.mem_ineqs_iff, HPolytope.mem_ineqs_iff]
  constructor
  · rintro ⟨hup, hlo⟩ j
    have h₁ : x j ≤ toReal (I.sup j) := by rw [← aux_identityMat_mulVec (𝕋 := 𝕋) x j]; exact hup j
    have h₂ : -(x j) ≤ toReal (neg (I.inf j)) := by
      rw [← negIdentityMat_mulVec (𝕋 := 𝕋) x j]; exact hlo j
    rw [toReal_neg] at h₂
    -- stated plainly, membership being `entry` of the nominal box
    show toReal (I.inf j) ≤ x j ∧ x j ≤ toReal (I.sup j)
    exact ⟨by linarith, h₁⟩
  · intro h
    have hlo : ∀ j, toReal (I.inf j) ≤ x j := fun j => (h j).1
    have hhi : ∀ j, x j ≤ toReal (I.sup j) := fun j => (h j).2
    refine ⟨fun j => ?_, fun j => ?_⟩
    · rw [aux_identityMat_mulVec]
      exact hhi j
    · rw [negIdentityMat_mulVec, Pi.neg_apply, toReal_neg']
      linarith [hlo j]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
