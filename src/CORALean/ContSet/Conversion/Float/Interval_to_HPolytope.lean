import CORALean.ContSet.HPolytope.Float.Operations.Intersection
import CORALean.ContSet.HPolytope.Float.Operations.MemIntersectionIff
import CORALean.ContSet.HPolytope.Float.Operations.Ineqs
import CORALean.ContSet.HPolytope.Float.Operations.MemIneqsIff

/-!
# A box as halfspaces, over a floating-point scalar

Two square blocks rather than one stacked matrix: the identity against `sup`,
its negation against `-inf`, intersected. Nothing rounds — the entries are `one`
and `zero` and the bounds are the box's own — and the block form keeps the row
index out of `Fin.append`, which does not reduce on a variable.

This is the operation that needed `one` in the scalar: a constraint matrix
cannot name a coordinate without it.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- The identity, and the identity negated: the only two constraint matrices a
box needs. -/
def identityMat (𝕋 : Type) [FloatOps 𝕋] (n : ℕ) : Mat 𝕋 n n :=
  fun i j => if i = j then one else zero

def negIdentityMat (𝕋 : Type) [FloatOps 𝕋] (n : ℕ) : Mat 𝕋 n n :=
  fun i j => if i = j then neg one else zero

theorem identityMat_mulVec (x : Vec ℝ n) (i : Fin n) :
    (toRealMat (identityMat 𝕋 n) *ᵥ x) i = x i := by -- --- PROOF ---
  show ∑ j, toReal (if i = j then (one : 𝕋) else zero) * x j = x i
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl, toReal_one, one_mul]
  · intro j _ hj
    rw [if_neg (Ne.symm hj), toReal_zero, zero_mul]
  · intro hc
    exact absurd (Finset.mem_univ i) hc

-- the same for the negated identity, which is what turns a lower bound into a row
theorem negIdentityMat_mulVec (x : Vec ℝ n) (i : Fin n) :
    (toRealMat (negIdentityMat 𝕋 n) *ᵥ x) i = -(x i) := by -- --- PROOF ---
  show ∑ j, toReal (if i = j then neg (one : 𝕋) else zero) * x j = -(x i)
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl, toReal_neg, toReal_one, neg_one_mul]
  · intro j _ hj
    rw [if_neg (Ne.symm hj), toReal_zero, zero_mul]
  · intro hc
    exact absurd (Finset.mem_univ i) hc

def Interval.hPolytope (I : Interval (Vec 𝕋 n)) : HPolytope 𝕋 (Vec 𝕋 n) :=
  (HPolytope.ineqs (identityMat 𝕋 n) I.sup).intersection
    (HPolytope.ineqs (negIdentityMat 𝕋 n) fun j => neg (I.inf j))


-- =======================================  MAIN THEOREM  ======================================= --

-- the two row blocks are exactly the two ends of the box, so nothing rounds
theorem Interval.hPolytope_exact (I : Interval (Vec 𝕋 n)) :
    (Interval.hPolytope I).construct = I.construct := by -- --- PROOF ---
  ext x
  simp only [Interval.hPolytope]
  rw [HPolytope.mem_intersection_iff, HPolytope.mem_ineqs_iff, HPolytope.mem_ineqs_iff]
  constructor
  · rintro ⟨hup, hlo⟩ j
    have h₁ : x j ≤ toReal (I.sup j) := by rw [← identityMat_mulVec (𝕋 := 𝕋) x j]; exact hup j
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
    · rw [identityMat_mulVec]
      exact hhi j
    · rw [negIdentityMat_mulVec, toReal_neg]
      linarith [hlo j]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
