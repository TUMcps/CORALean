module

public import CORALean.ContSet.HPolytope.Float.Operations.BoxToSlack
public import CORALean.ContSet.HPolytope.Float.Theorems.Basic
public import CORALean.ContSet.HPolytope.Float.Theorems.LeErrUp

@[expose] public section

/-!
# `HPolytope.boxToSlack` encloses

A point of `P` is a nominal point plus a box point. Each row reads the nominal point within its
slack and the box point within what `errUp` bounds, so the sum is within the widened slack, and
the result's box is the origin.

## Inputs
* `P` – H-polytope

## Hypotheses
* none

## Conclusion
* the box in the slacks encloses the polytope with its box
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The box in the slacks encloses the polytope with its box. -/
theorem HPolytope.boxToSlack_outer (P : HPolytope 𝕋 (Vec 𝕋 n)) :
    P.construct ⊆ P.boxToSlack.construct := by -- --- PROOF ---
  rintro _ ⟨y, hy, e, he, rfl⟩
  obtain ⟨hle, heq⟩ := HPolytope.mem_nominal_iff.mp hy
  -- a row reads the sum as the sum of what it reads
  have hrow : ∀ {k : ℕ} (M : Mat 𝕋 k n) (i : Fin k),
      (toRealMat M *ᵥ (y + e)) i = (toRealMat M *ᵥ y) i + ∑ j, toReal (M i j) * e j := by
    intro k M i
    rw [Matrix.mulVec_add, Pi.add_apply]
    rfl
  refine (HPolytope.mem_nominal_of_origin rfl).mpr
    (HPolytope.mem_nominal_iff.mpr ⟨fun i => ?_, fun i => ?_⟩)
  -- an inequality: the box adds at most `errUp`
  · show (toRealMat P.A *ᵥ (y + e)) i
      ≤ toReal (P.b i) + |toReal (addUp (absolute (P.b_error i)) (P.errUp (P.A i)))|
    have h := add_le_addUp (absolute (P.b_error i)) (P.errUp (P.A i))
    have h' := P.le_errUp (P.A i) he
    rw [toReal_absolute] at h
    rw [hrow]
    linarith [hle i, le_abs_self (toReal (addUp (absolute (P.b_error i)) (P.errUp (P.A i))))]
  -- an equality: the box moves its reading by at most the larger of the two directions
  · set w := addUp (absolute (P.be_error i)) (maximum (P.errUp (P.Ae i)) (P.errUp (-(P.Ae i))))
    show |(toRealMat P.Ae *ᵥ (y + e)) i - toReal (P.be i)| ≤ |toReal w|
    have h := add_le_addUp (absolute (P.be_error i))
      (maximum (P.errUp (P.Ae i)) (P.errUp (-(P.Ae i))))
    have hu := P.le_errUp (P.Ae i) he
    have hl := P.le_errUp (-(P.Ae i)) he
    simp only [Pi.neg_apply, toReal_neg', neg_mul, Finset.sum_neg_distrib] at hl
    rw [toReal_absolute, toReal_maximum] at h
    have hw : toReal w ≤ |toReal w| := le_abs_self _
    have hm1 := le_max_left (toReal (P.errUp (P.Ae i))) (toReal (P.errUp (-(P.Ae i))))
    have hm2 := le_max_right (toReal (P.errUp (P.Ae i))) (toReal (P.errUp (-(P.Ae i))))
    have hz := abs_le.mp (heq i)
    rw [hrow, abs_le]
    constructor <;> linarith [hz.1, hz.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
