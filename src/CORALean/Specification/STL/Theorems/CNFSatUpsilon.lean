module

public import CORALean.Specification.STL.Operations.CNFUpsilon
public import CORALean.Specification.STL.Theorems.RTLSatBigOr
public import CORALean.Specification.STL.Theorems.RTLSatBigAnd
public import CORALean.Specification.STL.Theorems.ShiftShift

@[expose] public section

/-!
# What `Υ` of a normal form says of a reach sequence

`R ⊨ᵣ Υ(⋀ᵢ ⋁ⱼ X_c^j (φᵢⱼ ∨ ϱᵢⱼ))` unfolded: each clause has a branch whose `ϱ'` holds of the whole
set `R(jc + c/2)`, or `ϱ_l ∨ ϱ'` does for some `l`, or `ϱᵢⱼ` of all of `R(jc)`. Every `R(0)` and
each `R(jc + c/2)` must be non-empty, which is what makes the empty `⋁` of [1, Lemma 2], Eq. (17),
false.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.CNF.sat_upsilon (c : ℝ≥0) (cnf : STL.CNF X) (R : ℝ≥0 → Set X)
    (h₀ : (R 0).Nonempty) (hne : ∀ clause ∈ cnf, ∀ b ∈ clause, (R (c / 2 + b.j * c)).Nonempty) :
    (cnf.upsilon c).Sat R ↔ ∀ clause ∈ cnf, ∃ b ∈ clause,
      ((∀ r ∈ R (c / 2 + b.j * c), (Pform.bigOr b.K).Sat r) ∨
        ∃ ϱ ∈ b.L, ∀ r ∈ R (c / 2 + b.j * c), (ϱ.or (Pform.bigOr b.K)).Sat r) ∨
      ∀ r ∈ R (b.j * c), b.ϱ.Sat r := by -- --- PROOF ---
  unfold STL.CNF.upsilon
  simp only [RTL.Formula.sat_bigAnd]
  refine forall₂_congr fun clause hcl => ?_
  rw [RTL.Formula.sat_bigOr _ _ _ h₀]
  refine exists_congr fun b => and_congr_right fun hb => ?_
  -- unfold the shifts, each leaving the set at a single time
  simp only [RTL.Formula.Sat, Time.shift_shift]
  rw [RTL.Formula.sat_bigOr _ _ _ (by simp only [Time.shift, zero_add]; exact hne clause hcl b hb)]
  simp only [RTL.Formula.Sat, Time.shift, zero_add]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
