module

public import CORALean.Specification.STL.Theorems.CNFSatToFormula
public import CORALean.Specification.STL.Theorems.CNFSatUpsilon
public import CORALean.Specification.STL.Definitions.ReachSequence

@[expose] public section

/-!
# Lemma 2 needs the powers `j` of a clause to be distinct

[1, Lemma 2] reads `⋁ⱼ X_c^j (φᵢⱼ ∨ ϱᵢⱼ)` with one disjunct per `j`. Two branches with the same
`j` break completeness: `F(0,1) x ∨ F(0,1) ¬x` holds of every trace of `R(t) = Bool`, yet `Υ` is
`X_{1/2} A x ∨ X_{1/2} A ¬x`, false, where `Υ` of the merged `F(0,1)(x ∨ ¬x)` is true.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* a clause with duplicate powers makes the encoding incomplete

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


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.CNF.exists_upsilon_not_complete_of_duplicate : -- --- CONCL ---
    ∃ (R : ℝ≥0 → Set Bool) (cnf : STL.CNF Bool),
      (∀ t, (R t).Nonempty) ∧ ReachSequence.IsFinRep ∅ R ∧ ReachSequence.IsCDivisible 1 ∅ ∧
        ¬ ((cnf.upsilon 1).Satisfies R ↔
          (cnf.toFormula 1).HoldsOn (ReachSequence.traceSet R)) := by -- --- PROOF ---
  -- two branches at `j = 0`, one for each of the two states
  let br : (Bool → Prop) → STL.Branch Bool := fun p =>
    { j := 0, ϱ := Pform.bot, K := [Pform.atom p], L := [] }
  let R : ℝ≥0 → Set Bool := fun _ => Set.univ
  have hne : ∀ t, (R t).Nonempty := fun _ => ⟨true, trivial⟩
  refine ⟨R, [[br (fun x => x = true), br (fun x => x = false)]], hne, fun _ _ _ => rfl,
    fun u hu => by simp at hu, ?_⟩
  intro h
  -- every trace is `true` or `false` at `1/2`, so one of the two `F` holds
  have hC : (STL.CNF.toFormula 1 [[br (fun x => x = true), br (fun x => x = false)]]).HoldsOn
      (ReachSequence.traceSet R) := by
    intro ξ _
    rw [STL.CNF.sat_toFormula]
    intro clause hcl
    obtain rfl := List.mem_singleton.1 hcl
    cases hx : ξ (1 / 2)
    · refine ⟨br (fun x => x = false), by simp, Or.inl (Or.inl ⟨Pform.atom fun x => x = false,
        by simp [br], 1 / 2, by norm_num, by norm_num, ?_⟩)⟩
      simpa [Pform.Satisfies, br] using hx
    · refine ⟨br (fun x => x = true), by simp, Or.inl (Or.inl ⟨Pform.atom fun x => x = true,
        by simp [br], 1 / 2, by norm_num, by norm_num, ?_⟩)⟩
      simpa [Pform.Satisfies, br] using hx
  -- but `Υ` asks that all of `Bool` be `true`, or all `false`
  have hU := (STL.CNF.sat_upsilon 1 _ R (hne 0) fun _ _ _ _ => ⟨true, trivial⟩).1 (h.2 hC) _
    (List.mem_singleton_self _)
  obtain ⟨b, hb, hb'⟩ := hU
  rcases List.mem_pair.1 hb with rfl | rfl <;>
    simp [br, Pform.bigOr, Pform.Satisfies, R] at hb'

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
