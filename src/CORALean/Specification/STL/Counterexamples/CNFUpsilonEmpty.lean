module

public import CORALean.Specification.STL.Theorems.CNFSatToFormula
public import CORALean.Specification.STL.Theorems.CNFSatUpsilon
public import CORALean.Specification.STL.Definitions.ReachSequence

@[expose] public section

/-!
# Lemma 2 needs every `R(t)` non-empty

[1, Lemma 2]'s proof glues a trace out of a state of every `R(t)`. With `R(5)` empty, `C(R)` is
empty and every formula holds of it, but `Υ` still asks for states: `R(t) = Bool` for `t ≠ 5` and
the formula `X_0(F(0,1)⊥ ∨ ⊥)` is a counterexample, `R` finitely represented with breakpoint `5`.

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

theorem STL.CNF.exists_upsilon_not_complete_of_empty : -- --- CONCL ---
    ∃ (R : ℝ≥0 → Set Bool) (T : Finset ℝ≥0) (cnf : STL.CNF Bool),
      ReachSequence.FinRep T R ∧ ReachSequence.CDivisible 1 T ∧
        (∀ clause ∈ cnf, (clause.map STL.Branch.j).Nodup) ∧
          ¬ ((cnf.upsilon 1).Sat R ↔
            (cnf.toFormula 1).HoldsOn (ReachSequence.traceSet R)) := by -- --- PROOF ---
  classical
  -- `R` is `Bool` everywhere but at time `5`
  let R : ℝ≥0 → Set Bool := fun t => if t = 5 then ∅ else Set.univ
  let b : STL.Branch Bool := { j := 0, ϱ := Pform.bot, K := [], L := [] }
  have h25 : (2⁻¹ : ℝ≥0) ≠ 5 := by
    intro h
    have := congrArg NNReal.toReal h
    norm_num at this
  refine ⟨R, {5}, [[b]], ?_, fun u hu => ⟨5, by simpa using hu⟩, by simp [b], ?_⟩
  · -- no breakpoint lies in the interval between two points that avoid it
    intro s t h
    have hs : s ≠ 5 := fun e => h 5 (by simp) (by simp [e])
    have ht : t ≠ 5 := fun e => h 5 (by simp) (by simp [e])
    simp [R, hs, ht]
  · intro h
    -- no trace exists, so the formula holds of all of them
    have hC : (STL.CNF.toFormula 1 [[b]]).HoldsOn (ReachSequence.traceSet R) :=
      fun ξ hξ => absurd (hξ 5) (by simp [R])
    have hR : ∀ clause ∈ [[b]], ∀ b ∈ clause, (R (1 / 2 + b.j * 1)).Nonempty := by
      intro clause _ b' hb'
      obtain rfl := List.mem_singleton.1 ‹clause ∈ [[b]]›
      obtain rfl := List.mem_singleton.1 hb'
      simp [R, b, h25]
    -- but `Υ` asks `⊥` of the state set at `1/2`, which has a state
    have hU := (STL.CNF.sat_upsilon 1 _ R (by simp [R]) hR).1 (h.2 hC) _ (List.mem_singleton_self _)
    obtain ⟨b', hb', hb''⟩ := hU
    obtain rfl := List.mem_singleton.1 hb'
    simp [b, R, Pform.bigOr, Pform.Sat, h25] at hb''

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
