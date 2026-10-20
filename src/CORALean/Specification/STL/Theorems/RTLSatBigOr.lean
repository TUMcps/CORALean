module

public import CORALean.Specification.STL.Operations.RTLBigOr

@[expose] public section

/-!
# A disjunction of RTL formulas

[1, Lemma 2]: `R ⊨ᵣ ⋁ (l.map g) ⇔ ∃ b ∈ l, R ⊨ᵣ g b`, given a state at time `0`: the empty `⋁` is
`A ⊥`, which holds exactly of an empty `R(0)`.

## Inputs
* `β` – index type
* `l` – list of indices
* `g` – formula of each index
* `R` – reach sequence

## Hypotheses
* `h` – the reach set at time zero is nonempty

## Conclusion
* the disjunction holds iff some formula holds

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

theorem RTL.Formula.sat_bigOr {β : Type} (l : List β) (g : β → RTL.Formula X) (R : ℝ≥0 → Set X)
    (h : (R 0).Nonempty) :
    (RTL.Formula.bigOr (l.map g)).Sat R ↔ ∃ b ∈ l, (g b).Sat R := by -- --- PROOF ---
  induction l with
  | nil =>
    -- `A ⊥` says every state of `R 0` is false
    obtain ⟨r, hr⟩ := h
    simp only [RTL.Formula.bigOr, List.map_nil, List.foldr_nil, RTL.Formula.Sat, List.not_mem_nil,
      false_and, exists_false, iff_false]
    exact fun h => h r hr
  | cons b l ih =>
    have : (RTL.Formula.bigOr ((b :: l).map g)).Sat R ↔
        (g b).Sat R ∨ (RTL.Formula.bigOr (l.map g)).Sat R := Iff.rfl
    rw [this, ih]
    simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
