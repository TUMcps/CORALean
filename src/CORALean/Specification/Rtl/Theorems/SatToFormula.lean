module

public import CORALean.Specification.Rtl.Definitions.Sat
public import CORALean.Specification.Rtl.Operations.ToFormula

@[expose] public section

/-!
# An `rtl` formula means what the paper's RTL formula means

If an `rtl` object is the formula `φ` of [1, Def. 1] (`toFormula`), its semantics (`Rtl.Sat`, the
equations (4)-(7) of [1, Def. 2], leaf by leaf) is the semantics of `φ`.

## Inputs
* `f` – reading of a label as a predicate

## Hypotheses
* none

## Conclusion
* the semantics of the object and of its paper formula agree

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {L X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Rtl.sat_toFormula (f : L → Pform X) :
    ∀ (ψ : Rtl L) (φ : RTL.Formula X), ψ.toFormula f = some φ → ∀ R : ℝ≥0 → Set X,
      (ψ.Sat (fun l r => (f l).Sat r) R ↔ φ.Sat R) := by -- --- PROOF ---
  intro ψ
  induction ψ with
  | all l =>
    intro φ h R
    obtain rfl : RTL.Formula.A (f l) = φ := Option.some.inj h
    exact Iff.rfl
  | and a b iha ihb =>
    intro φ h R
    -- both operands convert, and the conjunction is the conjunction
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b', hb, h⟩ := Option.map_eq_some_iff.mp h
    obtain rfl : RTL.Formula.and a' b' = φ := h
    exact and_congr (iha a' ha R) (ihb b' hb R)
  | or a b iha ihb =>
    intro φ h R
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b', hb, h⟩ := Option.map_eq_some_iff.mp h
    obtain rfl : RTL.Formula.or a' b' = φ := h
    exact or_congr (iha a' ha R) (ihb b' hb R)
  | next t a ih =>
    intro φ h R
    -- only a nonnegative shift converts
    unfold Rtl.toFormula at h
    split_ifs at h with ht
    obtain ⟨a', ha, h⟩ := Option.map_eq_some_iff.mp h
    obtain rfl : RTL.Formula.next t.toNNReal a' = φ := h
    exact ih a' ha _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
