module

public import CORALean.Specification.STL.Theorems.SatOfPform
public import CORALean.Specification.STL.Definitions.Transformation

@[expose] public section

/-!
# Eq. 10 needs every `R(t)` non-empty

[1, Eq. 10] says a sound and complete `Υ` has `Υ(ϱ) ≡ Aϱ`. Take the single reach sequence `R` that
is `Bool` everywhere but at time `1`, where it is empty, and `Υ(φ)` true or false as `C(R) ⊨ₜ φ`:
it is sound and complete for `{R}`, `C(R)` is empty, so `Υ(⊥)` holds while `A ⊥` does not.

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

theorem STL.exists_upsilon_ofPform_ne : -- --- STMT ---
    ∃ (R : ℝ≥0 → Set Bool) (Υ : STL.Formula Bool → RTL.Formula Bool),
      STL.IsSound {R} Υ ∧ STL.IsComplete {R} Υ ∧
        ¬ ((Υ (STL.Formula.ofPform Pform.bot)).Sat R ↔
          (RTL.Formula.A Pform.bot).Sat R) := by -- --- PROOF ---
  classical
  let R : ℝ≥0 → Set Bool := fun t => if t = 1 then ∅ else Set.univ
  -- `Υ(φ)` is `A ⊤` when `φ` holds of the traces of `R` and `A ⊥` otherwise
  let Υ : STL.Formula Bool → RTL.Formula Bool := fun φ =>
    if φ.HoldsOn (ReachSequence.traceSet R) then .A Pform.top else .A Pform.bot
  have h0 : R 0 = Set.univ := by simp [R]
  -- `A ⊥` fails at `R`, since `R 0` has a state
  have hbot : ¬ (RTL.Formula.A Pform.bot).Sat R := fun h => h true (by simp [h0]) |>.elim
  have htop : (RTL.Formula.A Pform.top).Sat R := fun r _ => trivial
  refine ⟨R, Υ, ?_, ?_, ?_⟩
  · rintro R' rfl φ h
    by_contra hφ
    exact hbot (by simpa [Υ, hφ] using h)
  · rintro R' rfl φ h
    have : Υ φ = RTL.Formula.A Pform.top := if_pos h
    rw [this]; exact htop
  · -- `C(R)` is empty, so `⊥` holds of all of it
    have hC : (STL.Formula.ofPform (Pform.bot : Pform Bool)).HoldsOn (ReachSequence.traceSet R) :=
      fun ξ hξ => absurd (hξ 1) (by simp [R])
    intro h
    have : Υ (STL.Formula.ofPform Pform.bot) = RTL.Formula.A Pform.top := if_pos hC
    exact hbot (h.1 (by rw [this]; exact htop))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
