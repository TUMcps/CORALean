module

public import CORALean.Specification.Kleene.Operations.Basic
public import CORALean.Specification.KleeneSignal.Definitions.IsValid
public import CORALean.Specification.KleeneSignal.KleeneSignal
public import CORALean.Specification.KleeneSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.CombineSpec
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# A three-valued signal from its minimal and maximal refinements

`until`, `and_` and `or_` of `kleeneSignal` build their result from the Boolean signals `mn`, the
operation on the refinements with unknown mapped to false, and `mx`, with unknown mapped to true:
the Boolean part is `mn`, and the value is unknown where they differ. For valid `mn`, `mx` the
signal is valid, `True` where both are `true` and `False` where both are `false`.

`mn` and `mx` are `⌊Λ⌋` and `⌈Λ⌉` of the result, which is their `⊔₁`, as
[1, Sec. 4.2 (refinements)] recovers `Λ(t)`.

## Inputs
* `T` – time type
* `mn` – minimal refinement
* `mx` – maximal refinement

## Hypotheses
* `hmn` – the minimal refinement is valid
* `hmx` – the maximal refinement is valid

## Conclusion
* the combined signal is valid, true where both hold and false where neither

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- The signal built from `mn` and `mx` is `True` where both hold, `False` where neither. -/
theorem KleeneSignal.minMax_spec {T : Type} [LinearOrder T] [Zero T]
    (mn mx : PointSegmentSignal T) (hmn : mn.IsValid) (hmx : mx.IsValid) : -- --- CONCL ---
    let R : KleeneSignal T := ⟨mn, PointSegmentSignal.combine
      (fun (args : Fin 2 → Bool) (_ : Unit) => decide (args 0 ≠ args 1)) ![mn, mx] ()⟩
    R.IsValid ∧ ∀ t : T, 0 ≤ t → (R.at t = Kleene.tt ↔ mn.at t = true ∧ mx.at t = true) ∧
      (R.at t = Kleene.ff ↔ mn.at t = false ∧ mx.at t = false) := by -- --- PROOF ---
  intro R
  -- the unknown part is the combination of the two refinements
  obtain ⟨hv, h⟩ := PointSegmentSignal.combine_spec
    (fun (args : Fin 2 → Bool) (_ : Unit) => decide (args 0 ≠ args 1)) ![mn, mx]
    (Fin.forall_fin_two.2 ⟨hmn, hmx⟩) ()
  refine ⟨⟨hmn, hv⟩, fun t ht => ?_⟩
  have hu := h t ht
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hu
  simp only [R, KleeneSignal.at, hu]
  -- read off the values by cases on the two Boolean values
  have key : ∀ a b : Bool,
      ((if decide (a ≠ b) = true then Kleene.uu else Kleene.fromBool a) = Kleene.tt ↔
        a = true ∧ b = true) ∧
      ((if decide (a ≠ b) = true then Kleene.uu else Kleene.fromBool a) = Kleene.ff ↔
        a = false ∧ b = false) := by
    intro a b
    cases a <;> cases b <;> simp [Kleene.fromBool]
  exact key _ _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
