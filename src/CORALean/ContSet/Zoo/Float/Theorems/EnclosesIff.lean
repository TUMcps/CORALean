module

public import CORALean.ContSet.Zoo.Float.Zoo
public import CORALean.ContSet.SetIntersection.Theorems.Basic

@[expose] public section

/-!
# A zoo encloses `f` when each of its members does

`Zoo.Encloses` is membership in the zoo's `SetIntersection` of members; this unfolds it to the
two members' own statements, the form the operations' guarantees are proved in.

## Inputs
* `Z` – zoo
* `f` – function

## Hypotheses
* none

## Conclusion
* `Z` encloses `f` iff each member does
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zoo.encloses_iff {Z : Zoo 𝕋 n} {f : Vec ℝ n → ℝ} :
    Z.Encloses f ↔ (∀ T, Z.taylm = some T → T.Encloses f) ∧
      ∀ I, Z.ivl = some I → ∀ t ∈ Real.Taylm.box n,
        (fun _ => f t : Vec ℝ 1) ∈ I.construct := by -- --- PROOF ---
  obtain ⟨a, b⟩ := Z
  show f ∈ ContSet.construct (Zoo.members ⟨a, b⟩) ↔ _
  simp only [SetIntersection.mem_construct, Zoo.members, List.mem_append, List.mem_map,
    Option.mem_toList]
  cases a <;> cases b <;> simp [ContSet.construct, or_imp, forall_and, forall_eq']

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
