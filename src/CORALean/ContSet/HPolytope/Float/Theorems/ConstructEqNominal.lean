module

public import CORALean.ContSet.HPolytope.Float.Definitions.Basic
public import CORALean.ContSet.HPolytope.Float.HPolytope

@[expose] public section

/-!
# An error-free polytope denotes its nominal part

A box whose bounds all read `0` is the origin, and adding the origin changes nothing; the slacks
are part of the nominal polytope, so this asks only for the box.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.construct_eq_nominal {P : HPolytope 𝕋 (Vec 𝕋 n)}
    (h : ∀ j, toReal (P.I_error.inf j) = 0 ∧ toReal (P.I_error.sup j) = 0) :
    P.construct = P.nominal.construct := by -- --- PROOF ---
  -- the box is the origin
  have hbox : P.I_error.construct = {0} := by
    ext x
    refine ⟨fun hx => funext fun j => ?_, fun hx => ?_⟩
    · have h1 : toReal (P.I_error.inf j) ≤ x j := (hx j).1
      have h2 : x j ≤ toReal (P.I_error.sup j) := (hx j).2
      rw [(h j).1] at h1
      rw [(h j).2] at h2
      exact le_antisymm h2 h1
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      intro j
      show toReal (P.I_error.inf j) ≤ 0 ∧ 0 ≤ toReal (P.I_error.sup j)
      rw [(h j).1, (h j).2]
      exact ⟨le_rfl, le_rfl⟩
  -- so the sum is the nominal part
  show P.nominal.construct + P.I_error.construct = _
  rw [hbox, Set.singleton_zero, add_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
