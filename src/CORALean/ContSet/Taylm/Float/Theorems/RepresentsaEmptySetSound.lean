module

public import CORALean.ContSet.Taylm.Float.Operations.RepresentsaEmptySet

@[expose] public section

/-!
# `Taylm.representsa_emptySet` is sound

A `true` answer exhibits a component whose remainder bounds are crossed, so no point satisfies it:
the range set is empty.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.representsa_emptySet_sound {T : Fin m → Taylm 𝕋 n}
    (h : Taylm.representsa_emptySet T = true) : Taylm.construct T = ∅ := by -- --- PROOF ---
  obtain ⟨i, -, hi⟩ := List.any_eq_true.1 h
  have hlt := toReal_lt_of_ltStrict hi
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  -- a point of the range set would have `remInf ≤ remSup` in coordinate `i`
  obtain ⟨t, -, ht⟩ := hx
  have h1 : toReal (T i).remInf ≤ x i - (T i).nominal.poly t := (ht i).1
  have h2 : x i - (T i).nominal.poly t ≤ toReal (T i).remSup := (ht i).2
  linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
