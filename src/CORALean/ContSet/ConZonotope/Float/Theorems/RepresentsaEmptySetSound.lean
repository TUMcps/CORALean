module

public import CORALean.ContSet.ConZonotope.Float.Operations.RepresentsaEmptySet

@[expose] public section

/-!
# A `true` from `ConZonotope.representsa_emptySet` proves the set empty

Every point of the set would satisfy `0 = c x ≤ val` for the certified bound `val`, and `val < 0`
is what the check established.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.representsa_emptySet_sound {cZ : ConZonotope 𝕋 (Vec 𝕋 n)}
    (h : cZ.representsa_emptySet = true) : cZ.construct = ∅ := by -- --- PROOF ---
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  have hlt := toReal_lt_of_ltStrict h
  rw [toReal_zero] at hlt
  have hle := (cZ.boundDotWeights
    (c := rowLin (fun (_ : Fin 1) => fun (_ : Fin n) => (zero : 𝕋)) 0)
    (fun _ => zero) (fun _ => rfl) cZ.P.emptyWeights.1 cZ.P.emptyWeights.2.1
    cZ.P.emptyWeights.2.2).le x hx
  have h0 : (rowLin (fun (_ : Fin 1) => fun (_ : Fin n) => (zero : 𝕋)) 0) x = 0 := by
    refine (show _ = ∑ j, toReal (zero : 𝕋) * x j from rfl).trans ?_
    simp [toReal_zero]
  rw [h0] at hle
  linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
