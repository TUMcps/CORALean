module

public import CORALean.ContSet.SpectraShadow.Float.Operations.RepresentsaOrigin
public import CORALean.ContSet.SpectraShadow.Float.Theorems.RepresentsaPointSound

@[expose] public section

/-!
# A `true` from `SpectraShadow.representsa_origin` proves the set is `{0}`

The certified singleton is the box's corner (`SpectraShadow.representsa_point_sound`'s
argument), and that corner reads as `0`.

## Inputs
* `S` – spectrahedral shadow
* `Yup` – matrices indexed by `Fin n`
* `Ylo` – matrices indexed by `Fin n`
* `β` – vector of length `S.m`

## Hypotheses
* `h` – `S.representsa_origin Yup Ylo β` holds

## Conclusion
* A `true` from `SpectraShadow.representsa_origin` proves the set is `{0}`
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

theorem SpectraShadow.representsa_origin_sound {S : SpectraShadow 𝕋 (Vec 𝕋 n)}
    {Yup Ylo : Fin n → Mat 𝕋 S.k S.k} {β : Vec 𝕋 S.m}
    (h : S.representsa_origin Yup Ylo β = true) : S.construct = {0} := by -- --- PROOF ---
  simp only [SpectraShadow.representsa_origin, Bool.and_eq_true] at h
  obtain ⟨hp, ho⟩ := h
  split at ho
  · rename_i I hI
    simp only [List.all_eq_true, List.mem_finRange, Bool.and_eq_true, forall_const] at ho
    -- the member the singleton test certified is the box's corner, which is `0`
    have hpI := hp
    unfold SpectraShadow.representsa_point at hpI
    rw [hI] at hpI
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const] at hpI
    have h0 : toRealVec I.sup = 0 := funext fun i =>
      le_antisymm ((toReal_le_of_le (ho i).1).trans_eq toReal_zero)
        (toReal_zero.symm.trans_le (toReal_le_of_le (ho i).2))
    obtain ⟨p, hS⟩ := SpectraShadow.representsa_point_sound hp
    have hmem := SpectraShadow.containsPoint_sound hpI.2
    rw [h0, hS, Set.mem_singleton_iff] at hmem
    rw [hS, ← hmem]
  · exact absurd ho (by simp)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
