module

public import CORALean.ContSet.HPolytope.Float.Operations.Isequal

@[expose] public section

/-!
# `HPolytope.isequal` is sound

A `true` answer says the stored numbers agree as real numbers, so the nominal polytopes are the
same, and so are the denoted sets. `false` refutes nothing.

## Inputs
* `P` – H-polytope
* `Q` – H-polytope

## Hypotheses
* `h` – `P.isequal Q` holds

## Conclusion
* `P` and `Q` have the same nominal part
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.isequal_nominal {P Q : HPolytope 𝕋 (Vec 𝕋 n)}
    (h : P.isequal Q = true) : -- --- CONCL ---
    P.nominal = Q.nominal := by -- --- PROOF ---
  unfold HPolytope.isequal at h
  split at h
  · rename_i e
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const] at h
    -- a certified `le` each way is equality of the stored numbers as reals
    have eqr : ∀ {a b : 𝕋}, (le a b = true ∧ le b a = true) → toReal a = toReal b :=
      fun ⟨h₁, h₂⟩ => le_antisymm (toReal_le_of_le h₁) (toReal_le_of_le h₂)
    obtain ⟨⟨hin, heq⟩, -⟩ := h
    obtain ⟨m₁, A₁, b₁, e₁, Ae₁, be₁, eb₁, ebe₁, E₁⟩ := P
    obtain ⟨m₂, A₂, b₂, e₂, Ae₂, be₂, eb₂, ebe₂, E₂⟩ := Q
    simp only at e hin heq
    obtain ⟨rfl, rfl⟩ := e
    simp only [Fin.cast_eq_self] at hin heq
    have hA : toRealMat A₁ = toRealMat A₂ :=
      funext fun r => funext fun j => eqr (by simpa using (hin r).2 j)
    have hb : toRealVec b₁ = toRealVec b₂ := funext fun r => eqr (hin r).1.1
    have heb : toRealVec eb₁ = toRealVec eb₂ := funext fun r => eqr (hin r).1.2
    -- the equality rows likewise, and their slack
    have hAe : toRealMat Ae₁ = toRealMat Ae₂ :=
      funext fun r => funext fun j => eqr (by simpa using (heq r).2 j)
    have hbe : toRealVec be₁ = toRealVec be₂ := funext fun r => eqr (heq r).1.1
    have hebe : toRealVec ebe₁ = toRealVec ebe₂ := funext fun r => eqr (heq r).1.2
    show Real.HPolytope.intersection
        (Real.HPolytope.ineqs (toRealMat A₁) (toRealVec b₁ + |toRealVec eb₁|))
        (Real.HPolytope.slab (toRealMat Ae₁) (toRealVec be₁ - |toRealVec ebe₁|)
          (toRealVec be₁ + |toRealVec ebe₁|)) =
      Real.HPolytope.intersection
        (Real.HPolytope.ineqs (toRealMat A₂) (toRealVec b₂ + |toRealVec eb₂|))
        (Real.HPolytope.slab (toRealMat Ae₂) (toRealVec be₂ - |toRealVec ebe₂|)
          (toRealVec be₂ + |toRealVec ebe₂|))
    rw [hA, hb, heb, hAe, hbe, hebe]
  · simp at h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
