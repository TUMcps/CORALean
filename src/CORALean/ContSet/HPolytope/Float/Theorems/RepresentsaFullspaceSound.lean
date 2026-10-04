import CORALean.ContSet.HPolytope.Float.Operations.RepresentsaFullspace
import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

/-!
# A float polytope the `'fullspace'` test accepts is the whole space

When `representsaFullspace` answers `true`, every stored row is `0` read as reals, every
right-hand side admits `0`, so every point meets every row. One-sided: `false` decides
nothing, since a `le` may fail on numbers it could have certified.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.representsaFullspace_sound {P : HPolytope 𝕋 n}
    (h : P.representsaFullspace = true) : P.construct = Set.univ := by -- --- PROOF ---
  unfold HPolytope.representsaFullspace at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const] at h
  obtain ⟨hin, heq⟩ := h
  -- a certified `le` each way is a zero entry
  have zr : ∀ {a : 𝕋}, (le a (FloatOps.zero : 𝕋) = true ∧ le (FloatOps.zero : 𝕋) a = true) →
      toReal a = 0 :=
    fun ⟨h₁, h₂⟩ => le_antisymm (toReal_zero (𝕋 := 𝕋) ▸ toReal_le_of_le h₁)
      (toReal_zero (𝕋 := 𝕋) ▸ toReal_le_of_le h₂)
  refine Set.eq_univ_of_forall fun x => HPolytope.mem_construct_iff.mpr ⟨fun i => ?_, fun r => ?_⟩
  · -- the row is zero, and its bound is not negative
    have hrow : (toRealMat P.A *ᵥ x) i = 0 := by
      simp only [mulVec, dotProduct, toRealMat]
      exact Finset.sum_eq_zero fun j _ => by rw [zr ((hin i).2 j), zero_mul]
    rw [hrow]
    simpa [toReal_zero] using toReal_le_of_le (hin i).1
  · -- the row is zero, and its interval holds zero
    have hrow : (toRealMat P.Ae *ᵥ x) r = 0 := by
      simp only [mulVec, dotProduct, toRealMat]
      exact Finset.sum_eq_zero fun j _ => by rw [zr ((heq r).2 j), zero_mul]
    rw [hrow]
    exact ⟨by simpa [toReal_zero] using toReal_le_of_le (heq r).1.1,
      by simpa [toReal_zero] using toReal_le_of_le (heq r).1.2⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
