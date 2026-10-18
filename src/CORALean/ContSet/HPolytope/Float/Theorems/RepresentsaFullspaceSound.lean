module

public import CORALean.ContSet.HPolytope.Float.Operations.RepresentsaFullspace
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
public import CORALean.ContSet.Interval.Float.Theorems.Basic

@[expose] public section

/-!
# A float polytope the `'fullspace'` test accepts is the whole space

When `representsaFullspace` answers `true`, every stored row is `0` read as reals, every
right-hand side admits `0`, so every point meets every row. One-sided: `false` decides
nothing, since a `le` may fail on numbers it could have certified.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.representsaFullspace_sound {P : HPolytope 𝕋 (Vec 𝕋 n)}
    (h : P.representsaFullspace = true) : P.construct = Set.univ := by -- --- PROOF ---
  unfold HPolytope.representsaFullspace at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const] at h
  obtain ⟨⟨hin, heq⟩, hbox⟩ := h
  -- a certified `le` each way is a zero entry
  have zr : ∀ {a : 𝕋}, (le a (FloatOps.zero : 𝕋) = true ∧ le (FloatOps.zero : 𝕋) a = true) →
      toReal a = 0 :=
    fun ⟨h₁, h₂⟩ => le_antisymm (toReal_zero (𝕋 := 𝕋) ▸ toReal_le_of_le h₁)
      (toReal_zero (𝕋 := 𝕋) ▸ toReal_le_of_le h₂)
  -- every point is the nominal point `x - e` plus the box point `e = inf`
  refine Set.eq_univ_of_forall fun x => ?_
  have he : (fun j => toReal (P.I_error.inf j)) ∈ P.I_error.construct :=
    Interval.mem_vec_iff.mpr fun j => ⟨le_rfl, toReal_le_of_le (hbox j)⟩
  have hy : x - (fun j => toReal (P.I_error.inf j)) ∈ P.nominal.construct := by
    refine HPolytope.mem_nominal_iff.mpr ⟨fun i => ?_, fun r => ?_⟩
    · -- the row is zero, and its bound is not negative
      have hrow : (toRealMat P.A *ᵥ (x - fun j => toReal (P.I_error.inf j))) i = 0 := by
        simp only [mulVec, dotProduct, toRealMat]
        exact Finset.sum_eq_zero fun j _ => by rw [zr ((hin i).2 j), zero_mul]
      rw [hrow]
      have h0 := toReal_le_of_le (hin i).1
      rw [toReal_zero] at h0
      linarith [abs_nonneg (toReal (P.b_error i))]
    · -- the row is zero, and its right-hand side is zero
      have hrow : (toRealMat P.Ae *ᵥ (x - fun j => toReal (P.I_error.inf j))) r = 0 := by
        simp only [mulVec, dotProduct, toRealMat]
        exact Finset.sum_eq_zero fun j _ => by rw [zr ((heq r).2 j), zero_mul]
      rw [hrow, zr (heq r).1, sub_zero, abs_zero]
      exact abs_nonneg _
  exact ⟨_, hy, _, he, sub_add_cancel _ _⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
