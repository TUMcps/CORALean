import CORALean.ContSet.SpectraShadow.Real.SpectraShadow
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

/-!
# A shadow with every generator zero has no interior

With every generator zero the shadow is inside the point `{c}`, which has no interior in a space of
positive dimension: the case CORA's `norm(G, 'fro') < 1e-8` shortcut means to catch.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.not_isFullDim_of_G_zero (hn : 0 < n) (S : SpectraShadow (Vec ℝ n))
    (hG : ∀ j, S.G j = 0) : ¬ (interior S.construct).Nonempty := by -- --- PROOF ---
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  -- the shadow is in the point `{c}`
  have hsub : S.construct ⊆ {S.c} := by
    rintro _ ⟨β, -, rfl⟩
    simp [hG]
  rintro ⟨x, hx⟩
  have := interior_mono hsub hx
  rw [interior_singleton] at this
  exact this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
