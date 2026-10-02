import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
import CORALean.ContSet.Zonotope.Float.Operations.OfEntryBounds
import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError
import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

/-!
# `Zonotope.ofEntryBounds` contains the exact zonotope it brackets

The exact zonotope's coefficients are the witness: the stored generators reach the
nominal part, the centre's gap is `sub_mem_residual`, and each generator's gap, being
nonnegative and below its width, is `mem_generatorError`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.ofEntryBounds_outer (Z : CORALean.Real.Zonotope (Vec ℝ n))
    {cLo cHi : Vec 𝕋 n} {GLo GHi : Mat 𝕋 n Z.h} (E : Interval (Vec 𝕋 n))
    (hc : ∀ i, toReal (cLo i) ≤ Z.c i ∧ Z.c i ≤ toReal (cHi i))
    (hG : ∀ i k, toReal (GLo i k) ≤ Z.G k i ∧ Z.G k i ≤ toReal (GHi i k)) :
    Z.construct + E.construct
      ⊆ (Zonotope.ofEntryBounds cLo cHi GLo GHi E).construct := by -- --- PROOF ---
  rintro _ ⟨_, ⟨β, hβ, rfl⟩, e, he, rfl⟩
  -- each generator's gap is nonnegative and below its width
  have hW : ∀ i k, |Z.G k i - toReal (GLo i k)| ≤ toReal (subUp (GHi i k) (GLo i k)) := by
    intro i k
    rw [abs_of_nonneg (sub_nonneg.mpr (hG i k).1)]
    exact le_trans (sub_le_sub_right (hG i k).2 _) (sub_le_subUp _ _)
  refine ⟨fun i => toReal (cLo i) + ∑ k, toReal (GLo i k) * β k,
    Zonotope.mem_nominalSet_iff.mpr ⟨β, hβ, fun _ => rfl⟩,
    _, Interval.plus_outer _ _ ⟨_, Interval.plus_outer _ _ ⟨e, he, _,
      Interval.sub_mem_residual (stored := cLo) hc, rfl⟩, _,
      Zonotope.mem_generatorError (Δ := fun i k => Z.G k i - toReal (GLo i k)) hW hβ, rfl⟩, ?_⟩
  -- coordinate by coordinate, the stored part and the gaps recombine into the exact point
  funext i
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hsum : ∑ k, β k * Z.G k i
      = ∑ k, toReal (GLo i k) * β k + ∑ k, (Z.G k i - toReal (GLo i k)) * β k := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsum]
  ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
