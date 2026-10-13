module

public import CORALean.ContSet.Zonotope.Float.Operations.MatPlus
public import CORALean.ContSet.Zonotope.Float.Theorems.OfEntryBoundsMatOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact

@[expose] public section

/-!
# `Zonotope.matPlus` over-approximates the Minkowski sum

The nominal parts add inside the exact `Zonotope.plus` (`plus_exact`), which
`ofEntryBoundsMat_outer` rounds: its generators are stored exactly, its centre between the
two directed sums. The boxes add by `matPlus_outer`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   09-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.matPlus_outer (Z₁ Z₂ : Zonotope (Mat 𝕋 m n)) :
    Z₁.construct + Z₂.construct ⊆ (Zonotope.matPlus Z₁ Z₂).construct := by -- --- PROOF ---
  rintro _ ⟨_, ⟨a, ha, e, he, rfl⟩, _, ⟨b, hb, f, hf, rfl⟩, rfl⟩
  have hab : a + b ∈ (CORALean.Real.Zonotope.plus Z₁.nominal Z₂.nominal).construct := by
    rw [← CORALean.Real.Zonotope.plus_exact]
    exact Set.add_mem_add ha hb
  -- the exact sum's generators are the stored ones, read as reals
  have hG : ∀ k i j, toReal (Fin.append Z₁.G Z₂.G k i j)
      ≤ (CORALean.Real.Zonotope.plus Z₁.nominal Z₂.nominal).G k i j
      ∧ (CORALean.Real.Zonotope.plus Z₁.nominal Z₂.nominal).G k i j
        ≤ toReal (Fin.append Z₁.G Z₂.G k i j) := by
    intro k i j
    refine Fin.addCases (fun l => ?_) (fun l => ?_) k
    · simp only [CORALean.Real.Zonotope.plus, Zonotope.nominal, realImage_mat, Fin.append_left,
        toRealMat]
      exact ⟨le_rfl, le_rfl⟩
    · simp only [CORALean.Real.Zonotope.plus, Zonotope.nominal, realImage_mat, Fin.append_right,
        toRealMat]
      exact ⟨le_rfl, le_rfl⟩
  -- the nominal sum rounded, the two boxes added
  have hmem : a + b + (e + f) ∈ (Zonotope.matPlus Z₁ Z₂).construct :=
    Zonotope.ofEntryBoundsMat_outer
      (CORALean.Real.Zonotope.plus Z₁.nominal Z₂.nominal) (Interval.matPlus Z₁.E Z₂.E)
      (cLo := fun i j => addDown (Z₁.c i j) (Z₂.c i j))
      (cHi := fun i j => addUp (Z₁.c i j) (Z₂.c i j))
      (fun i j => ⟨addDown_le_add _ _, add_le_addUp _ _⟩) hG
      ⟨a + b, hab, e + f, Interval.matPlus_outer _ _ he hf, rfl⟩
  have heq : a + b + (e + f) = a + e + (b + f) := by abel
  show a + e + (b + f) ∈ _
  rw [← heq]
  exact hmem

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
