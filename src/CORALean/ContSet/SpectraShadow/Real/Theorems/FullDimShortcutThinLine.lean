module

public import CORALean.ContSet.SpectraShadow.Real.Operations.FullDimShortcut

@[expose] public section

/-!
# CORA's `isFullDim` shortcut marks a full-dimensional shadow as empty

The shortcut reads the generator matrix alone: `A₀ = 1`, `A₁ = 0`, `c = 0` and `G = 10⁻⁹` is all of
`ℝ¹`, with an interior, and `norm(G, 'fro') < 1e-8` fires, so CORA caches `emptySet.val = true`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `{β · 10⁻⁹}`: the whole of `ℝ¹`, through a tiny generator. -/
noncomputable abbrev aux_thinLine : SpectraShadow (Vec ℝ 1) :=
  ⟨1, 1, 1, fun _ => 0, 0, fun _ => fun _ => 1 / 10 ^ 9⟩

theorem aux_thinLine_construct : aux_thinLine.construct = Set.univ := by -- --- PROOF ---
  ext x
  simp only [Set.mem_univ, iff_true]
  refine ⟨fun _ => x 0 * 10 ^ 9, ?_, ?_⟩
  · simp only [aux_thinLine, smul_zero, Finset.sum_const_zero, add_zero]
    exact (Matrix.PosSemidef.one : (1 : Mat ℝ 1 1).PosSemidef)
  · funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    simp [aux_thinLine]


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.fullDimShortcut_thinLine :
    aux_thinLine.fullDimShortcut ∧ (interior aux_thinLine.construct).Nonempty := by -- --- PROOF ---
  refine ⟨?_, ?_⟩
  · simp [SpectraShadow.fullDimShortcut, SpectraShadow.aux_gFro, aux_thinLine]
    norm_num
  · rw [aux_thinLine_construct, interior_univ]
    exact ⟨0, trivial⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
