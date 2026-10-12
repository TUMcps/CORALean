import CORALean.ContSet.LevelSet.Real.Operations.PotIntCora
import CORALean.ContSet.LevelSet.Real.Definitions.RangeBound
import CORALean.ContSet.Interval.Real.Interval

/-!
# CORA's `potInt` misses a guard that is hit

The guard `{x | x = 0 ∧ x - 1 ≤ 0}` (a cell `{'==','<='}`) and the reach set `[0, 1]` share the
point `0`, yet the `==` row has bounds `(0, 1)`, which `isIntersecting_` reads as `0 < 0`, so
`potInt` does not list the pair `(0, 0)` and the jump through this guard is missed (read from the
source, not run). The bounds are range bounds of the guard function over the set.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The guard `x = 0 ∧ x - 1 ≤ 0`. -/
def LevelSet.aux_G : LevelSet 1 :=
  ⟨2, fun x i => if i = 0 then x 0 else x 0 - 1, fun i => if i.val = 0 then .eq else .le⟩

/-- The reach set `[0, 1]`. -/
def LevelSet.aux_R : Interval (Vec ℝ 1) := ⟨fun _ => 0, fun _ => 1⟩

/-- The bounds of the guard function over `[0, 1]`: `(0, 1)` and `(-1, 0)`. -/
def LevelSet.aux_BG (g : LevelSet 1) (_ : ℕ) : Fin g.m → ℝ × ℝ :=
  fun i => if i.val = 0 then (0, 1) else (-1, 0)


-- =======================================  MAIN THEOREM  ======================================= --

theorem LevelSet.potIntCora_misses_counterexample :
    LevelSet.aux_G.construct ∩ LevelSet.aux_R.construct ≠ ∅ ∧
      (∀ i : Fin 2, IsRangeBound (fun x => LevelSet.aux_G.f x i) LevelSet.aux_R.construct
        (LevelSet.aux_BG LevelSet.aux_G 0 i).1 (LevelSet.aux_BG LevelSet.aux_G 0 i).2) ∧
      (0, 0) ∉ LevelSet.potIntCora [LevelSet.aux_G] 1 LevelSet.aux_BG := by -- --- PROOF ---
  refine ⟨?_, ?_, ?_⟩
  · -- the point `0` is in both
    intro h
    have : (fun _ => (0 : ℝ) : Vec ℝ 1) ∈ (∅ : Set (Vec ℝ 1)) := by
      rw [← h]
      refine ⟨?_, fun i => ⟨le_rfl, zero_le_one⟩⟩
      show ∀ i : Fin 2, _
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩ <;> simp [LevelSet.aux_G, CompOp.holds]
    exact this
  · -- the bounds are range bounds
    refine Fin.forall_fin_two.mpr ⟨fun x hx => ?_, fun x hx => ?_⟩
    · have h0 := hx 0
      simp only [LevelSet.aux_BG, LevelSet.aux_G]
      exact ⟨h0.1, h0.2⟩
    · have h0 := hx 0
      have h1 : (0 : ℝ) ≤ x 0 := h0.1
      have h2 : x 0 ≤ 1 := h0.2
      simp only [LevelSet.aux_BG, LevelSet.aux_G]
      exact ⟨by simp; linarith, by simp; linarith⟩
  · -- the `==` row reads `0 < 0`
    rintro ⟨_, _, h⟩
    have := h (⟨0, by decide⟩ : Fin 2)
    simp [LevelSet.aux_G, LevelSet.aux_BG] at this


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
