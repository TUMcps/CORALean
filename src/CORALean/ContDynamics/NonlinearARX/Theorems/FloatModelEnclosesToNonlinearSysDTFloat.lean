module

public import CORALean.ContDynamics.NonlinearARX.Operations.ToNonlinearSysDTFloat

@[expose] public section

/-!
# The converted float model encloses the converted system

If `fm` encloses `sys`, then `fm.toNonlinearSysDTFloat` encloses `sys.toNonlinearSysDT`: a block of
the next window below the last is a block of this one, and the last block is `f_ARX` at the
window and the inputs, newest first. An outer statement.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float ContSet SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {dy du p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearARX.FloatModel.Encloses.toNonlinearSysDTFloat
    {fm : NonlinearARX.FloatModel 𝕋 dy du p} {sys : NonlinearARX dy du p}
    (h : fm.Encloses sys) :
    fm.toNonlinearSysDTFloat.Encloses sys.toNonlinearSysDT := by -- --- PROOF ---
  -- a vector is in a float box when every coordinate is between the real bounds
  have mem_iff : ∀ {k : ℕ} (I : Interval (Vec 𝕋 k)) (v : Vec ℝ k),
      v ∈ construct I ↔ ∀ i, toReal (I.inf i) ≤ v i ∧ v i ≤ toReal (I.sup i) :=
    fun _ _ => Iff.rfl
  refine ⟨fun X V x hx v hv => ?_⟩
  rw [mem_iff] at hx hv
  rw [mem_iff]
  intro r
  unfold NonlinearARX.FloatModel.toNonlinearSysDTFloat NonlinearARX.toNonlinearSysDT
  dsimp only
  by_cases hr : (finProdFinEquiv.symm r).1.val + 1 < p
  · -- a block moved up from the window
    simp only [dif_pos hr]
    exact hx _
  · -- the newest block, `f_ARX`
    simp only [dif_neg hr]
    exact (mem_iff _ _).1 (h.f_mem
      ⟨fun s => X.inf (finProdFinEquiv (Fin.rev (finProdFinEquiv.symm s).1,
          (finProdFinEquiv.symm s).2)),
       fun s => X.sup (finProdFinEquiv (Fin.rev (finProdFinEquiv.symm s).1,
          (finProdFinEquiv.symm s).2))⟩
      ⟨fun s => V.inf (finProdFinEquiv (Fin.rev (finProdFinEquiv.symm s).1,
          (finProdFinEquiv.symm s).2)),
       fun s => V.sup (finProdFinEquiv (Fin.rev (finProdFinEquiv.symm s).1,
          (finProdFinEquiv.symm s).2))⟩
      (fun s => x (finProdFinEquiv (Fin.rev (finProdFinEquiv.symm s).1,
          (finProdFinEquiv.symm s).2))) ((mem_iff _ _).2 fun s => hx _)
      (fun s => v (finProdFinEquiv (Fin.rev (finProdFinEquiv.symm s).1,
          (finProdFinEquiv.symm s).2))) ((mem_iff _ _).2 fun s => hv _)) _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
