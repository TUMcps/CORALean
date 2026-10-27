module

public import CORALean.ContSet.LevelSet.Real.LevelSet
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `isequal` of CORA's levelSet equates level sets that differ

`aux_isequal_levelSet` renames the variables of each equation to placeholders by their order among
the equation's own used variables, `subs(ls.eq(i), usedVars1, subNames)` and `subs(S.eq(j),
usedVars2, subNames)`, and calls rows equal when `simplify` of the difference is `0`. The table
`symNames(:,2)` meant to record which variable of the second level set stands for which of the first
is written and never read, so nothing makes the renamings of different rows agree. For the level
sets `x₁ ≤ 0` and `x₂ ≤ 0` over `[x₁; x₂]` both equations become the placeholder `xyz_1`, and CORA
answers `true` (read from the source, not run). `LevelSet.step_rowMatchCora` is that per-row test;
the theorem says it holds for the two rows while the level sets differ.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA equates two level sets that differ
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The row test of `aux_isequal_levelSet`: the equations agree after renaming the variables. -/
@[step_of LevelSet.isequal_cora_counterexample]
def LevelSet.step_rowMatchCora (f g : Vec ℝ n → ℝ) : Prop :=
  ∃ π : Equiv.Perm (Fin n), ∀ x, f x = g (fun k => x (π k))


-- =======================================  MAIN THEOREM  ======================================= --

theorem LevelSet.isequal_cora_counterexample : -- --- CONCL ---
    let L : LevelSet 2 := ⟨1, fun x _ => x 0, fun _ => .le⟩
    let S : LevelSet 2 := ⟨1, fun x _ => x 1, fun _ => .le⟩
    L.op 0 = S.op 0 ∧ LevelSet.step_rowMatchCora (fun x => L.f x 0) (fun x => S.f x 0) ∧
      L.construct ≠ S.construct := by -- --- PROOF ---
  intro L S
  refine ⟨rfl, ⟨Equiv.swap 0 1, fun x => ?_⟩, fun h => ?_⟩
  · simp [L, S]
  · have h1 : (fun k : Fin 2 => if k = 0 then (0 : ℝ) else 1) ∈ L.construct := by
      intro i
      simp [L, CompOp.holds]
    rw [h] at h1
    have := h1 0
    simp [S, CompOp.holds] at this
    have h2 : (1 : ℝ) ≤ 0 := this
    exact absurd h2 (by norm_num)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
