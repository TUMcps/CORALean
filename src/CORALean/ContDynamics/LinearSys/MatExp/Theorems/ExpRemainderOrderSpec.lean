import CORALean.ContDynamics.LinearSys.MatExp.ExpRemainderOrder
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExistsExpRemainderBoundLt
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundAntitoneSucc

/-!
# The chosen order meets the error it was chosen for

What turns `exists_expRemainderBound_lt` into a rule: `expRemainderOrder` is
admissible whenever the error is, so a caller states `ε` and gets both the
bound and the side condition without naming an order at all.

`2 ≤ η` costs nothing to reach: the auxiliary lemma raises an admissible order
by one, so the witness the existence theorem hands over is raised twice and is
then at least `2` outright.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One more order keeps both halves: the bound falls, and the side condition
only has a larger denominator to divide by. -/
theorem aux_expRemainderBound_lt_succ {x : Mat ℝ n n} {ε : ℝ} {η : ℕ}
    (h : MatExp.expRemainderBound x η < ε ∧ ‖x‖ / ((η : ℝ) + 2) < 1) :
    MatExp.expRemainderBound x (η + 1) < ε ∧
      ‖x‖ / (((η + 1 : ℕ) : ℝ) + 2) < 1 := by -- --- PROOF ---
  obtain ⟨hb, hs⟩ := h
  have hnn : (0 : ℝ) ≤ ‖x‖ := norm_nonneg _
  have hpos : (0 : ℝ) < (η : ℝ) + 2 := by positivity
  -- the side condition at `η + 1` is the same numerator over a larger denominator
  have hs' : ‖x‖ / (((η + 1 : ℕ) : ℝ) + 2) < 1 := by
    have hle : ‖x‖ / (((η + 1 : ℕ) : ℝ) + 2) ≤ ‖x‖ / ((η : ℝ) + 2) := by
      push_cast
      apply div_le_div_of_nonneg_left hnn hpos
      linarith
    linarith
  exact ⟨lt_of_le_of_lt (MatExp.expRemainderBound_antitone_succ η hs) hb, hs'⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- The order chosen for `ε` is admissible for `ε`: under the bound, and sound,
with no side condition left for the caller to discharge. -/
theorem MatExp.expRemainderOrder_spec (x : Mat ℝ n n) {ε : ℝ} (hε : 0 < ε) :
    MatExp.OrderAdmissible x ε (MatExp.expRemainderOrder x ε) := by -- --- PROOF ---
  obtain ⟨η, hη⟩ := MatExp.exists_expRemainderBound_lt x hε
  -- two orders up is admissible outright, `2 ≤ η + 2` needing nothing of `η`
  have h2 := aux_expRemainderBound_lt_succ (aux_expRemainderBound_lt_succ hη)
  have hmem : MatExp.OrderAdmissible x ε (η + 1 + 1) := ⟨by omega, h2.1, h2.2⟩
  have hne : {η : ℕ | MatExp.OrderAdmissible x ε η}.Nonempty := ⟨η + 1 + 1, hmem⟩
  exact Nat.sInf_mem hne

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
