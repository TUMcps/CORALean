module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.IsOrderAdmissible
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderOrder
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExistsExpRemainderBoundLt
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# The chosen order meets the error it was chosen for

What turns `exists_expRemainderBound_lt` into a rule: `expRemainderOrder` is
admissible whenever the error is, so a caller states `ε` and gets both the
bound and the side condition without naming an order at all.

`2 ≤ η` costs nothing to reach: the auxiliary lemma raises an admissible order
by one, so the witness the existence theorem hands over is raised twice and is
then at least `2` outright.

## Inputs
* `x` – matrix
* `ε` – admissible error

## Hypotheses
* `hε` – error positive

## Conclusion
* the chosen order is admissible for the error
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- One more order never costs precision: raising `η` never raises the bound,
given the side condition the lower order already needs. -/
theorem MatExp.aux_expRemainderBound_antitone_succ {x : Mat ℝ n n} (η : ℕ)
    (hx : ‖x‖ / ((η : ℝ) + 2) < 1) : -- --- CONCL ---
    MatExp.expRemainderBound x (η + 1) ≤ MatExp.expRemainderBound x η := by -- --- PROOF ---
  have hnn : (0 : ℝ) ≤ ‖x‖ := norm_nonneg _
  have h2pos : (0 : ℝ) < (η : ℝ) + 2 := by positivity
  have hterm1_nn : (0 : ℝ) ≤ ‖x‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ) := by positivity
  have hfact : (Nat.factorial (η + 1 + 1) : ℝ) = ((η : ℝ) + 2) * (Nat.factorial (η + 1) : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have heq : ‖x‖ ^ (η + 1 + 1) / (Nat.factorial (η + 1 + 1) : ℝ)
      = (‖x‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ)) * (‖x‖ / ((η : ℝ) + 2)) := by
    rw [hfact, pow_succ]
    field_simp
  -- the leading term shrinks by a factor of at most `1`, the side condition's own bound
  have hterm1 : ‖x‖ ^ (η + 1 + 1) / (Nat.factorial (η + 1 + 1) : ℝ)
      ≤ ‖x‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ) := by
    rw [heq]
    calc (‖x‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ)) * (‖x‖ / ((η : ℝ) + 2))
        ≤ (‖x‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left hx.le hterm1_nn
      _ = ‖x‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ) := mul_one _
  have hfrac_mono : ‖x‖ / ((η : ℝ) + 1 + 2) ≤ ‖x‖ / ((η : ℝ) + 2) := by
    apply div_le_div_of_nonneg_left hnn h2pos
    linarith
  have hd1 : (0 : ℝ) < 1 - ‖x‖ / ((η : ℝ) + 2) := by linarith
  have hd2 : (0 : ℝ) < 1 - ‖x‖ / ((η : ℝ) + 1 + 2) := by linarith
  have hterm2 : (1 - ‖x‖ / ((η : ℝ) + 1 + 2))⁻¹ ≤ (1 - ‖x‖ / ((η : ℝ) + 2))⁻¹ :=
    inv_anti₀ hd1 (by linarith)
  have hterm2_nn : (0 : ℝ) ≤ (1 - ‖x‖ / ((η : ℝ) + 1 + 2))⁻¹ := inv_nonneg.mpr hd2.le
  simp only [MatExp.expRemainderBound]
  push_cast
  exact mul_le_mul hterm1 hterm2 hterm2_nn hterm1_nn

end


/-- One more order keeps both halves: the bound falls, and the side condition
only has a larger denominator to divide by. -/
theorem aux_expRemainderBound_lt_succ {x : Mat ℝ n n} {ε : ℝ} {η : ℕ}
    (h : MatExp.expRemainderBound x η < ε ∧ ‖x‖ / ((η : ℝ) + 2) < 1) : -- --- CONCL ---
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
  exact ⟨lt_of_le_of_lt (MatExp.aux_expRemainderBound_antitone_succ η hs) hb, hs'⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- The order chosen for `ε` is admissible for `ε`: under the bound, and sound,
with no side condition left for the caller to discharge. -/
theorem MatExp.expRemainderOrder_spec (x : Mat ℝ n n) {ε : ℝ} (hε : 0 < ε) : -- --- CONCL ---
    MatExp.IsOrderAdmissible x ε (MatExp.expRemainderOrder x ε) := by -- --- PROOF ---
  obtain ⟨η, hη⟩ := MatExp.exists_expRemainderBound_lt x hε
  -- two orders up is admissible outright, `2 ≤ η + 2` needing nothing of `η`
  have h2 := aux_expRemainderBound_lt_succ (aux_expRemainderBound_lt_succ hη)
  have hmem : MatExp.IsOrderAdmissible x ε (η + 1 + 1) := ⟨by omega, h2.1, h2.2⟩
  have hne : {η : ℕ | MatExp.IsOrderAdmissible x ε η}.Nonempty := ⟨η + 1 + 1, hmem⟩
  exact Nat.sInf_mem hne

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
