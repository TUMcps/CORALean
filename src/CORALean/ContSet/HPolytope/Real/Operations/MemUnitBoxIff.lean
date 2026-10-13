module

public import CORALean.ContSet.HPolytope.Real.Operations.UnitBox
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Membership in `HPolytope.unitBox`

Membership is the two constraint halves read back as a bound on the magnitude.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `Fin.addCases` does not reduce on a variable index, so which half of the
constraint list an index falls in takes a rewrite. -/
theorem HPolytope.aux_unitBox_A_castAdd (j : Fin n) :
    (HPolytope.unitBox n).A (Fin.castAdd n j) = LinearMap.proj j := by
  show Fin.append (fun j : Fin n => (LinearMap.proj j : Vec ℝ n →ₗ[ℝ] ℝ))
    (fun j : Fin n => -(LinearMap.proj j : Vec ℝ n →ₗ[ℝ] ℝ)) (Fin.castAdd n j) = _
  rw [Fin.append_left]

theorem HPolytope.aux_unitBox_A_natAdd (j : Fin n) :
    (HPolytope.unitBox n).A (Fin.natAdd n j) = -LinearMap.proj j := by
  show Fin.append (fun j : Fin n => (LinearMap.proj j : Vec ℝ n →ₗ[ℝ] ℝ))
    (fun j : Fin n => -(LinearMap.proj j : Vec ℝ n →ₗ[ℝ] ℝ)) (Fin.natAdd n j) = _
  rw [Fin.append_right]


-- =======================================  MAIN THEOREM  ======================================= --

-- membership is those two halves read back as a bound on the magnitude
theorem HPolytope.mem_unitBox_iff {x : Vec ℝ n} :
    x ∈ (HPolytope.unitBox n).construct ↔ ∀ j, |x j| ≤ 1 := by -- --- PROOF ---
  constructor
  · rintro ⟨hle, -⟩ j
    have hup : x j ≤ 1 := by
      have h := hle (Fin.castAdd n j)
      rw [HPolytope.aux_unitBox_A_castAdd] at h
      exact h
    have hlo : -(x j) ≤ 1 := by
      have h := hle (Fin.natAdd n j)
      rw [HPolytope.aux_unitBox_A_natAdd] at h
      exact h
    exact abs_le.mpr ⟨by linarith, hup⟩
  -- back, the lower half being the negated projection
  · intro h
    refine ⟨Fin.addCases (fun j => ?_) fun j => ?_, fun i => i.elim0⟩
    · rw [HPolytope.aux_unitBox_A_castAdd]
      exact (abs_le.mp (h j)).2
    · rw [HPolytope.aux_unitBox_A_natAdd]
      have hlo := (abs_le.mp (h j)).1
      show -(x j) ≤ 1
      linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
