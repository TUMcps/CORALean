import CORALean.ContSet.Polytope.Polytope

/-!
# `Polytope.unitBox`

The supremum-norm unit ball as `2n` constraints, `±xⱼ ≤ 1`. This is the
coefficient domain a zonotope ranges over, so a constrained zonotope's domain is
this intersected with its constraints.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

def Polytope.unitBox (n : ℕ) : Polytope (Vec ℝ n) where
  m := n + n
  A := Fin.append (fun j => LinearMap.proj j) (fun j => -LinearMap.proj j)
  b := fun _ => 1
  me := 0
  Ae := Fin.elim0
  be := Fin.elim0

/-- `Fin.addCases` does not reduce on a variable index, so which half of the
constraint list an index falls in takes a rewrite. -/
theorem Polytope.aux_unitBox_A_castAdd (j : Fin n) :
    (Polytope.unitBox n).A (Fin.castAdd n j) = LinearMap.proj j := by
  show Fin.append (fun j : Fin n => (LinearMap.proj j : Vec ℝ n →ₗ[ℝ] ℝ))
    (fun j : Fin n => -(LinearMap.proj j : Vec ℝ n →ₗ[ℝ] ℝ)) (Fin.castAdd n j) = _
  rw [Fin.append_left]

theorem Polytope.aux_unitBox_A_natAdd (j : Fin n) :
    (Polytope.unitBox n).A (Fin.natAdd n j) = -LinearMap.proj j := by
  show Fin.append (fun j : Fin n => (LinearMap.proj j : Vec ℝ n →ₗ[ℝ] ℝ))
    (fun j : Fin n => -(LinearMap.proj j : Vec ℝ n →ₗ[ℝ] ℝ)) (Fin.natAdd n j) = _
  rw [Fin.append_right]

theorem Polytope.mem_unitBox_iff {x : Vec ℝ n} :
    x ∈ (Polytope.unitBox n).construct ↔ ∀ j, |x j| ≤ 1 := by
  constructor
  · rintro ⟨hle, -⟩ j
    have hup : x j ≤ 1 := by
      have h := hle (Fin.castAdd n j)
      rw [Polytope.aux_unitBox_A_castAdd] at h
      exact h
    have hlo : -(x j) ≤ 1 := by
      have h := hle (Fin.natAdd n j)
      rw [Polytope.aux_unitBox_A_natAdd] at h
      exact h
    exact abs_le.mpr ⟨by linarith, hup⟩
  · intro h
    refine ⟨Fin.addCases (fun j => ?_) fun j => ?_, fun i => i.elim0⟩
    · rw [Polytope.aux_unitBox_A_castAdd]
      exact (abs_le.mp (h j)).2
    · rw [Polytope.aux_unitBox_A_natAdd]
      have hlo := (abs_le.mp (h j)).1
      show -(x j) ≤ 1
      linarith

end CORALean.Real
