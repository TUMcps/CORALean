import CORALean.ContSet.HPolytope.Real.HPolytope
import CORALean.ContSet.Interval.Real.Interval

/-!
# `HPolytope.box`

CORA's `polytope(interval)`: a box as the `2n` constraints `xⱼ ≤ supⱼ` and
`-xⱼ ≤ -infⱼ`. `unitBox` is this at `[-1, 1]ⁿ`, kept separate because a
constrained zonotope's domain names it constantly and should not carry an
interval around.

The only conversion into a halfspace description that costs nothing. The other
direction — a box enclosing a halfspace description — is `2n` linear programs.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

def HPolytope.box (I : Interval (Vec ℝ n)) : HPolytope (Vec ℝ n) where
  m := n + n
  A := Fin.append (fun j => LinearMap.proj j) (fun j => -LinearMap.proj j)
  b := Fin.append I.sup fun j => -I.inf j
  me := 0
  Ae := Fin.elim0
  be := Fin.elim0

/-- `Fin.addCases` does not reduce on a variable index, so which half of the
constraint list an index falls in takes a rewrite. -/
theorem HPolytope.aux_box_A_castAdd (I : Interval (Vec ℝ n)) (j : Fin n) :
    (HPolytope.box I).A (Fin.castAdd n j) = LinearMap.proj j := by
  show Fin.append (fun j : Fin n => (LinearMap.proj j : Vec ℝ n →ₗ[ℝ] ℝ))
    (fun j : Fin n => -(LinearMap.proj j : Vec ℝ n →ₗ[ℝ] ℝ)) (Fin.castAdd n j) = _
  rw [Fin.append_left]

theorem HPolytope.aux_box_A_natAdd (I : Interval (Vec ℝ n)) (j : Fin n) :
    (HPolytope.box I).A (Fin.natAdd n j) = -LinearMap.proj j := by
  show Fin.append (fun j : Fin n => (LinearMap.proj j : Vec ℝ n →ₗ[ℝ] ℝ))
    (fun j : Fin n => -(LinearMap.proj j : Vec ℝ n →ₗ[ℝ] ℝ)) (Fin.natAdd n j) = _
  rw [Fin.append_right]

theorem HPolytope.aux_box_b_castAdd (I : Interval (Vec ℝ n)) (j : Fin n) :
    (HPolytope.box I).b (Fin.castAdd n j) = I.sup j := by
  show Fin.append I.sup (fun j => -I.inf j) (Fin.castAdd n j) = _
  rw [Fin.append_left]

theorem HPolytope.aux_box_b_natAdd (I : Interval (Vec ℝ n)) (j : Fin n) :
    (HPolytope.box I).b (Fin.natAdd n j) = -I.inf j := by
  show Fin.append I.sup (fun j => -I.inf j) (Fin.natAdd n j) = _
  rw [Fin.append_right]

theorem HPolytope.mem_box_iff {I : Interval (Vec ℝ n)} {x : Vec ℝ n} :
    x ∈ (HPolytope.box I).construct ↔ ∀ j, I.inf j ≤ x j ∧ x j ≤ I.sup j := by
  constructor
  · rintro ⟨hle, -⟩ j
    have hup : x j ≤ I.sup j := by
      have h := hle (Fin.castAdd n j)
      rw [HPolytope.aux_box_A_castAdd, HPolytope.aux_box_b_castAdd] at h
      exact h
    have hlo : -(x j) ≤ -I.inf j := by
      have h := hle (Fin.natAdd n j)
      rw [HPolytope.aux_box_A_natAdd, HPolytope.aux_box_b_natAdd] at h
      exact h
    exact ⟨by linarith, hup⟩
  · intro h
    refine ⟨Fin.addCases (fun j => ?_) fun j => ?_, fun i => i.elim0⟩
    · rw [HPolytope.aux_box_A_castAdd, HPolytope.aux_box_b_castAdd]
      exact (h j).2
    · rw [HPolytope.aux_box_A_natAdd, HPolytope.aux_box_b_natAdd]
      show -(x j) ≤ -I.inf j
      linarith [(h j).1]

end CORALean.Real
