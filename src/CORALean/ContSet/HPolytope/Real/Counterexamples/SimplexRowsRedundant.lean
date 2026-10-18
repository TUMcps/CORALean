module

public import CORALean.ContSet.HPolytope.Real.Operations.SimplexRows
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.Global.DropIdx
public import CORALean.Global.EuclideanNorm
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# A unit direction can be redundant in `[1, Alg. 3]`

In `ℝ¹` the simplex is `{x ≤ 1, -x ≤ 1}`; appending the unit direction `ℓ = 1` repeats the row
`x ≤ 1`, and dropping the new row leaves the same set. So "any direction `ℓ` of unit length …
will be non-redundant" is false; it holds for `ℓ` distinct from the rows present
(`ineqs_unit_rows_minimal`).

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.simplexRows_redundant_counterexample : -- --- STMT ---
    ∃ ℓ : Fin 1 → Vec ℝ 1, ‖ℓ 0‖₂ = 1 ∧
      (HPolytope.ineqs (HPolytope.simplexRows ℓ) 1).construct =
        (HPolytope.ineqs ((HPolytope.simplexRows ℓ).submatrix (dropIdx (Fin.last 2)) id)
          fun i => (1 : Vec ℝ 3) (dropIdx (Fin.last 2) i)).construct := by -- --- PROOF ---
  refine ⟨fun _ => 1, by simp [norm₂], ?_⟩
  -- the rows `x ≤ 1`, `-x ≤ 1`, `x ≤ 1`, read off the appended blocks
  have hA : ∀ r : Fin 3, HPolytope.simplexRows (fun _ : Fin 1 => (1 : Vec ℝ 1)) r =
      Fin.append (Fin.append (fun i => (Pi.single i 1 : Vec ℝ 1))
        ![fun _ => -(1 / √((1 : ℕ) : ℝ))]) (fun _ : Fin 1 => (1 : Vec ℝ 1)) r := fun r => rfl
  have r0 : HPolytope.simplexRows (fun _ : Fin 1 => (1 : Vec ℝ 1)) 0 = Pi.single 0 1 := by
    rw [hA, show (0 : Fin 3) = (Fin.castAdd 1 (Fin.castAdd 1 (0 : Fin 1)) : Fin (1 + 1 + 1))
      from rfl, Fin.append_left, Fin.append_left]
  have r1 : HPolytope.simplexRows (fun _ : Fin 1 => (1 : Vec ℝ 1)) 1 = fun _ => -1 := by
    rw [hA, show (1 : Fin 3) = (Fin.castAdd 1 (Fin.natAdd 1 (0 : Fin 1)) : Fin (1 + 1 + 1))
      from rfl, Fin.append_left, Fin.append_right]
    simp
  have r2 : HPolytope.simplexRows (fun _ : Fin 1 => (1 : Vec ℝ 1)) 2 = 1 := by
    rw [hA, show (2 : Fin 3) = (Fin.natAdd (1 + 1) (0 : Fin 1) : Fin (1 + 1 + 1)) from rfl,
      Fin.append_right]
  -- the rows applied to a point
  have hrows : ∀ x : Vec ℝ 1, HPolytope.simplexRows (fun _ : Fin 1 => (1 : Vec ℝ 1)) *ᵥ x =
      ![x 0, -x 0, x 0] := fun x => by
    funext r
    fin_cases r
    · show HPolytope.simplexRows (fun _ : Fin 1 => (1 : Vec ℝ 1)) 0 ⬝ᵥ x = _
      rw [r0]
      simp
    · show HPolytope.simplexRows (fun _ : Fin 1 => (1 : Vec ℝ 1)) 1 ⬝ᵥ x = _
      rw [r1]
      simp [dotProduct]
    · show HPolytope.simplexRows (fun _ : Fin 1 => (1 : Vec ℝ 1)) 2 ⬝ᵥ x = _
      rw [r2]
      simp [dotProduct]
  -- dropping the last row leaves the first two, which already say `x ≤ 1`
  have hd0 : dropIdx (Fin.last 2) 0 = 0 := rfl
  have hd1 : dropIdx (Fin.last 2) 1 = 1 := rfl
  ext x
  rw [HPolytope.mem_ineqs_iff, HPolytope.mem_ineqs_iff]
  constructor
  · intro h i
    exact h _
  · intro h r
    have h0 := h 0
    have h1 := h 1
    change (HPolytope.simplexRows (fun _ : Fin 1 => (1 : Vec ℝ 1)) *ᵥ x) (dropIdx (Fin.last 2) 0)
      ≤ 1 at h0
    change (HPolytope.simplexRows (fun _ : Fin 1 => (1 : Vec ℝ 1)) *ᵥ x) (dropIdx (Fin.last 2) 1)
      ≤ 1 at h1
    rw [hd0, hrows] at h0
    rw [hd1, hrows] at h1
    rw [hrows]
    fin_cases r <;> simpa using (by assumption : _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
