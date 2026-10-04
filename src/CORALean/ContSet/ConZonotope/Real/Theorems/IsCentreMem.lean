import CORALean.ContSet.ConZonotope.Real.Operations.IsCentre
import CORALean.ContSet.ConZonotope.Real.Operations.MemOfMatIff
import CORALean.ContSet.HPolytope.Real.Operations.MemIneqsIff
import CORALean.ContSet.HPolytope.Real.Theorems.IsLPCentreMem

/-!
# The centre of a constrained zonotope lies in it

Every branch of `ConZonotope.IsCentre` names a coefficient vector `β` with `|β| ≤ 1` and `A β = b`
and puts the centre at `c + G β`: an optimum of a program over the coefficient polytope is feasible
in it. With no constraint rows the centre is `c`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α] {q h : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.IsCentre.mem {c : α} {G : Fin h → α} {A : Mat ℝ q h} {b : Vec ℝ q} {x : α}
    (hx : ConZonotope.IsCentre c G A b x) :
    x ∈ (ConZonotope.ofMat c G A b).construct := by -- --- PROOF ---
  rw [ConZonotope.mem_ofMat_iff]
  rcases hx with ⟨hq, rfl⟩ | ⟨-, hLP | hN | hK⟩
  · -- no constraint rows: the zero coefficients
    subst hq
    exact ⟨0, fun j => by simp, fun i => i.elim0, by simp⟩
  · -- the polytope program's optimum is in its domain
    obtain ⟨β, hβ, rfl⟩ := hLP
    have hmem := ConZonotope.mem_domain_iff.mp hβ.mem
    obtain ⟨hb, hP⟩ := hmem
    exact ⟨β, hb, HPolytope.mem_eqs_iff.mp hP, rfl⟩
  · -- the null-space optimum `x0 + N y` solves `A β = b` and its rows are the box
    obtain ⟨k, N, x0, y, hx0, hAN, -, -, -, -, hy, rfl⟩ := hN
    have hrow := hy.mem.1
    refine ⟨x0 + N *ᵥ y, fun j => ?_, fun i => ?_, rfl⟩
    · have h1 : (N *ᵥ y) j ≤ 1 - x0 j := by
        have := hrow (Fin.castAdd h j)
        simp only [ConZonotope.nullPolytope, Fin.append_left] at this
        exact this
      have h2 : -(N *ᵥ y) j ≤ 1 + x0 j := by
        have := hrow (Fin.natAdd h j)
        simp only [ConZonotope.nullPolytope, Fin.append_right] at this
        exact this
      rw [abs_le]
      simp only [Pi.add_apply]
      constructor <;> linarith
    · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, hAN, hx0]
      simp
  · -- a trivial kernel: the unique solution
    obtain ⟨β, -, hβ, hb, rfl⟩ := hK
    exact ⟨β, hb, fun i => by rw [hβ], rfl⟩


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
