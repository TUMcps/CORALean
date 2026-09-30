import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOuter
import CORALean.ContSet.Interval.Real.Instances
import CORALean.ContSet.Zonotope.Real.Instances

/-!
# The same `reach`, two different matrix uncertainties

`LinParamSysDT.reach` asks for `Mtimes 𝕄 S` and nothing about what `𝕄` is: its
guarantee was written `⋃ A ∈ construct M, …` from the start, so a *set* of
matrices needs no interface of its own, only an `Mtimes` instance. This file
runs the one algorithm at two: an interval matrix `𝕄 := ℐ` and a matrix
zonotope `𝕄 := 𝕄𝒵`, both bounding the same nominal system matrix — the
identity — at `S := 𝒵`.

A concrete trajectory, the system matrix pinned to the identity at every step
and the input held at zero, lands in `reach`'s output through `reach_outer` at
each representation, with no line of `reach` itself touched.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet

-- The uncertainty models: an interval matrix and a matrix zonotope, bracketing the identity.

/-- The identity, bounded within `0.9` of itself on the diagonal, and exactly on
the off-diagonal. -/
def Example.sysI : LinParamSysDT ℐ 2 :=
  ⟨⟨!![(0.9:ℝ), 0; 0, 0.9], !![(1.1:ℝ), 0; 0, 1.1]⟩⟩

/-- The identity, plus one generator of radius `0.1` on the diagonal. -/
def Example.sysZ : LinParamSysDT 𝕄𝒵 2 :=
  ⟨⟨1, (1 : Mat ℝ 2 2), fun _ => !![(0.1:ℝ), 0; 0, 0.1]⟩⟩

/-- The identity sits in both: entrywise within the interval's bounds, and at
the matrix zonotope's own centre. -/
theorem Example.one_mem_sysI : (1 : Mat ℝ 2 2) ∈ construct Example.sysI.A := by
  rintro ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    norm_num [Entrywise.entry_mat, Matrix.one_apply, Example.sysI]

theorem Example.one_mem_sysZ : (1 : Mat ℝ 2 2) ∈ construct Example.sysZ.A :=
  ⟨fun _ => 0, fun _ => by norm_num, by simp [Example.sysZ]⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Start at `(1, 1)`, hold the input at `0`: the identity system matrix leaves
the state fixed at every step. -/
def Example.lpX0 : Vec ℝ 2 := ![1, 1]

def Example.lpR0 : Zonotope (Vec ℝ 2) := Zonotope.ofPoint Example.lpX0
def Example.lpU : Zonotope (Vec ℝ 2) := Zonotope.ofPoint (0 : Vec ℝ 2)

/-- A trajectory at the interval-matrix uncertainty: the same identity at every
step, witnessed by `one_mem_sysI`. -/
theorem Example.trajI : Example.sysI.Trajectory (S := 𝒵) Example.lpR0 Example.lpU
    (fun _ => Example.lpX0) (fun _ => 0) where
  init := Zonotope.mem_ofPoint Example.lpX0
  input _ := Zonotope.mem_ofPoint 0
  step _ := ⟨1, Example.one_mem_sysI, by simp [Example.lpX0, Matrix.one_mulVec]⟩

/-- The same trajectory at the matrix-zonotope uncertainty, witnessed by
`one_mem_sysZ` instead. -/
theorem Example.trajZ : Example.sysZ.Trajectory (S := 𝒵) Example.lpR0 Example.lpU
    (fun _ => Example.lpX0) (fun _ => 0) where
  init := Zonotope.mem_ofPoint Example.lpX0
  input _ := Zonotope.mem_ofPoint 0
  step _ := ⟨1, Example.one_mem_sysZ, by simp [Example.lpX0, Matrix.one_mulVec]⟩

/-- `reach_outer`, unchanged, at the interval matrix. -/
example {o : ℕ} (ho : 0 < o) (k : ℕ) :
    Example.lpX0 ∈
      construct (Example.sysI.reach (S := 𝒵) ⟨Example.lpR0, Example.lpU, 0, k⟩ ⟨o, ho⟩) :=
  Example.sysI.reach_outer (S := 𝒵) ho Example.lpR0 Example.lpU Example.trajI k

/-- `reach_outer`, unchanged, at the matrix zonotope — the strictly tighter
model, since it keeps the correlation an interval matrix throws away. -/
example {o : ℕ} (ho : 0 < o) (k : ℕ) :
    Example.lpX0 ∈
      construct (Example.sysZ.reach (S := 𝒵) ⟨Example.lpR0, Example.lpU, 0, k⟩ ⟨o, ho⟩) :=
  Example.sysZ.reach_outer (S := 𝒵) ho Example.lpR0 Example.lpU Example.trajZ k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
