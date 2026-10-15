import CORALean.ContDynamics.LinParamSysDT.Operations.Canonical
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
contraction `0.9 · I` — at `S := 𝒵`.

A concrete trajectory, the system matrix pinned to the nominal `0.9 · I` at every
step and the input held at zero, so that the state shrinks by `0.9` each step, lands
in `reach`'s output through `reach_outer` at each representation, with no line of
`reach` itself touched.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet

-- The uncertainty models: an interval matrix and a matrix zonotope, bracketing the identity.

/-- The contraction `0.9 · I`, bounded within `0.1` of itself on the diagonal, and exactly on
the off-diagonal. -/
def Example.sysI : LinParamSysDT ℐ 2 :=
  .canonical ⟨!![(0.8:ℝ), 0; 0, 0.8], !![(1.0:ℝ), 0; 0, 1.0]⟩

/-- The same contraction, `0.9 · I` plus one generator of radius `0.1` on the diagonal. -/
def Example.sysZ : LinParamSysDT 𝕄𝒵 2 :=
  .canonical ⟨1, (0.9 : ℝ) • (1 : Mat ℝ 2 2), fun _ => !![(0.1:ℝ), 0; 0, 0.1]⟩

/-- The nominal matrix `0.9 · I` sits in both: entrywise within the interval's bounds, and at
the matrix zonotope's own center. -/
theorem Example.nominal_mem_sysI : (0.9 : ℝ) • (1 : Mat ℝ 2 2) ∈ construct Example.sysI.A := by
  rintro ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    norm_num [Entrywise.entry_mat, Matrix.one_apply, Example.sysI, LinParamSysDT.canonical]

theorem Example.nominal_mem_sysZ : (0.9 : ℝ) • (1 : Mat ℝ 2 2) ∈ construct Example.sysZ.A :=
  ⟨fun _ => 0, fun _ => by norm_num, by simp [Example.sysZ, LinParamSysDT.canonical]⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Start at `(1, 1)`, hold the input at `0`: the nominal matrix shrinks the state by `0.9`
every step, `x(k) = 0.9ᵏ · (1, 1)`. -/
def Example.lpX0 : Vec ℝ 2 := ![1, 1]

def Example.lpR0 : Zonotope (Vec ℝ 2) := Zonotope.ofPoint Example.lpX0
def Example.lpU : Zonotope (Vec ℝ 2) := Zonotope.ofPoint (0 : Vec ℝ 2)

/-- The nominal run: the contraction applied `k` times. -/
def Example.lpX (k : ℕ) : Vec ℝ 2 := (0.9 : ℝ) ^ k • Example.lpX0

theorem Example.lpX_zero : Example.lpX 0 = Example.lpX0 := by simp [Example.lpX]

theorem Example.lpX_succ (k : ℕ) :
    Example.lpX (k + 1) = ((0.9 : ℝ) • (1 : Mat ℝ 2 2)) *ᵥ Example.lpX k + 0 := by
  simp [Example.lpX, pow_succ, mul_smul, Matrix.smul_mulVec, smul_comm (0.9 : ℝ)]

/-- A trajectory at the interval-matrix uncertainty: the nominal matrix at every
step, witnessed by `nominal_mem_sysI`. -/
theorem Example.trajI : Example.sysI.IsCanonicalTrajectory (S := 𝒵) Example.lpR0 Example.lpU
    Example.lpX (fun _ => 0) where
  init := by rw [Example.lpX_zero]; exact Zonotope.mem_ofPoint Example.lpX0
  input _ := Zonotope.mem_ofPoint 0
  step k := ⟨_, Example.nominal_mem_sysI, Example.lpX_succ k⟩

/-- The same trajectory at the matrix-zonotope uncertainty, witnessed by
`nominal_mem_sysZ` instead. -/
theorem Example.trajZ : Example.sysZ.IsCanonicalTrajectory (S := 𝒵) Example.lpR0 Example.lpU
    Example.lpX (fun _ => 0) where
  init := by rw [Example.lpX_zero]; exact Zonotope.mem_ofPoint Example.lpX0
  input _ := Zonotope.mem_ofPoint 0
  step k := ⟨_, Example.nominal_mem_sysZ, Example.lpX_succ k⟩

/-- `reach_outer`, unchanged, at the interval matrix: the contracted state after `k`
steps is in the computed set. -/
example {o : ℕ} (ho : 0 < o) (k : ℕ) :
    Example.lpX k ∈
      construct (Example.sysI.reach (S := 𝒵) ⟨Example.lpR0, Example.lpU, 0, k⟩ ⟨o, ho⟩) :=
  Example.sysI.reach_outer (S := 𝒵) ho Example.lpR0 Example.lpU Example.trajI k

/-- `reach_outer`, unchanged, at the matrix zonotope — the strictly tighter
model, since it keeps the correlation an interval matrix throws away. -/
example {o : ℕ} (ho : 0 < o) (k : ℕ) :
    Example.lpX k ∈
      construct (Example.sysZ.reach (S := 𝒵) ⟨Example.lpR0, Example.lpU, 0, k⟩ ⟨o, ho⟩) :=
  Example.sysZ.reach_outer (S := 𝒵) ho Example.lpR0 Example.lpU Example.trajZ k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
