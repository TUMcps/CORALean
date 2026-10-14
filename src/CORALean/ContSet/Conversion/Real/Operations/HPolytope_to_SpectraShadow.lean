module

public import CORALean.Global.BlockDiag
public import CORALean.ContSet.HPolytope.Real.HPolytope
public import CORALean.ContSet.SpectraShadow.Real.SpectraShadow
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

/-!
# A polytope as a spectrahedral shadow — the construction

`HPolytope.stackedRows`, `HPolytope.stackedBounds` and `HPolytope.spectraShadow` are the
constructions; `HPolytope_to_SpectraShadow` states and proves what they guarantee.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The stacked rows `C = [A; Ae; -Ae]`. -/
def HPolytope.stackedRows (P : HPolytope (Vec ℝ n)) : Fin (P.m + P.me + P.me) → (Vec ℝ n →ₗ[ℝ] ℝ) :=
  Fin.append (Fin.append P.A P.Ae) fun i => -(P.Ae i)

/-- The stacked right-hand side `d = [b; be; -be]`. -/
def HPolytope.stackedBounds (P : HPolytope (Vec ℝ n)) : Fin (P.m + P.me + P.me) → ℝ :=
  Fin.append (Fin.append P.b P.be) fun i => -(P.be i)

def HPolytope.spectraShadow (P : HPolytope (Vec ℝ n)) : SpectraShadow (Vec ℝ n) where
  k := P.m + P.me + P.me
  m := n
  A₀ := diagonal P.stackedBounds
  A := fun i => diagonal fun j => -(P.stackedRows j (Pi.single i 1 : Fin n → ℝ))
  c := 0
  G := fun i => (Pi.single i 1 : Fin n → ℝ)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
