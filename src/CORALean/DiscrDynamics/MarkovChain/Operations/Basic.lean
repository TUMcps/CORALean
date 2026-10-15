module

public import CORALean.DiscrDynamics.MarkovChain.Definitions.Basic
public import CORALean.DiscrDynamics.MarkovChain.Operations.Gamma
public import CORALean.DiscrDynamics.GridPartition.Operations.IntersectingCells
public import Mathlib.Data.Matrix.Basic

@[expose] public section

/-!
# `DiscrDynamics/MarkovChain/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean

variable {n m : ℕ}


-- ==================================  `MarkovChain.convertT`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `aux_convert`: the per-input matrices as one matrix, block diagonal over the inputs. -/
def MarkovChain.convertT {N : ℕ} (Phi : Fin m → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    Matrix (Fin (N + 1) × Fin m) (Fin (N + 1) × Fin m) ℝ :=
  fun a b => if a.2 = b.2 then Phi a.2 a.1 b.1 else 0


-- =================================  `MarkovChain.gammaFull`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `aux_computeGammaFull`: `Gamma` as a block for each cell. -/
noncomputable def MarkovChain.gammaFull (N m : ℕ) (γ : ℝ) :
    Matrix (Fin (N + 1) × Fin m) (Fin (N + 1) × Fin m) ℝ :=
  fun a b => if a.1 = b.1 then MarkovChain.gamma m γ a.2 b.2 else 0


-- ================================  `MarkovChain.markovchain`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `markovchain(field)`: a chain with no transition matrices yet. -/
def MarkovChain.markovchain (field : GridPartition n) : MarkovChain n 0 :=
  ⟨field, ⟨Fin.elim0, Fin.elim0⟩⟩


-- ==================================  `MarkovChain.projMat`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `aux_projectionMatrix`: the sum over the inputs of a state, from the pairs to the states. -/
def MarkovChain.projMat (N m : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1) × Fin m) ℝ :=
  fun s b => if b.1 = s then 1 else 0


-- =================================  `MarkovChain.setColumn`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `T(:, s + 1) = tp; T(1, 1) = 1`: column `s` set to `tp`, the outside kept absorbing. -/
def MarkovChain.setColumn {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (s : Fin (N + 1))
    (tp : Fin (N + 1) → ℝ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun r c => if r = 0 ∧ c = 0 then 1 else if c = s then tp r else A r c


-- ===========================  `MarkovChain.transitionProbability`  ============================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `priv_transitionProbability`: the share of the points whose first intersecting cell is `s`. -/
noncomputable def MarkovChain.transitionProbability (field : GridPartition n)
    (pts : List (Vec ℝ n)) : Fin (field.nrOfCells + 1) → ℝ := fun s =>
  ((pts.filter fun x => (field.intersectingCells ⟨x, x⟩).headD 0 = s).length : ℝ) / pts.length

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
