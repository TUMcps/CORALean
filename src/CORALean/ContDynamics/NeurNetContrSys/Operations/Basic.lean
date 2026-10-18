module

public import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys

@[expose] public section

/-!
# `ContDynamics/NeurNetContrSys/Operations`: small declarations

The splits of an input matrix that the plant's input `[a; e]` needs, and the loop in which the
network drives every input; the input itself is in the main file, which states the runs with it.

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

section


-- ========================================  `leftCols`  ======================================== --
-- Authors:       Claude Opus 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---

/-- The columns of `B` that act on the network's part of the input, CORA's `B(:, 1:m)`. -/
def leftCols {α : Type} {n M m : ℕ} (hm : m ≤ M) (B : Mat α n M) : Mat α n m :=
  Matrix.of fun i j => B i (Fin.castLE hm j)

end


section
open ContSet ContDynamics
variable {n : ℕ} {P : Type} [ContDynamics P n]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =================================  `NeurNetContrSys.ofFull`  ================================= --
-- Authors:       Claude Opus 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---

/-- The loop in which the network drives every input (`m = nrOfInputs`, no external input). -/
def NeurNetContrSys.ofFull (plant : P) (contr : NeuralNetwork S n (nrOfInputs plant))
    (dt : ℝ) : NeurNetContrSys P S n :=
  ⟨plant, nrOfInputs plant, le_rfl, contr, dt⟩

end


section


-- =======================================  `rightCols`  ======================================== --
-- Authors:       Claude Opus 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---

/-- The columns of `B` that act on the external part of the input, CORA's `B(:, m+1:end)`. -/
def rightCols {α : Type} {n M m : ℕ} (hm : m ≤ M) (B : Mat α n M) : Mat α n (M - m) :=
  Matrix.of fun i j => B i ⟨m + j.val, by omega⟩

end

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
