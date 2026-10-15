module

public import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys

@[expose] public section

/-!
# `ContDynamics/NeurNetContrSys/Operations`: small declarations

The plant's input `[a; e]` of a closed loop and the splits of an input matrix it needs, and the
loop in which the network drives every input.

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

section


-- =======================================  `joinInput`  ======================================== --
-- Authors:       Claude Opus 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---

/-- The plant's input vector `[a; e]` of the network's part `a`, the first `m` coordinates, and the
external part `e`, the `M − m` after them. -/
def joinInput {M m : ℕ} (hm : m ≤ M) (a : Vec ℝ m) (e : Vec ℝ (M - m)) : Vec ℝ M :=
  fun i => if h : i.val < m then a ⟨i.val, h⟩ else e ⟨i.val - m, by omega⟩


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


-- =================================  `NeurNetContrSys.input`  ================================== --
-- Authors:       Claude Opus 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---

/-- The plant's input `[a; e]`: the network's output `a`, the external input `e`. -/
def NeurNetContrSys.input (sys : NeurNetContrSys P S n) (a : Vec ℝ sys.m) (e : Vec ℝ sys.nExt) :
    Vec ℝ (nrOfInputs sys.plant) :=
  joinInput sys.hm a e


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
