module

public import CORALean.HybridDynamics.Definitions.NonlinearReset
public import CORALean.HybridDynamics.Definitions.ResolveSource
public import CORALean.HybridDynamics.Definitions.Transition
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# `HybridDynamics/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean

section
-- The number of globally bound inputs, CORA's `numGlobalInputs = nnz(idxGlobalInput)`.
variable {N g k : ℕ} {n m p : Fin k → ℕ}


-- ==================================  `HybridAutomaton.uloc`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Intended `uloc{l}`: `u` at every location below `numLoc`.

`uloc = repmat({params.u},numLoc,1)`: every location `l < numLoc` gets `u` itself. -/
def HybridAutomaton.uloc {α : Type} (numLoc : Nat) (u : α) (l : Nat) : Option α :=
  if l < numLoc then some u else none


-- ==============================  `NonlinearReset.globalColumns`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `numGlobalInputs = nnz(idxGlobalInput)` in `nonlinearReset/resolve`: how many inputs of
the components are bound to a global input, counted with repetitions. -/
def NonlinearReset.globalColumns (inputBinds : ∀ i, Fin (m i) → ResolveSource k p g) : ℕ :=
  (Finset.univ.filter fun ij : (Σ i, Fin (m i)) =>
    ∃ a, inputBinds ij.1 ij.2 = .global a).card


-- ========================================  `scatter`  ========================================= --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The entries of `v` placed at the coordinates `σ` of a larger vector, zero elsewhere: MATLAB's
`x(σ) = v` on a zero vector. `resolve` of a reset writes a block `B(stateBinds{i}, ...)`. -/
def scatter {n N : ℕ} (σ : Fin n → Fin N) (v : Fin n → ℝ) : Fin N → ℝ :=
  fun a => ∑ r, if σ r = a then v r else 0

end

section
variable {G : ℕ → Type} {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- ==============================  `Transition.toNonlinearReset`  =============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A transition's affine reset `x ↦ W x + w` as a nonlinear reset, which ignores its input: CORA's
`linearReset` is a `nonlinearReset` with a function that happens to be affine. -/
noncomputable def Transition.toNonlinearReset (e : Transition G L 𝕋 n) : NonlinearReset n 0 n where
  f := fun x _ => e.reset x

end

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
