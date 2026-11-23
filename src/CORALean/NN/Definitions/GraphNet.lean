module

public import CORALean.NN.Operations.GraphEnvCons
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Graph networks

CORA.cpp's networks with sources and residuals (`NeuralNetwork::source`, `Layer::residuals`): a
layer reads one earlier output through its weights, adds its bias and further earlier outputs
through their maps (a ResNet's skip connection), and applies its activation. `GraphNet Γ k` is
the rest of a network after the outputs `Γ` (`GraphEnv`), and `eval` the exact network. The
product `[a; b] ↦ [a ⊙ b; 0]` of the halves is CORA.cpp's `Activation::product`, which keeps the
dimension and zeroes the second half.

-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

namespace Real

/-- A residual of a layer with `m` outputs: the earlier output `src` through the map `R`. -/
structure GraphResidual (Γ : List ℕ) (m : ℕ) where
  src : Fin Γ.length
  R : Mat ℝ m (Γ.get src)

/-- The activation of a layer: the identity, `σ` at every neuron, or the product of the halves. -/
inductive GraphAct : ℕ → Type where
  | identity {m : ℕ} : GraphAct m
  | elementwise {m : ℕ} (σ : ℝ → ℝ) : GraphAct m
  | product (n : ℕ) : GraphAct (n + n)

/-- A layer with `m` outputs after the outputs `Γ`: the source `src` through `W`, the bias `b`,
the residuals, and the activation. -/
structure GraphLayer (Γ : List ℕ) (m : ℕ) where
  src : Fin Γ.length
  W : Mat ℝ m (Γ.get src)
  b : Vec ℝ m
  residuals : List (GraphResidual Γ m)
  act : GraphAct m

/-- The layers after the outputs `Γ`, the last output of dimension `k`. -/
inductive GraphNet : List ℕ → ℕ → Type where
  | done {k : ℕ} {Γ : List ℕ} : GraphNet (k :: Γ) k
  | layer {Γ : List ℕ} {m k : ℕ} (L : GraphLayer Γ m) (rest : GraphNet (m :: Γ) k) : GraphNet Γ k

/-- The activation at the point `z`. -/
noncomputable def GraphAct.apply : {m : ℕ} → GraphAct m → Vec ℝ m → Vec ℝ m
  | _, .identity, z => z
  | _, .elementwise σ, z => fun i => σ (z i)
  | _, .product n, z =>
      Fin.addCases (fun i => z (Fin.castAdd n i) * z (Fin.natAdd n i)) (fun _ => 0)

/-- The layer's input `W x_src + b + ∑ R x_r`, before the activation. -/
noncomputable def GraphLayer.preact {Γ : List ℕ} {m : ℕ} (L : GraphLayer Γ m)
    (e : GraphEnv (Vec ℝ) Γ) : Vec ℝ m :=
  fun i => ∑ j, L.W i j * e L.src j + L.b i
    + (L.residuals.map fun r => ∑ j, r.R i j * e r.src j).sum

/-- The exact network: each layer's output in front of the earlier ones, then the last output. -/
noncomputable def GraphNet.eval : {Γ : List ℕ} → {k : ℕ} → GraphNet Γ k → GraphEnv (Vec ℝ) Γ →
    Vec ℝ k
  | _, _, .done, e => e ⟨0, Nat.succ_pos _⟩
  | _, _, .layer L rest, e => rest.eval (GraphEnv.cons (L.act.apply (L.preact e)) e)

end Real

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
