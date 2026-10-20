module

public import CORALean.ContDynamics.Interfaces
public import CORALean.NN.NeuralNetwork

@[expose] public section

/-!
# A neural network in the loop of a plant: the representation

CORA's `neurNetContrSys(sys, nn, dt)`: one class over every plant, any `ContDynamics`, the
network's output `u = π(x(i dt))` computed at the sampling instants and *held* over the control
period `dt`. [1, Alg. 2]'s system is `ẋ(t) = f(x(t), u_c(x(t), t), w(t))`, `w(t) ∈ W`. The
network drives the first `m` inputs of the plant; the remaining `nExt = nrOfInputs − m` are
external, CORA's `n_ext`, over `U_ext`, and the plant receives `U_nn × U_ext` (`inputSet`). With
`nExt = 0` (`ofFull`) the network drives every input. CORA's loop at a linear plant drops `E`.
The runs are `IsTrajectory`: on period `i` a run of the plant, shifted to `i dt`, under the held
input `[π(x(i dt)); v]`. The discrete-time loop is `NeurNetContrSysDT`.

## References

* [1] N. Kochdumper et al. "Open- and Closed-Loop Neural Network Verification
      using Polynomial Zonotopes". arXiv:2207.02715, 2022.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   18-October-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet ContDynamics

variable {n : ℕ} {P : Type} [ContDynamics P n]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

/-- The plant and the network controlling its first `m` inputs, the rest external, and the control
period `dt`: CORA's `neurNetContrSys(sys, nn, dt)`. -/
structure NeurNetContrSys (P : Type) (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] (n : ℕ)
    [ContDynamics P n] where
  plant : P
  m : ℕ
  hm : m ≤ nrOfInputs plant
  contr : NeuralNetwork S n m
  dt : ℝ

/-- CORA's `n_ext`: the plant's inputs the network does not drive. -/
abbrev NeurNetContrSys.nExt (sys : NeurNetContrSys P S n) : ℕ := nrOfInputs sys.plant - sys.m

/-- The plant's input vector `[a; e]` of the network's part `a`, the first `m` coordinates, and the
external part `e`, the `M − m` after them. -/
def joinInput {M m : ℕ} (hm : m ≤ M) (a : Vec ℝ m) (e : Vec ℝ (M - m)) : Vec ℝ M :=
  fun i => if h : i.val < m then a ⟨i.val, h⟩ else e ⟨i.val - m, by omega⟩

/-- The plant's input `[a; e]`: the network's output `a`, the external input `e`. -/
def NeurNetContrSys.input (sys : NeurNetContrSys P S n) (a : Vec ℝ sys.m) (e : Vec ℝ sys.nExt) :
    Vec ℝ (nrOfInputs sys.plant) :=
  joinInput sys.hm a e

/-- The plant's input set `U_nn × U_ext`. -/
def NeurNetContrSys.inputSet (sys : NeurNetContrSys P S n) (U_nn : Set (Vec ℝ sys.m))
    (U_ext : Set (Vec ℝ sys.nExt)) : Set (Vec ℝ (nrOfInputs sys.plant)) :=
  {u | ∃ a ∈ U_nn, ∃ e ∈ U_ext, u = sys.input a e}

/-- The full run over `H` control periods of length `sys.dt` from `R₀`: on period `i`, a run of
the plant under the held `π(x(i dt))`, an external input `v` in `U_ext` and a disturbance in `W`. -/
structure NeurNetContrSys.IsTrajectory (sys : NeurNetContrSys P S n)
    (π : Vec ℝ n → Vec ℝ sys.m) (H : ℕ) (R₀ : S n)
    (U_ext : Set (Vec ℝ sys.nExt)) (W : Set (Vec ℝ (nrOfDisturbances sys.plant)))
    (x : ℝ → Vec ℝ n) (v : ℝ → Vec ℝ sys.nExt)
    (w : ℝ → Vec ℝ (nrOfDisturbances sys.plant)) : Prop where
  init : x 0 ∈ construct R₀
  flow (i : ℕ) (hi : i < H) :
    ContDynamics.IsTrajectory sys.plant (Set.Icc 0 sys.dt) Set.univ
      (sys.inputSet {π (x ((i : ℝ) * sys.dt))} U_ext) W
      (fun t => x ((i : ℝ) * sys.dt + t))
      (fun t => sys.input (π (x ((i : ℝ) * sys.dt))) (v ((i : ℝ) * sys.dt + t)))
      (fun t => w ((i : ℝ) * sys.dt + t))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
