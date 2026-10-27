module

public import CORALean.Global.Tensor
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# Hybrid automata with nonlinear flows, guards and resets

[1, Def. 1]: `p` modes with flows `ẋ = fᵢ(x, u)` and invariant sets `Sᵢ ⊂ ℝⁿ`, and `q` transitions
`Tᵢ = ⟨Gᵢ, rᵢ(·), sᵢ, dᵢ⟩` with a guard set, a reset `rᵢ : ℝⁿ → ℝⁿ` and the source and target
modes. `HybridAutomaton` is the linear case CORA's reachability runs on. `IsRunAt` is the evolution
[1] describes in words, with the time it lasts: flow in mode `m` with inputs in `U`, staying in
`S_m`, until the state is in the guard of a transition out of `m`, which is taken at once, the
reset applied. Urgency is the "is taken" of the text. A stay is a Carathéodory run of `fᵢ` with the
invariant kept over the whole of it, the semantics [1, Sec. 3.2] computes against.

## References

* [1] [N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear Guard
      Sets". Proceedings of the 23rd International Conference on Hybrid Systems: Computation and
      Control, 2020.](../../../../references/2020/kochdumper-hscc-nonlinear-guards.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open MeasureTheory


-- ========================================  MAIN TYPE  ========================================= --

/-- [1, Def. 1]: a transition `⟨G, r(·), s, d⟩`. -/
structure NonlinTransition (n p : ℕ) where
  G : Set (Vec ℝ n)
  r : Vec ℝ n → Vec ℝ n
  s : Fin p
  d : Fin p

/-- [1, Def. 1]: the flows `F`, the invariants `S` and the transitions `T`. -/
structure NonlinHybridAutomaton (n m p q : ℕ) where
  F : Fin p → Vec ℝ n → Vec ℝ m → Vec ℝ n
  S : Fin p → Set (Vec ℝ n)
  T : Fin q → NonlinTransition n p

variable {n m p q : ℕ}

/-- A stay of length `τ` in mode `i`: the flow `fᵢ` under inputs in `U`, inside `Sᵢ`, meeting
no guard out of `i` before its end. -/
structure NonlinHybridAutomaton.IsStay (H : NonlinHybridAutomaton n m p q) (U : Set (Vec ℝ m))
    (i : Fin p) (τ : ℝ) (x : ℝ → Vec ℝ n) (u : ℝ → Vec ℝ m) : Prop where
  nonneg : 0 ≤ τ
  input (t : ℝ) (ht : t ∈ Set.Icc 0 τ) : u t ∈ U
  meas : AEStronglyMeasurable (fun t => H.F i (x t) (u t)) (volume.restrict (Set.Icc 0 τ))
  integrable (t : ℝ) (ht : t ∈ Set.Icc 0 τ) :
    IntervalIntegrable (fun s => H.F i (x s) (u s)) volume 0 t
  cont : ContinuousOn x (Set.Icc 0 τ)
  flow (t : ℝ) (ht : t ∈ Set.Icc 0 τ) : x t = x 0 + ∫ s in (0:ℝ)..t, H.F i (x s) (u s)
  invariant (t : ℝ) (ht : t ∈ Set.Icc 0 τ) : x t ∈ H.S i
  urgent (t : ℝ) (ht : t ∈ Set.Ico 0 τ) (j : Fin q) (hj : (H.T j).s = i) : x t ∉ (H.T j).G

/-- A run from `x` in mode `i` to `y` in mode `i'`, lasting `t` in all. -/
inductive NonlinHybridAutomaton.IsRunAt (H : NonlinHybridAutomaton n m p q) (U : Set (Vec ℝ m)) :
    ℝ → Fin p → Vec ℝ n → Fin p → Vec ℝ n → Prop where
  | flow {i : Fin p} {τ : ℝ} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} (h : H.IsStay U i τ x u) :
      H.IsRunAt U τ i (x 0) i (x τ)
  | jump {t τ : ℝ} {i i' : Fin p} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {y : Vec ℝ n}
      {j : Fin q} (h : H.IsStay U i τ x u) (hs : (H.T j).s = i) (hguard : x τ ∈ (H.T j).G)
      (rest : H.IsRunAt U t (H.T j).d ((H.T j).r (x τ)) i' y) :
      H.IsRunAt U (τ + t) i (x 0) i' y

/-- [1, Def. 2]: `Rᵉ(t)`, every state `ξ(t, x₀, m₀, u(·))` of a run from `x₀ ∈ X₀` in mode
`m₀` with inputs in `U`, in whichever mode it is at time `t`. -/
def NonlinHybridAutomaton.reachSetExact (H : NonlinHybridAutomaton n m p q) (X₀ : Set (Vec ℝ n))
    (m₀ : Fin p) (U : Set (Vec ℝ m)) (t : ℝ) : Set (Vec ℝ n) :=
  {y | ∃ x₀ ∈ X₀, ∃ i, H.IsRunAt U t m₀ x₀ i y}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
