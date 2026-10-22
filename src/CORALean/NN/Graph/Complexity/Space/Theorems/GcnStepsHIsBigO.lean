module

public import CORALean.NN.Graph.Complexity.Space.Theorems.GcnSharedH
public import CORALean.NN.Graph.Complexity.Space.Theorems.Basic
public import CORALean.NN.Graph.Operations.GcnSteps
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import CORALean.ContSet.PolyZonotope.Real.Operations.PadBack
public import CORALean.ContSet.PolyZonotope.Real.Operations.PadFront
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Tactic.Positivity
public import CORALean.NN.Graph.Complexity.Space.Theorems.MessagePassingEnclosureHLe
public import CORALean.NN.Graph.Complexity.Space.Theorems.MessagePassingEnclosureP
public import CORALean.NN.Graph.Complexity.Space.Theorems.MessagePassingEnclosureHIsBigO

@[expose] public section

/-!
# `GNN.gcnSteps_h_isBigO`

[1, Thm. 1] for the graph layers: `L` message-passing steps at an uncertain
graph are polynomial of degree `3L` in the number of uncertain edges.

## Inputs
* `R` – relaxation of the activations
* `A` – adjacency matrix
* `U` – uncertain edges for each edge count
* `L` – number of steps
* `W` – weights of the steps
* `X` – input polynomial zonotope

## Hypotheses
* none

## Conclusion
* the generator count is big-O of the edge count to the power 3L

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   13-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N F m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `L` message-passing steps at one uncertain graph multiply the generator
count by at most `P.h + 2` each. -/
theorem GNN.aux_gcnSteps_h_le (P : PolyZonotope (Mat ℝ N N)) (L : ℕ) : -- --- CONCL ---
    ∀ (W : Fin L → Mat ℝ F F) (H : PolyZonotope (Mat ℝ N F)) (hp : P.p = H.p),
      (GNN.gcnSteps P L W H hp).h + 1 ≤ (P.h + 2) ^ L * (H.h + 1) := by -- --- PROOF ---
  induction L with
  | zero =>
    -- no step at all: the chain is its own input
    intro _ H _
    show H.h + 1 ≤ (P.h + 2) ^ 0 * (H.h + 1)
    simp
  | succ L ih =>
    intro W H hp
    -- the step's own count, with the `+1` folded into the base of the power
    have hstep : (GNN.gcnShared (W 0) P H hp).h + 1 ≤ (P.h + 2) * (H.h + 1) := by
      rw [GNN.gcnShared_h]
      nlinarith
    have hih := ih (fun i => W i.succ) (GNN.gcnShared (W 0) P H hp) rfl
    calc (GNN.gcnSteps P (L + 1) W H hp).h + 1
        ≤ (P.h + 2) ^ L * ((GNN.gcnShared (W 0) P H hp).h + 1) := hih
      _ ≤ (P.h + 2) ^ L * ((P.h + 2) * (H.h + 1)) := Nat.mul_le_mul (le_refl _) hstep
      _ = (P.h + 2) ^ (L + 1) * (H.h + 1) := by ring


/-- The chain's count against the cubic in `m`, before any cast: the constant
collects the node count and the input set, the growth is the power of `m`. -/
theorem aux_gcnSteps_h_le_pow (R : Relaxation ℝ) (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) (L : ℕ) (W : Fin L → Mat ℝ F F)
    (X : PolyZonotope (Mat ℝ N F)) (hm : 1 ≤ m) : -- --- CONCL ---
    (GNN.gcnSteps ((GNN.messagePassingEnclosure R A U).padBack X.p) L W
        (X.padFront (GNN.messagePassingEnclosure R A U).p) rfl).h
      ≤ (((N + 2) * (N + 2) + 1) * (N + 2) + 2) ^ L * (X.h + 1) * m ^ (3 * L) := by -- --- PROOF ---
  -- the base of the power: `𝒫`'s own cubic, with the `+2` a step costs folded in
  have hmpe : (GNN.messagePassingEnclosure R A U).h + 2
      ≤ (((N + 2) * (N + 2) + 1) * (N + 2) + 2) * m ^ 3 := by
    have h := GNN.messagePassingEnclosure_h_le R A U hm
    have hc : 1 ≤ m ^ 3 := Nat.one_le_pow 3 m (by omega)
    calc (GNN.messagePassingEnclosure R A U).h + 2
        ≤ ((N + 2) * (N + 2) + 1) * (N + 2) * m ^ 3 + 2 * m ^ 3 := by linarith
      _ = (((N + 2) * (N + 2) + 1) * (N + 2) + 2) * m ^ 3 := by ring
  -- padding moves the factor count only, so the chain's bound reads off `𝒫` and `X`
  have hP : ((GNN.messagePassingEnclosure R A U).padBack X.p).h
      = (GNN.messagePassingEnclosure R A U).h := rfl
  have hH : (X.padFront (GNN.messagePassingEnclosure R A U).p).h = X.h := rfl
  have hchain := GNN.aux_gcnSteps_h_le ((GNN.messagePassingEnclosure R A U).padBack X.p) L W
    (X.padFront (GNN.messagePassingEnclosure R A U).p) rfl
  rw [hP, hH] at hchain
  calc (GNN.gcnSteps ((GNN.messagePassingEnclosure R A U).padBack X.p) L W
          (X.padFront (GNN.messagePassingEnclosure R A U).p) rfl).h
      ≤ ((GNN.messagePassingEnclosure R A U).h + 2) ^ L * (X.h + 1) :=
        le_trans (Nat.le_succ _) hchain
    _ ≤ ((((N + 2) * (N + 2) + 1) * (N + 2) + 2) * m ^ 3) ^ L * (X.h + 1) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hmpe L) (le_refl _)
    _ = (((N + 2) * (N + 2) + 1) * (N + 2) + 2) ^ L * (X.h + 1) * m ^ (3 * L) := by
        rw [mul_pow, ← pow_mul]
        ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1] for the graph layers: `L` message-passing steps at an uncertain
graph are polynomial of degree `3L` in the number of uncertain edges. -/
theorem GNN.gcnSteps_h_isBigO (R : Relaxation ℝ) (A : Mat ℝ N N)
    (U : ∀ m : ℕ, Fin m → Fin N × Fin N) (L : ℕ) (W : Fin L → Mat ℝ F F)
    (X : PolyZonotope (Mat ℝ N F)) : -- --- CONCL ---
    (fun m : ℕ => (((GNN.gcnSteps ((GNN.messagePassingEnclosure R A (U m)).padBack X.p) L W
        (X.padFront (GNN.messagePassingEnclosure R A (U m)).p) rfl).h : ℕ) : ℝ))
      =O[Filter.atTop] fun m : ℕ => (m : ℝ) ^ (3 * L) := by -- --- PROOF ---
  apply Asymptotics.IsBigO.of_bound
    (((((N + 2) * (N + 2) + 1) * (N + 2) + 2) ^ L * (X.h + 1) : ℕ) : ℝ)
  filter_upwards [Filter.eventually_ge_atTop 1] with m hm
  -- the whole bound is a statement about naturals, so the cast is the last step
  have h := aux_gcnSteps_h_le_pow R A (U m) L W X hm
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  exact_mod_cast h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
