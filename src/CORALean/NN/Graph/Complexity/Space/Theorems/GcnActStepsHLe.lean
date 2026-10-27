module

public import CORALean.NN.Graph.Complexity.Space.Theorems.GcnSharedH
public import CORALean.NN.Graph.Complexity.Space.Theorems.Basic
public import CORALean.NN.Graph.Operations.GcnActSteps
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.Theorems.DependentP
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.Theorems.Basic

@[expose] public section

/-!
# `GNN.gcnActSteps`'s count over a chain of steps

[1, Thm. 1 (generators)], the graph layers: one step takes `h` to `(P.h + 1)(h + 1)` generators
(`gcnShared_h`), the activation enclosure adds at most its `n` neurons ([1, Prop. 1],
`ActLayer.AddsAtMost`) and making them dependent moves the independent count into `h`, so `h' + 1 ≤
(P.h + 2)(h + 1) + n`. `P` is padded, never grown, so `P.h` is the same at every step. `L` steps
leave `h + 1 ≤ (P.h + 2)^L (h₀ + 1 + L ν)` for activations adding at most `ν` each.

## Inputs
* `ν` – neurons an activation adds at most
* `L` – number of steps

## Hypotheses
* none

## Conclusion
* after L steps the generator count is bounded by a power of P.h + 2 times the input's plus L ν

## References

* [1] [T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.](../../../../../../../references/2025/ladner-tmlr-gcn.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {N F₁ F₂ : ℕ}

/-- The `q` count of `gcnShared`'s result. -/
private theorem GNN.aux_gcnShared_q (W : Mat ℝ F₁ F₂) (P : PolyZonotope (Mat ℝ N N))
    (H : PolyZonotope (Mat ℝ N F₁)) (hp : P.p = H.p) : (GNN.gcnShared W P H hp).q = 0 := rfl

end


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1 (generators)], the graph layers: `L` steps leave at most `(P.h + 2)^L (h₀ + 1 + L ν)`
generators when every activation adds at most `ν`. -/
theorem GNN.gcnActSteps_h_le (ν : ℕ) (L : ℕ) : -- --- CONCL ---
    ∀ (c : ℕ → ℕ) (W : ∀ s, Mat ℝ (c s) (c (s + 1))) (acts : ∀ s, GNN.ActLayer N (c (s + 1)))
      (_ : ∀ s, s < L → (acts s).AddsAtMost ν) (P : PolyZonotope (Mat ℝ N N))
      (H : PolyZonotope (Mat ℝ N (c 0))) (hp : P.p = H.p),
      (GNN.gcnActSteps L c W acts P H hp).h + 1
        ≤ (P.h + 2) ^ L * (H.h + 1 + L * ν) := by -- --- PROOF ---
  induction L with
  | zero =>
    intro c W acts hadd P H hp
    simp [GNN.gcnActSteps]
  | succ L ih =>
    intro c W acts hadd P H hp
    -- the first layer's activation set, named once
    set A := (acts 0).act (GNN.gcnShared (W 0) P H hp) with hA
    -- one step: convolve, enclose the activation, make its generators dependent
    have hstep : A.dependent.h + 1 ≤ (P.h + 2) * (H.h + 1) + ν := by
      have h1 := hadd 0 (Nat.succ_pos L) (GNN.gcnShared (W 0) P H hp)
      rw [GNN.gcnShared_h, GNN.aux_gcnShared_q] at h1
      show A.h + A.q + 1 ≤ _
      nlinarith
    have hih := ih (fun s => c (s + 1)) (fun s => W (s + 1)) (fun s => acts (s + 1))
      (fun s hs => hadd (s + 1) (by omega))
      (P.padBack A.q)
      A.dependent (by
        show P.p + A.q = A.p + A.q
        rw [(acts 0).p_eq]; rfl)
    show (GNN.gcnActSteps L _ _ _ _ _ _).h + 1 ≤ _
    refine hih.trans ?_
    -- `padBack` keeps `P.h`, and the next bound absorbs the step's `ν`
    show (P.h + 2) ^ L * (A.dependent.h + 1 + L * ν) ≤ (P.h + 2) ^ (L + 1) * (H.h + 1 + (L + 1) * ν)
    calc (P.h + 2) ^ L * (A.dependent.h + 1 + L * ν)
        ≤ (P.h + 2) ^ L * ((P.h + 2) * (H.h + 1) + ν + L * ν) := by gcongr
      _ ≤ (P.h + 2) ^ L * ((P.h + 2) * (H.h + 1 + (L + 1) * ν)) := by
          gcongr
          have h2 : (L + 1) * ν ≤ (P.h + 2) * ((L + 1) * ν) := Nat.le_mul_of_pos_left _ (by omega)
          have h3 : (P.h + 2) * (H.h + 1 + (L + 1) * ν)
              = (P.h + 2) * (H.h + 1) + (P.h + 2) * ((L + 1) * ν) := by ring
          rw [h3]
          nlinarith [h2]
      _ = (P.h + 2) ^ (L + 1) * (H.h + 1 + (L + 1) * ν) := by ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
