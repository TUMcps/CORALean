import CORALean.NN.Graph.Complexity.ConvUncertain
import CORALean.NN.Graph.Operations.GcnActSteps
import CORALean.ContSet.PolyZonotope.Real.Complexity.Dependent

/-!
# `GNN.gcnActSteps`'s count over a chain of steps

[1, Thm. 1 (generators)], the graph layers: one step takes `h` to `(P.h + 1)(h + 1)` generators
(`gcnShared_h`), the activation enclosure adds at most its `n` neurons ([1, Prop. 1],
`ActLayer.AddsAtMost`) and making them dependent moves the independent count into `h`, so `h' + 1 ≤
(P.h + 2)(h + 1) + n`. `P` is padded, never grown, so `P.h` is the same at every step. `L` steps
leave `h + 1 ≤ (P.h + 2)^L (h₀ + 1 + L ν)` for activations adding at most `ν` each.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1 (generators)], the graph layers: `L` steps leave at most `(P.h + 2)^L (h₀ + 1 + L ν)`
generators when every activation adds at most `ν`. -/
theorem GNN.gcnActSteps_h_le (ν : ℕ) (L : ℕ) :
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
    -- one step: convolve, enclose the activation, make its generators dependent
    have hstep : (((acts 0).act (GNN.gcnShared (W 0) P H hp)).dependent).h + 1
        ≤ (P.h + 2) * (H.h + 1) + ν := by
      have h1 := hadd 0 (Nat.succ_pos L) (GNN.gcnShared (W 0) P H hp)
      rw [GNN.gcnShared_h, GNN.gcnShared_q] at h1
      show ((acts 0).act (GNN.gcnShared (W 0) P H hp)).h
          + ((acts 0).act (GNN.gcnShared (W 0) P H hp)).q + 1 ≤ _
      nlinarith
    have hih := ih (fun s => c (s + 1)) (fun s => W (s + 1)) (fun s => acts (s + 1))
      (fun s hs => hadd (s + 1) (by omega))
      (P.padBack ((acts 0).act (GNN.gcnShared (W 0) P H hp)).q)
      ((acts 0).act (GNN.gcnShared (W 0) P H hp)).dependent (by
        show P.p + ((acts 0).act (GNN.gcnShared (W 0) P H hp)).q
          = ((acts 0).act (GNN.gcnShared (W 0) P H hp)).p
            + ((acts 0).act (GNN.gcnShared (W 0) P H hp)).q
        rw [(acts 0).p_eq]; rfl)
    show (GNN.gcnActSteps L _ _ _ _ _ _).h + 1 ≤ _
    refine hih.trans ?_
    -- `padBack` keeps `P.h`, and the next bound absorbs the step's `ν`
    show (P.h + 2) ^ L * (((acts 0).act (GNN.gcnShared (W 0) P H hp)).dependent.h + 1 + L * ν)
      ≤ (P.h + 2) ^ (L + 1) * (H.h + 1 + (L + 1) * ν)
    calc (P.h + 2) ^ L * (((acts 0).act (GNN.gcnShared (W 0) P H hp)).dependent.h + 1 + L * ν)
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
