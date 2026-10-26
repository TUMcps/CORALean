module

public import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubmatrixMem
public import CORALean.NN.Graph.Operations.EvalSteps
public import CORALean.NN.Graph.Operations.ReducedStepsFloat
public import CORALean.NN.Graph.Theorems.MemBallSelf
public import CORALean.NN.Graph.Theorems.MemBallSuccOfMessagePassing

@[expose] public section

/-!
# The float reduced chain encloses row `v` of the whole-graph chain
Run `L` message-passing steps on node sets `κ k` that still hold `ball A v (L - k)` before step
`k`, each product `Interval.matMul` on the stored matrix as an interval, the features agreeing
with `X` on the first set: the interval `GNN.reducedStepsFloat` contains a real matrix whose
every row naming `v` is row `v` of the `L` steps on the whole graph [1, §4.3]. The rows of the
reduced chain are the exact ones (`GNN.reducedSteps_row`); the rounding is the products'.

## Inputs
* `A` – adjacency matrix
* `P` – interval message-passing matrix
* `v` – node of interest

## Hypotheses
* `hP` – interval contains the exact message-passing matrix

## Conclusion
* the float reduced chain encloses the node's row of the whole-graph chain

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {N F : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One step at a row inside the ball: the restricted product reads the same entries as the
full one. -/
private theorem aux_reducedStepsFloat_row_step {c0 c1 : ℕ} (A : Mat ℝ N N) (v : Fin N) (r : ℕ)
    (κ0 : Fin c0 → Fin N) (κ1 : Fin c1 → Fin N) (hinj : Function.Injective κ0)
    (hS : ∀ x ∈ Real.GNN.ball A v (r + 1), ∃ a, κ0 a = x) (X : Mat ℝ N F) (Y : Mat ℝ c0 F)
    (hY : ∀ a, κ0 a ∈ Real.GNN.ball A v (r + 1) → Y a = X (κ0 a)) (b : Fin c1)
    (hb : κ1 b ∈ Real.GNN.ball A v r) : -- --- CONCL ---
    (((Real.GNN.messagePassing A).submatrix κ1 κ0) * Y) b
      = (Real.GNN.messagePassing A * X) (κ1 b) := by -- --- PROOF ---
  funext g
  simp only [Matrix.mul_apply, Matrix.submatrix_apply]
  refine Fintype.sum_of_injective κ0 hinj _ _ (fun j hj => ?_) (fun a => ?_)
  · by_contra hne
    have hne' : Real.GNN.messagePassing A (κ1 b) j ≠ 0 := fun h => hne (by rw [h, zero_mul])
    obtain ⟨a, ha⟩ := hS j (Real.GNN.mem_ball_succ_of_messagePassing A v r hb hne')
    exact hj ⟨a, ha⟩
  · by_cases h0 : Real.GNN.messagePassing A (κ1 b) (κ0 a) = 0
    · simp [h0]
    · rw [hY a (Real.GNN.mem_ball_succ_of_messagePassing A v r hb h0)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem GNN.reducedStepsFloat_outer (A : Mat ℝ N N) (P : Interval (Mat 𝕋 N N))
    (hP : Real.GNN.messagePassing A ∈ P.construct) (v : Fin N) : -- --- CONCL ---
    ∀ (L : ℕ) (c : ℕ → ℕ) (κ : (k : ℕ) → Fin (c k) → Fin N)
      (_ : ∀ k, Function.Injective (κ k))
      (_ : ∀ k ≤ L, ∀ x ∈ Real.GNN.ball A v (L - k), ∃ a, κ k a = x)
      (W : ℕ → Interval (Mat 𝕋 F F)) (Wr : ℕ → Mat ℝ F F) (_ : ∀ k, Wr k ∈ (W k).construct)
      (X : Mat ℝ N F) (Yi : Interval (Mat 𝕋 (c 0) F)) (Y : Mat ℝ (c 0) F) (_ : Y ∈ Yi.construct)
      (_ : ∀ a, κ 0 a ∈ Real.GNN.ball A v L → Y a = X (κ 0 a)),
      ∃ Z ∈ (GNN.reducedStepsFloat P L c κ W Yi).construct, ∀ a, κ L a = v →
        Z a = Real.GNN.evalSteps (Real.GNN.messagePassing A) L (fun i : Fin L => Wr i)
          X v := by -- --- PROOF ---
  -- induct on the number of steps, the node sets shifting by one each time
  intro L
  induction L with
  | zero =>
      intro c κ _ _ W Wr _ X Yi Y hY hYX
      refine ⟨Y, hY, fun a ha => ?_⟩
      exact ha ▸ hYX a (ha ▸ Real.GNN.mem_ball_self A v 0)
  | succ L ih =>
      intro c κ hinj hS W Wr hW X Yi Y hY hYX
      -- the restricted real step lies in the interval step
      have hmem : (Real.GNN.messagePassing A).submatrix (κ 1) (κ 0) * Y * Wr 0
          ∈ (Interval.matMul (Interval.matMul (P.submatrix (κ 1) (κ 0)) Yi) (W 0)).construct :=
        Interval.matMul_outer _ _
          (Interval.matMul_outer _ _ (Interval.submatrix_mem hP _ _) hY) (hW 0)
      -- at a row inside the ball it is the full step's row
      have hrow : ∀ b, κ 1 b ∈ Real.GNN.ball A v L →
          ((Real.GNN.messagePassing A).submatrix (κ 1) (κ 0) * Y * Wr 0) b
            = (Real.GNN.messagePassing A * X * Wr 0) (κ 1 b) := by
        intro b hb
        have h := aux_reducedStepsFloat_row_step A v L (κ 0) (κ 1) (hinj 0)
          (hS 0 (Nat.zero_le _)) X Y hYX b hb
        have e1 : ∀ {m p : ℕ} (Q : Matrix (Fin m) (Fin p) ℝ) (R : Mat ℝ p F) (b : Fin m)
            (f : Fin F), (Q * R) b f = ∑ k, Q b k * R k f := fun _ _ _ _ => Matrix.mul_apply
        funext f
        rw [e1, e1]
        exact Finset.sum_congr rfl fun k _ => by rw [congrFun h k]
      -- the rest of the chain is the induction hypothesis on the shifted sets
      obtain ⟨Z, hZ, hZv⟩ := ih (fun k => c (k + 1)) (fun k => κ (k + 1))
        (fun k => hinj (k + 1))
        (fun k hk x hx => hS (k + 1) (by omega) x (by simpa [show L + 1 - (k + 1) = L - k by omega]
          using hx))
        (fun k => W (k + 1)) (fun k => Wr (k + 1)) (fun k => hW (k + 1))
        (Real.GNN.messagePassing A * X * Wr 0) _ _ hmem hrow
      refine ⟨Z, hZ, fun a ha => ?_⟩
      simpa [Real.GNN.evalSteps] using hZv a ha

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
