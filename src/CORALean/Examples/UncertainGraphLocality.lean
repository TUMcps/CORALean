import CORALean.NN.Graph.Theorems.EvalStepsRowBallOfAdjacencyUncertain
import CORALean.NN.Graph.Theorems.NotMemBallOfIsolated

/-!
# One subgraph serves every admissible `lam` at once

[1, §4.3]'s `evalSteps_row_ball_of_adjacency_uncertain` at a path graph `0 -- 1 -- 2 -- 3` plus an
isolated node `4`, with one uncertain edge `1 -- 3` at `lam := 0.5`. `κ` is sized against
`adjMax`'s `3`-ball, `{0, 1, 2, 3}`: node `4` carries no edge at all, so no radius ever reaches it.
The uncertain edge sits inside `adjAt`'s own `2`-ball: at `lam = 0` node `3` needs all three path
hops to reach `0`, at `lam = 0.5` the direct edge halves that, so the inner enumeration moves with
`lam` while the outer one, built from `adjMax`, does not: one `κ` licenses the whole family at
once.

## Inputs
* none

## Output
* adjacency matrix of the path with an isolated node

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

-- The certain path `0 -- 1 -- 2 -- 3`; node `4` carries none of its edges.

def Example.uglA : Mat ℝ 5 5 := GNN.edgeMat (0, 1) + GNN.edgeMat (1, 2) + GNN.edgeMat (2, 3)

-- The graph's one uncertain edge, `1 -- 3`, and one admissible weight for it.

def Example.uglU : Fin 1 → Fin 5 × Fin 5 := fun _ => (1, 3)

def Example.uglLam : Fin 1 → ℝ := fun _ => 0.5

def Example.uglW : Fin 2 → Mat ℝ 1 1 := ![!![(2 : ℝ)], !![(0.5 : ℝ)]]

def Example.uglX : Mat ℝ 5 1 := !![(1 : ℝ); 2; 3; 4; 5]

-- `κ`, sized against `adjMax`'s `3`-ball: every node but the isolated `4`.

def Example.uglKappa : Fin 4 → Fin 5 := Fin.castLE (by omega)

/-- `A`'s entries are `0` or `1`, a sum of `edgeMat`'s own nonnegativity. -/
theorem Example.uglA_nonneg (i j : Fin 5) : 0 ≤ Example.uglA i j := by -- --- PROOF ---
  simp only [Example.uglA, Matrix.add_apply]
  have h1 := GNN.edgeMat_nonneg ((0 : Fin 5), (1 : Fin 5)) i j
  have h2 := GNN.edgeMat_nonneg ((1 : Fin 5), (2 : Fin 5)) i j
  have h3 := GNN.edgeMat_nonneg ((2 : Fin 5), (3 : Fin 5)) i j
  linarith

/-- Each summand of `A` is symmetric, both orientations written at once. -/
theorem Example.uglA_symm (i j : Fin 5) :
    Example.uglA i j = Example.uglA j i := by
  simp only [Example.uglA, Matrix.add_apply, GNN.edgeMat_symm _ i j]

/-- `lam := 0.5` for the one uncertain edge is admissible. -/
theorem Example.uglLam_admissible (e : Fin 1) : 0 ≤ Example.uglLam e ∧ Example.uglLam e ≤ 1 := by
  simp [Example.uglLam]; norm_num

/-- `κ` is injective, `Fin.castLE` embedding `Fin 4` into `Fin 5`. -/
theorem Example.uglKappa_inj : Function.Injective Example.uglKappa :=
  Fin.castLE_injective _

/-- Node `4` is isolated in `adjMax`: `A` never reaches it and neither does the
one uncertain edge `1 -- 3`, so `κ`'s omission of it can never matter. -/
theorem Example.uglKappa_covers :
    GNN.ball (GNN.adjMax Example.uglA Example.uglU) 0 3
      ⊆ Finset.univ.image Example.uglKappa := by -- --- PROOF ---
  have hiso : ∀ i, GNN.adjMax Example.uglA Example.uglU i 4 = 0 := by
    intro i
    simp [GNN.adjMax, GNN.adjAt, Example.uglA, Example.uglU, GNN.edgeMat]
  intro x hx
  have hxne : x ≠ (4 : Fin 5) := fun h =>
    GNN.not_mem_ball_of_isolated _ 0 hiso (by decide) 3 (h ▸ hx)
  have hxlt : x.val < 4 := by
    have hlt5 := x.isLt
    have hne4 : x.val ≠ 4 := fun h => hxne (Fin.ext h)
    omega
  exact Finset.mem_image.mpr ⟨⟨x.val, hxlt⟩, Finset.mem_univ _, Fin.ext rfl⟩

/-- Row `0` of a two-step chain on the uncertain path, computed from `adjMax`'s
own `3`-ball alone at `lam := 0.5` — the same `κ` any other admissible `lam`
would also have used. -/
example :
    ∃ φ : Fin (GNN.ball (GNN.adjAt Example.uglA Example.uglU Example.uglLam) 0 2).card
        → Fin 4,
      GNN.evalSteps (GNN.messagePassing (GNN.adjAt Example.uglA Example.uglU Example.uglLam)) 2
          Example.uglW Example.uglX 0
        = GNN.evalSteps
            ((GNN.messagePassing
              ((GNN.adjAt Example.uglA Example.uglU Example.uglLam).submatrix
                Example.uglKappa Example.uglKappa)).submatrix φ φ)
            2 Example.uglW
            ((Example.uglX.submatrix Example.uglKappa id).submatrix φ id)
            (GNN.ballEnumIdx (GNN.adjAt Example.uglA Example.uglU Example.uglLam) 0 2) :=
  GNN.evalSteps_row_ball_of_adjacency_uncertain Example.uglA Example.uglU Example.uglA_nonneg
    Example.uglA_symm Example.uglLam_admissible 0 2 Example.uglKappa Example.uglKappa_inj
    Example.uglKappa_covers Example.uglW Example.uglX

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
