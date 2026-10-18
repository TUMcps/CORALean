module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# [1, Prop. 3]'s printed generators do not enclose `I + At + ½(At)²`

[1, Prop. 3] prints `L^(0)(t) = I + G^(0)t + (G^(0)² + Σ ½G^(i)²)t²`,
`L^(j)(t) = G^(j)t + (G^(0)G^(j) + G^(j)G^(0))t²`, `L^(κ+j)(t) = ½G^(j)²t²` and
`L^(2κ+l)(t) = (G^(j)G^(k) + G^(k)G^(j))t²` for `{I + At + ½(At)² | A ∈ A_Z}`: every
quadratic coefficient is twice what the expansion of `A²` needs, so they enclose
`I + At + (At)²` and not the stated set. One dimension is enough: `A_Z = [0.9, 1.1]`
(`c = 1`, `G = 1/10`) and `t = 1`. The printed zonotope is `3.005 ± (0.3 + 0.005)`, so it
starts at `2.7`, while `A = 0.9` gives `I + A + ½A² = 2.305`. The pair block is padded
with zeros to `κ²` generators exactly as `Zonotope.quadTaylor` does, which changes no set.

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 3] as printed: the zonotope with the printed `L^(j)` does not enclose the
second-order Taylor sum of every matrix a matrix zonotope denotes. -/
theorem Zonotope.quadTaylor_printed_counterexample : -- --- STMT ---
    ¬ ∀ (n : ℕ) (A_Z : Zonotope (Mat ℝ n n)) (t : ℝ),
      (fun A => (1 : Mat ℝ n n) + t • A + (t ^ 2 / 2) • (A * A)) '' A_Z.construct
        ⊆ ({ h := A_Z.h + A_Z.h + A_Z.h * A_Z.h
             c := (1 : Mat ℝ n n) + t • A_Z.c + t ^ 2 • (A_Z.c * A_Z.c)
               + (t ^ 2 / 2) • ∑ i, A_Z.G i * A_Z.G i
             G := Fin.append
               (Fin.append
                 (fun i => t • A_Z.G i + t ^ 2 • (A_Z.c * A_Z.G i + A_Z.G i * A_Z.c))
                 (fun j => (t ^ 2 / 2) • (A_Z.G j * A_Z.G j)))
               (fun k =>
                 let ij := finProdFinEquiv.symm k
                 if ij.1 < ij.2 then t ^ 2 • (A_Z.G ij.1 * A_Z.G ij.2 + A_Z.G ij.2 * A_Z.G ij.1)
                 else 0) } : Zonotope (Mat ℝ n n)).construct := by -- --- PROOF ---
  intro h
  have hA : (!![9 / 10] : Mat ℝ 1 1) ∈ (⟨1, !![1], fun _ => !![1 / 10]⟩ :
      Zonotope (Mat ℝ 1 1)).construct :=
    ⟨fun _ => -1, fun _ => by simp, by ext i j; fin_cases i; fin_cases j; norm_num⟩
  obtain ⟨β, hβ, heq⟩ := h 1 ⟨1, !![1], fun _ => !![1 / 10]⟩ 1 ⟨_, hA, rfl⟩
  have h0 := congrFun (congrFun heq 0) 0
  have b0 := abs_le.mp (hβ 0)
  have b1 := abs_le.mp (hβ 1)
  simp [Fin.sum_univ_succ, Fin.append, Fin.addCases, finProdFinEquiv, Fin.divNat, Fin.modNat] at h0
  norm_num at h0
  linarith [b0.1, b1.1]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
