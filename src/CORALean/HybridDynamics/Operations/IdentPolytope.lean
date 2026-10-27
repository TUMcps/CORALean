module

public import CORALean.Global.Tensor
public import CORALean.ContSet.HPolytope.Real.Operations.RowLin

@[expose] public section

/-!
# The polytope `⟨C, d⟩_P` as an H-polytope

[1, Def. 2]: a polytope `⟨C, d⟩_P = {x | C x ≤ d}` of the paper's identification, given as the
list of its rows `(cᵢ, dᵢ)`, as the repository's H-polytope with those inequalities.

## Inputs
* `cs` – polytope rows

## Output
* half-space polytope of the rows

## References

* [1] [N. Kochdumper, M. A. Foughali, P. Habermehl and E. Asarin. "Robust Identification of Hybrid
      Automata from Noisy Data". Proceedings of the 28th ACM International Conference on Hybrid
      Systems: Computation and Control,
      2025.](../../../../references/2025/kochdumper-hscc-hybrid-automata-identification.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Def. 2]: the polytope `⟨C, d⟩_P` of the rows `cs = [(c₁, d₁), …]`, `C` having rows
`cᵢ`, as the repository's H-polytope: `construct` is `{x | cᵢᵀx ≤ dᵢ for every row}`. -/
def IdentHA.polytope (cs : List (Vec ℝ n × ℝ)) : Real.HPolytope (Vec ℝ n) where
  m := cs.length
  A := Real.HPolytope.rowLin (Matrix.of fun i => (cs.get i).1)
  b := fun i => (cs.get i).2
  me := 0
  Ae := Fin.elim0
  be := Fin.elim0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
