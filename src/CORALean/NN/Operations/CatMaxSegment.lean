module

public import CORALean.ContSet.LevelSet.Real.Operations.And
public import CORALean.NN.Operations.Basic
public import CORALean.NN.Definitions.Cat
public import CORALean.NN.Layers.Operations.SelectMat

@[expose] public section

/-!
# One max-pooling step as a CAT function

[1, Sec. II (MaxPool to CAT)]'s `fᵢ`: of a vector whose coordinates `a, …, a + k` are one
pooling window, keep the `a` before and the `b` after and replace the window by its maximum,
`fᵢ(x) = (x₁, …, x_{i-1}, x_k, x_{i+p·q}, …)`. Not affine, so a case per position `p` of the
maximum: guard `x_{a+p} ≥ x_{a+q}` for every `q`, then the selection matrix `W^(i,p)` keeping
`x_{a+p}`. The guard compares `x_{a+p}` with itself too, which the paper's Appendix A leaves out and
which always holds; it is what a conjunction of `k + 1` atoms needs to be nonempty at `k = 0`.

## Inputs
* `a` – coordinates before the window
* `k` – window size minus one
* `b` – coordinates after the window

## Output
* CAT function replacing the window by its maximum

## References

* [1] [T. Gehr, M. Mirman, D. Drachsler-Cohen, P. Tsankov, S. Chaudhuri and M. Vechev. "AI2: Safety
      and Robustness Certification of Neural Networks with Abstract Interpretation". 2018 IEEE
      Symposium on Security and Privacy (SP), 2018.](../../../../references/2018/gehr-sp-ai2.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `fᵢ`: the window `a, …, a + k` of `a + (k + 1) + b` coordinates replaced by its maximum. -/
def Cat.maxSegment (a k b : ℕ) : Cat 𝕋 (a + (k + 1) + b) (a + 1 + b) :=
  let seg : Fin (k + 1) → Fin (a + (k + 1) + b) := fun q => ⟨a + q.val, by omega⟩
  let isMax : Fin (k + 1) → CatCond (a + (k + 1) + b) := fun p =>
    Fin.foldr (k + 1) (fun q acc => (CatCond.ge (seg p) (seg q)).and_ acc) (.ge (seg p) (seg p))
  let keep : Fin (k + 1) → Fin (a + 1 + b) → Fin (a + (k + 1) + b) := fun p r =>
    ⟨if r.val < a then r.val else if r.val = a then a + p.val else r.val + k,
      by have := r.isLt; have := p.isLt; split_ifs <;> omega⟩
  .cases (k + 1) isMax fun p => .affine (selectMat (keep p)) fun _ => zero

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
