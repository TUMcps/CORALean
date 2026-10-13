module

public import CORALean.NN.Definitions.Cat

@[expose] public section

/-!
# ReLU as a CAT function

[1, Sec. II (ReLU to CAT)]: `ReLU = ReLUₙ ∘ … ∘ ReLU₁`, where `ReLUᵢ` is the two cases
`case (xᵢ ≥ 0): x` and `case (xᵢ < 0): I_{i←0} · x`, `I_{i←0}` the identity with row `i` zeroed.
`reluOn l` applies `ReLUᵢ` for the coordinates of `l` in order, so `reluOn (List.finRange n)`
is the paper's composition; the composition of no `ReLUᵢ` is the identity map, which the paper
does not need to write, its chains being nonempty. Every weight is `zero` or `one`, which every
scalar stores exactly.

## References

* [1] T. Gehr, M. Mirman, D. Drachsler-Cohen, P. Tsankov, S. Chaudhuri and M. Vechev. "AI2:
      Safety and Robustness Certification of Neural Networks with Abstract Interpretation".
      IEEE S&P 2018, pp. 3-18.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ReLUᵢ` for each `i` of `l`, the head first. -/
def Cat.reluOn : List (Fin n) → Cat 𝕋 n n
  | [] => .affine (fun r c => if r = c then one else zero) (fun _ => zero)
  | i :: is =>
    let identity : Mat 𝕋 n n := fun r c => if r = c then one else zero
    let zeroRowI : Mat 𝕋 n n := fun r c => if r = c ∧ r ≠ i then one else zero
    let reluI : Cat 𝕋 n n := .cases 2 ![.nonneg i, .neg i]
      ![.affine identity (fun _ => zero), .affine zeroRowI (fun _ => zero)]
    .comp (Cat.reluOn is) reluI

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
