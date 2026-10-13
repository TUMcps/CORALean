import CORALean.NN.Definitions.CatDomain

/-!
# The abstract transformer of a CAT function

[1, Fig. 8], one line per form: an affine map is the domain's `Aff`; a list of cases is the
join, over the cases, of each case's transformer applied to the element met with its guard;
a composition is the composition of the transformers. The join of no case is `⊥`, and the
cases are joined right to left, which the paper leaves open, `⊔` being commutative in it.

The meet with the `i`-th guard does not exclude the earlier guards, as `Cat.Eval` does: an
element met with fewer constraints is only larger, so nothing is lost but precision, exactly as
in the paper.

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

variable {𝕋 : Type} {S : ℕ → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `T#_f`, by [1, Fig. 8]. -/
def Cat.transformer (D : CatDomain 𝕋 S) : {m n : ℕ} → Cat 𝕋 m n → S m → S n
  | _, _, .affine W b, a =>
    let aff := D.aff a W b
    aff
  | _, n, .cases k E f, a =>
    let caseᵢ := fun i : Fin k => Cat.transformer D (f i) (D.meet a (E i))
    let joined := Fin.foldr k (fun i acc => D.join (caseᵢ i) acc) (D.bot n)
    joined
  | _, _, .comp f₂ f₁, a =>
    let inner := Cat.transformer D f₁ a
    let outer := Cat.transformer D f₂ inner
    outer

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
