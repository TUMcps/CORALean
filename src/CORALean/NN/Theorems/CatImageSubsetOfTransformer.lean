import CORALean.NN.Theorems.CatTransformerOuter

/-!
# Proving a property by abstract interpretation

[1, Sec. IV-B (robustness)]: a network `N`, written as a CAT function, satisfies `(X, C)` when
`γ(T#_N(α(X))) ⊆ C`, by [1, Thm. 1] and the property of `α`. `α(X)` is any abstract element
whose concretization contains `X`; local robustness is the case `C = C_L`, and nothing here
depends on what `C` is.

## References

* [1] T. Gehr, M. Mirman, D. Drachsler-Cohen, P. Tsankov, S. Chaudhuri and M. Vechev. "AI2:
      Safety and Robustness Certification of Neural Networks with Abstract Interpretation".
      IEEE S&P 2018, pp. 3-18.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {S : ℕ → Type}
  [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every output of `N` on `X` lies in `C` once the abstract output does. -/
theorem Cat.image_subset_of_transformer (D : CatDomain 𝕋 S) (hD : D.Sound) {m n : ℕ}
    (N : Cat 𝕋 m n) {X : Set (Vec ℝ m)} {C : Set (Vec ℝ n)} (a : S m)
    (hα : X ⊆ construct a) (hC : construct (N.transformer D a) ⊆ C) : N.image X ⊆ C :=
  fun _ ⟨x, hx, hxy⟩ => hC (Cat.transformer_outer D hD N a ⟨x, hα hx, hxy⟩)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
