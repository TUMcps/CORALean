module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.NN.Definitions.Cat

@[expose] public section

/-!
# What AI2 asks of an abstract domain

[1, Thm. 1]: an abstract transformer for every CAT function needs a domain with an affine
transformer `Aff`, a meet `⊓` with a guard, a join `⊔` and a least element `⊥`, each sound.
The abstract elements of dimension `n` are a representation `S n`, and `construct` is the
concretization `γ` of [1, Sec. III (transformers)]; `CatDomain` is the four operations and
`CatDomain.Sound` the inclusions the paper assumes of them, an operation meeting its inclusion
being an abstract transformer of that operation in the paper's sense.

The paper also assumes `⊥ ⊓ E = ⊥` and `a ⊔ ⊥ = a`; neither is needed for soundness, so neither
is asked. `γ(⊥) = ∅` is asked, being what a containment proof by meet reads.

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

open Matrix ContSet Float Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ========================================  MAIN TYPE  ========================================= --

/-- `Aff`, `⊓` with a guard, `⊔` and `⊥` on the representation `S`. -/
structure CatDomain (𝕋 : Type) (S : ℕ → Type) where
  aff {m n : ℕ} : S m → Mat 𝕋 n m → Vec 𝕋 n → S n
  meet {n : ℕ} : S n → CatCond n → S n
  join {n : ℕ} : S n → S n → S n
  bot (n : ℕ) : S n

/-- The inclusions [1, Thm. 1] assumes, `γ` being `construct`. -/
structure CatDomain.Sound {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
    (D : CatDomain 𝕋 S) : Prop where
  aff_outer {m n : ℕ} (a : S m) (W : Mat 𝕋 n m) (b : Vec 𝕋 n) :
    (fun x => toRealMat W *ᵥ x + toRealVec b) '' construct a ⊆ construct (D.aff a W b)
  meet_outer {n : ℕ} (a : S n) (E : CatCond n) :
    construct a ∩ {x | E.Holds x} ⊆ construct (D.meet a E)
  join_outer {n : ℕ} (a₁ a₂ : S n) : construct a₁ ∪ construct a₂ ⊆ construct (D.join a₁ a₂)
  bot_empty (n : ℕ) : construct (D.bot n) = ∅

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
