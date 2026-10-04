import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import CORALean.Global.Tensor

/-!
# Reachable sets of any model, and the general linear output approximation

`reachSetOf τ x∗ X₀ u∗ U` is [1, Def. 5]: every output `τ(x₀, u₀:ₖ)` from an initial state in
`x∗ ⊕ X₀` and inputs in `u∗ᵢ ⊕ Uᵢ`, the inputs chosen independently per step. `τ` is any
output map — a state-space model's, an input-output model's — fixed at one step `k`.

`glo` is [1, Def. 7]'s `τ̄(x₀, u₀:ₖ) = ȳ + C̄ (x₀ - x̄₀) + ∑ᵢ D̄ᵢ (uᵢ - ūᵢ)`, and `gloSet` is
(7)'s `Ȳ = ȳ ⊕ C̄(-c_x ⊕ X₀) ⊕ ⨁ᵢ D̄ᵢ(-c_u ⊕ Uᵢ)`. `prodJac A k m` is the product
`∏_{l=1}^m A_{k-l} = A_{k-1} ⋯ A_{k-m}` of (11b), the latest factor leftmost.

## References

* [1] L. Lützow and M. Althoff. "Reachset-Conformant System Identification". IEEE
      Transactions on Automatic Control, 71(5):3014-3029, 2026.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise

variable {n p q k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Def. 5]: the outputs `τ` reaches from `x∗ ⊕ X₀` under inputs in `u∗ᵢ ⊕ Uᵢ`. -/
def Conform.reachSetOf (τ : Vec ℝ n → (Fin (k + 1) → Vec ℝ p) → Vec ℝ q) (xs : Vec ℝ n)
    (X0 : Set (Vec ℝ n)) (us : Fin (k + 1) → Vec ℝ p) (U : Fin (k + 1) → Set (Vec ℝ p)) :
    Set (Vec ℝ q) :=
  {y | ∃ x0 ∈ {xs} + X0, ∃ u : Fin (k + 1) → Vec ℝ p, (∀ i, u i ∈ {us i} + U i) ∧ y = τ x0 u}

/-- [1, Def. 7]: the GLO approximation along the reference `(x̄₀, ū)`. -/
noncomputable def Conform.glo (yb : Vec ℝ q) (Cb : Mat ℝ q n) (Db : Fin (k + 1) → Mat ℝ q p)
    (xb : Vec ℝ n) (ub : Fin (k + 1) → Vec ℝ p) (x0 : Vec ℝ n) (u : Fin (k + 1) → Vec ℝ p) :
    Vec ℝ q :=
  yb + Cb *ᵥ (x0 - xb) + ∑ i, Db i *ᵥ (u i - ub i)

/-- (7): `Ȳ`. -/
def Conform.gloSet (yb : Vec ℝ q) (Cb : Mat ℝ q n) (Db : Fin (k + 1) → Mat ℝ q p)
    (cx : Vec ℝ n) (X0 : Set (Vec ℝ n)) (cu : Vec ℝ p) (U : Fin (k + 1) → Set (Vec ℝ p)) :
    Set (Vec ℝ q) :=
  {yb} + (fun x => Cb *ᵥ x) '' ({-cx} + X0) + ∑ i, (fun v => Db i *ᵥ v) '' ({-cu} + U i)

/-- `∏_{l=1}^m A_{k-l}`, ordered `A_{k-1} ⋯ A_{k-m}` as (11b) multiplies. -/
noncomputable def Conform.prodJac (A : ℕ → Mat ℝ n n) (k m : ℕ) : Mat ℝ n n :=
  ((List.range m).map fun l => A (k - 1 - l)).prod

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
