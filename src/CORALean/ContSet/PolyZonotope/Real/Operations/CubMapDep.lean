module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Bilin
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadBilin
public import CORALean.Global.Tensor
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# `PolyZonotope.cubMapDepOn`

CORA's `@polyZonotope/cubMap` on a set whose coefficients are all dependent: the cubic map
`{ (xᵀ T x) * x | x ∈ pZ }` of a polynomial zonotope is a polynomial zonotope again, exactly,
for the reason `quadMap` is: shared factors make `mᵢ mⱼ mₖ` a monomial at `Eᵢ + Eⱼ + Eₖ`.
Here the pairs are all the ordered ones (as in `quadMap`: the same polynomial, symmetrization
and `removeRedundantExponents` not modelled), and the two steps are two `bilin`s: the quadratic
forms `w(i, k) = xᵀ T{i,k} x`, then `zᵢ = Σₖ xₖ w(i, k)`. The three arguments are read out of
one set `P` by linear maps: the identity three times is the single form, the mixed form otherwise.

## Inputs
* `π₁` – first projection to vectors
* `π₂` – second projection to vectors
* `π₃` – third projection to vectors
* `T` – family of cubic form tensors
* `P` – polynomial zonotope

## Output
* polynomial zonotope of the cubic image of the projected set
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ} {V : Type} [AddCommGroup V] [Module ℝ V]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `(x, w) ↦ (Σₖ xₖ · w(i, k))ᵢ`, `w` indexed by the pairs `(i, k)`. -/
def PolyZonotope.aux_cubPair (m n : ℕ) : Vec ℝ n →ₗ[ℝ] Vec ℝ (m * n) →ₗ[ℝ] Vec ℝ m :=
  LinearMap.mk₂ ℝ (fun (x : Vec ℝ n) (w : Vec ℝ (m * n)) (i : Fin m) =>
      ∑ k, x k * w (finProdFinEquiv (i, k)))
    (fun _ _ _ => funext fun _ => by simp [add_mul, Finset.sum_add_distrib])
    (fun _ _ _ => funext fun _ => by simp [Finset.mul_sum, mul_assoc])
    (fun _ _ _ => funext fun _ => by simp [mul_add, Finset.sum_add_distrib])
    (fun _ _ _ => funext fun _ => by simp [Finset.mul_sum, mul_left_comm])

/-- The tensor read as one quadratic form per pair: `T{i,k}` at `(i, k)`. -/
def PolyZonotope.aux_cubQuad (T : Fin m → Fin n → Mat ℝ n n) : Fin (m * n) → Mat ℝ n n :=
  fun l => T (finProdFinEquiv.symm l).1 (finProdFinEquiv.symm l).2


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The cubic map of the arguments `π₁ x, π₂ x, π₃ x` of the points `x` of `P`; sound only where
every coefficient is dependent. -/
def PolyZonotope.cubMapDepOn (π₁ π₂ π₃ : V →ₗ[ℝ] Vec ℝ n) (T : Fin m → Fin n → Mat ℝ n n)
    (P : PolyZonotope V) : PolyZonotope (Vec ℝ m) :=
  -- the quadratic forms `w(i, k) = (π₁ x)ᵀ T{i,k} (π₂ x)`
  let w : PolyZonotope (Vec ℝ (m * n)) :=
    PolyZonotope.bilin ((PolyZonotope.quadBilin (PolyZonotope.aux_cubQuad T)).compl₁₂ π₁ π₂) P P rfl
  -- `Σₖ (π₃ x)ₖ w(i, k)`
  PolyZonotope.bilin ((PolyZonotope.aux_cubPair m n).compl₁₂ π₃ LinearMap.id) P w rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
