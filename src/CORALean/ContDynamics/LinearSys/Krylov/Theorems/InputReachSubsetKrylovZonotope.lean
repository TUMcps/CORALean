module

public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.InputReachSubsetKrylovTaylor
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex
public import CORALean.ContSet.Zonotope.Real.Theorems.IsBounded
public import CORALean.ContSet.Zonotope.Real.Theorems.Basic
public import CORALean.ContDynamics.LinearSys.Operations.Canonical
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The input solution for varying inputs in a zonotope, from the Krylov Taylor terms

A correct form of [1, Cor. IV.2]: for `U = (c_u, g⁽¹⁾_u, …, g⁽q⁾_u)`, `R_p(δ)` lies in the sum
over `j = 1, …, η + 1` of the zonotopes
`(P Ṽ(c_u)H̃ʲ(c_u)e₁ δʲ/j!, P Ṽ(g⁽ⁱ⁾_u)H̃ʲ(g⁽ⁱ⁾_u)e₁ δʲ/j!)`, plus the remainder `E(δ)·δ·U` of
[2, Prop. 2] in place of [1]'s `R_p,err`, below the Krylov order `η + 1 ≤ m`. There [1]'s
splitting into center and generators holds: after `P` and `e₁` the Krylov term is `A^{j-1}u`
(`augment_arnoldi_pow`), linear in `u`. [1]'s `R_p,err` fails
(`varying_input_reach_counterexample`).

## Inputs
* `A` – system matrix
* `Z` – input zonotope
* `δ` – step length
* `η` – Taylor order
* `m` – Krylov order

## Hypotheses
* `hδ` – step length positive
* `hηm` – Taylor order below the Krylov order
* `hε` – scaled norm small enough for the Taylor order

## Conclusion
* the input solution lies in the Krylov zonotopes plus the remainder

## References

* [1] [M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the
      Krylov Subspace". IEEE Transactions on Automatic Control,
      2020.](../../../../../../references/2020/althoff-tac-krylov.md)
* [2] [M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control,
      2007.](../../../../../../references/2007/althoff-cdc-uncertain-parameters-inputs.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The Krylov term of order `j + 1` at `u`, `P Ṽ(u)H̃^{j+1}(u)e₁ δ^{j+1}/(j+1)!`. -/
@[step_of Krylov.inputReach_subset_krylovZonotope]
noncomputable abbrev Krylov.step_krylovTerm (A : Mat ℝ n n) (δ : ℝ) (m j : ℕ) (u : Vec ℝ n) :
    Vec ℝ n :=
  (δ ^ (j + 1) / (Nat.factorial (j + 1) : ℝ)) • fun i =>
    (Krylov.arnoldiBasis (Krylov.augment A u) (Pi.single (Fin.last n) 1) (m + 1) *ᵥ
      (Krylov.arnoldiHessenberg (Krylov.augment A u) (Pi.single (Fin.last n) 1) (m + 1)
        ^ (j + 1) *ᵥ Pi.single 0 1)) (Fin.castSucc i)


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Below the Krylov order the Krylov term maps the zonotope `Z` onto the zonotope of the
images of its center and generators. -/
private theorem Krylov.aux_image_krylovTerm (A : Mat ℝ n n) (Z : Zonotope (Vec ℝ n)) (δ : ℝ)
    {m j : ℕ} (hj : j + 1 ≤ m) : -- --- CONCL ---
    Krylov.step_krylovTerm A δ m j '' Z.construct = (⟨Z.h, Krylov.step_krylovTerm A δ m j Z.c,
      fun i => Krylov.step_krylovTerm A δ m j (Z.G i)⟩ :
        Zonotope (Vec ℝ n)).construct := by -- --- PROOF ---
  -- the term is the linear map `u ↦ (δ^{j+1}/(j+1)!) A^j u`
  have hlin : ∀ u, Krylov.step_krylovTerm A δ m j u
      = (δ ^ (j + 1) / (Nat.factorial (j + 1) : ℝ)) • (A ^ j *ᵥ u) := fun u => by
    rw [Krylov.step_krylovTerm, Krylov.augment_arnoldi_pow A u m (Nat.le_add_left 1 j) hj,
      Nat.add_sub_cancel]
  ext x
  simp only [Set.mem_image, Zonotope.construct, Set.mem_setOf_eq, hlin]
  constructor
  · rintro ⟨u, ⟨β, hβ, rfl⟩, rfl⟩
    refine ⟨β, hβ, ?_⟩
    rw [Matrix.mulVec_add, Matrix.mulVec_sum, smul_add, Finset.smul_sum]
    simp only [Matrix.mulVec_smul, smul_comm (δ ^ (j + 1) / (Nat.factorial (j + 1) : ℝ))]
  · rintro ⟨β, hβ, rfl⟩
    refine ⟨Z.c + ∑ i, β i • Z.G i, ⟨β, hβ, rfl⟩, ?_⟩
    rw [Matrix.mulVec_add, Matrix.mulVec_sum, smul_add, Finset.smul_sum]
    simp only [Matrix.mulVec_smul, smul_comm (δ ^ (j + 1) / (Nat.factorial (j + 1) : ℝ))]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Cor. IV.2] below the Krylov order `η + 1 ≤ m`: the zonotopes of the Krylov terms at
`c_u` and the `g⁽ⁱ⁾_u`, plus [2, Prop. 2]'s remainder `E(δ)·δ·U` closed and convexified. -/
theorem Krylov.inputReach_subset_krylovZonotope (A : Mat ℝ n n) (Z : Zonotope (Vec ℝ n)) {δ : ℝ}
    (hδ : 0 < δ) (η m : ℕ) (hηm : η + 1 ≤ m) (hε : ‖δ • A‖ / ((η : ℝ) + 2) < 1) : -- --- CONCL ---
    (LinearSys.canonical A : LinearSys ℝ n).inputReach (S := 𝒮) Z.construct δ
      ⊆ (∑ j ∈ Finset.range (η + 1),
          (⟨Z.h, Krylov.step_krylovTerm A δ m j Z.c,
            fun i => Krylov.step_krylovTerm A δ m j (Z.G i)⟩ : Zonotope (Vec ℝ n)).construct)
        + closure (convexHull ℝ
            (⋃ M ∈ (MatExp.inputRemainder A δ η).construct,
              (M *ᵥ ·) '' Z.construct)) := by -- --- PROOF ---
  refine (Krylov.inputReach_subset_krylovTaylor A Z.convex_construct Z.isClosed_construct
    Z.isBounded_construct hδ η m hηm hε).trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  exact Krylov.aux_image_krylovTerm A Z δ (by simp at hj; omega)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
