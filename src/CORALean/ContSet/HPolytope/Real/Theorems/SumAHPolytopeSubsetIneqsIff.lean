module

public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic
public import CORALean.ContSet.HPolytope.Real.Operations.RowLin
public import CORALean.Global.LinProg.Farkas
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Matrix.Basic

@[expose] public section

/-!
# A Minkowski sum of AH-polytopes in an H-polytope, exactly

`[1, Prop. 1]`: `x̄ + ⨁ᵢ Xᵢ Pᵢ ⊆ {Hy x ≤ hy}` iff some `Λᵢ ≥ 0` have `Λᵢ Hᵢ = Hy Xᵢ` and
`∑ᵢ Λᵢ hᵢ ≤ hy - Hy x̄` (`[1, Prop. 1, Eq. 23]`). "If" is weak duality summand by summand. "Only
if" is one application of Farkas per row of `Hy`, over the product of the coefficient
spaces, whose rows are every summand's rows together. It needs every `Pᵢ` nonempty, which
the printed statement omits — at `N = 1` it is `[1, Lemma 1]`, and the same empty inbody
breaks it (`sum_ahPolytope_subset_ineqs_iff_counterexample`).

## Inputs
* `nx` – natural numbers indexed by `Fin N`
* `qx` – natural numbers indexed by `Fin N`
* `xbar` – mean of length `n`
* `X` – matrices indexed by `Fin N`
* `Hx` – matrices indexed by `Fin N`
* `hx` – vectors indexed by `Fin N`
* `Hy` – `qy × n` matrix
* `hy` – vector of length `qy`

## Hypotheses
* `hne` – each polytope is nonempty

## Conclusion
* A Minkowski sum of AH-polytopes in an H-polytope, exactly

## References

* [1] S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". 2019 IEEE
      58th Conference on Decision and Control (CDC), 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n qy N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.sum_ahPolytope_subset_ineqs_iff {nx qx : Fin N → ℕ} (xbar : Vec ℝ n)
    (X : (i : Fin N) → Mat ℝ n (nx i)) (Hx : (i : Fin N) → Mat ℝ (qx i) (nx i))
    (hx : (i : Fin N) → Vec ℝ (qx i)) (Hy : Mat ℝ qy n) (hy : Vec ℝ qy)
    (hne : ∀ i, (HPolytope.ineqs (Hx i) (hx i)).construct.Nonempty) : -- --- CONCL ---
    {x | ∃ p : (i : Fin N) → Vec ℝ (nx i),
        (∀ i, p i ∈ (HPolytope.ineqs (Hx i) (hx i)).construct) ∧ x = xbar + ∑ i, X i *ᵥ p i}
        ⊆ (HPolytope.ineqs Hy hy).construct ↔
      ∃ Λ : (i : Fin N) → Mat ℝ qy (qx i), (∀ i j k, 0 ≤ Λ i j k) ∧
        (∀ i, Λ i * Hx i = Hy * X i) ∧
        ∑ i, Λ i *ᵥ hx i ≤ hy - Hy *ᵥ xbar := by -- --- PROOF ---
  have hrl : ∀ {q m : ℕ} (M : Mat ℝ q m) j v, HPolytope.rowLin M j v = (M *ᵥ v) j :=
    fun _ _ _ => rfl
  let E := (i : Fin N) → Vec ℝ (nx i)
  -- the rows of every summand, read on the product of the coefficient spaces
  let A : (Σ i, Fin (qx i)) → (E →ₗ[ℝ] ℝ) :=
    fun σ => (HPolytope.rowLin (Hx σ.1) σ.2).comp (LinearMap.proj σ.1)
  let b : (Σ i, Fin (qx i)) → ℝ := fun σ => hx σ.1 σ.2
  have hproj : ∀ i (p : E), (LinearMap.proj i : E →ₗ[ℝ] Vec ℝ (nx i)) p = p i :=
    fun _ _ => rfl
  constructor
  · intro hsub
    have hrow : ∀ r, ∃ y : (Σ i, Fin (qx i)) → ℝ, (∀ σ, 0 ≤ y σ) ∧
        (∑ i, (HPolytope.rowLin (Hy * X i) r).comp (LinearMap.proj i) : E →ₗ[ℝ] ℝ)
          = ∑ σ, y σ • A σ ∧ ∑ σ, y σ * b σ ≤ hy r - (Hy *ᵥ xbar) r := by
      intro r
      refine exists_dual_of_forall_le_fintype A b _ _
        ⟨fun i => (hne i).some, fun σ => HPolytope.mem_ineqs_iff.mp (hne σ.1).some_mem σ.2⟩ ?_
      intro p hp
      have hmem := hsub ⟨p, fun i => HPolytope.mem_ineqs_iff.mpr fun k => hp ⟨i, k⟩, rfl⟩
      have := HPolytope.mem_ineqs_iff.mp hmem r
      rw [mulVec_add, mulVec_sum, Pi.add_apply, Finset.sum_apply] at this
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, hproj, hrl,
        ← mulVec_mulVec]
      linarith
    -- `Λᵢ` reads row `r`'s weights off the summand-`i` part of `y r`
    choose y hy0 hyc hyb using hrow
    refine ⟨fun i => Matrix.of fun r k => y r ⟨i, k⟩, fun i r k => hy0 r ⟨i, k⟩, fun i => ?_, ?_⟩
    -- an entry of `Λᵢ Hᵢ` is the combination evaluated at a unit vector of summand `i`
    · ext r l
      have h := congrArg (fun f : E →ₗ[ℝ] ℝ => f (Pi.single (M := fun i => Vec ℝ (nx i)) i
        (Pi.single l 1))) (hyc r)
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, hproj,
        LinearMap.smul_apply, smul_eq_mul, hrl, A] at h
      rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mulVec_zero,
        Pi.zero_apply]) (by simp), Pi.single_eq_same, mulVec_single_one, Matrix.col_apply,
        Fintype.sum_sigma, Finset.sum_eq_single i (fun j _ hj => by
          refine Finset.sum_eq_zero fun k _ => ?_
          rw [Pi.single_eq_of_ne hj, mulVec_zero, Pi.zero_apply, mul_zero]) (by simp)] at h
      simp only [Pi.single_eq_same, mulVec_single_one, Matrix.col_apply] at h
      rw [Matrix.mul_apply, h]
      simp
    · intro r
      have := hyb r
      rw [Fintype.sum_sigma] at this
      simpa [Finset.sum_apply, mulVec, dotProduct, b] using this
  -- weak duality, summand by summand
  · rintro ⟨Λ, hΛ, h1, h2⟩ _ ⟨p, hp, rfl⟩
    rw [HPolytope.mem_ineqs_iff]
    intro r
    have hle : ∀ i, (Hy *ᵥ (X i *ᵥ p i)) r ≤ (Λ i *ᵥ hx i) r := by
      intro i
      rw [mulVec_mulVec, ← h1 i, ← mulVec_mulVec]
      simp only [mulVec, dotProduct]
      exact Finset.sum_le_sum fun k _ =>
        mul_le_mul_of_nonneg_left (HPolytope.mem_ineqs_iff.mp (hp i) k) (hΛ i r k)
    have h2r := h2 r
    rw [Finset.sum_apply, Pi.sub_apply] at h2r
    rw [mulVec_add, mulVec_sum, Pi.add_apply, Finset.sum_apply]
    linarith [Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hle i]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
