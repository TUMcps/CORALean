module

public import CORALean.ContSet.PolyZonotope.Real.Operations.CubEval
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The cubic map of a weighted sum of vectors, expanded

The cubic map `x ↦ (Σₖ xₖ · xᵀ T{i,k} x)ᵢ` is trilinear in `(x, x, x)`: at `x = Σⱼ wⱼ gⱼ` it is
the sum over ordered triples of `wⱼ₁ wⱼ₂ wⱼ₃` times the contraction of `gⱼ₁, gⱼ₂, gⱼ₃`. With the
extended generators `[c, G]` and monomials as weights, this is why `PolyZonotope.cubMap` has one
generator per triple.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

open Finset

variable {n m N : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A trilinear form of three sums, with the sums pulled out. -/
theorem PolyZonotope.aux_trilinear_expand {k : ℕ} (M : Fin n → Fin n → Fin n → ℝ)
    (A B C : Fin k → Fin n → ℝ) :
    ∑ a, ∑ b, ∑ c, M a b c * (∑ i, A i a) * (∑ j, B j b) * (∑ l, C l c)
      = ∑ i, ∑ j, ∑ l, ∑ a, ∑ b, ∑ c, M a b c * A i a * B j b * C l c := by -- --- PROOF ---
  simp only [mul_sum, sum_mul]
  -- `a b c l j i` to `i j l a b c`
  conv_lhs =>
    enter [2]; intro a; enter [2]; intro b; enter [2]; intro c; enter [2]; intro l
    rw [Finset.sum_comm]
  conv_lhs => enter [2]; intro a; enter [2]; intro b; enter [2]; intro c; rw [Finset.sum_comm]
  conv_lhs => enter [2]; intro a; enter [2]; intro b; rw [Finset.sum_comm]
  conv_lhs => enter [2]; intro a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro i; enter [2]; intro a; enter [2]; intro b; enter [2]; intro c
    rw [Finset.sum_comm]
  conv_lhs => enter [2]; intro i; enter [2]; intro a; enter [2]; intro b; rw [Finset.sum_comm]
  conv_lhs => enter [2]; intro i; enter [2]; intro a; rw [Finset.sum_comm]
  conv_lhs => enter [2]; intro i; rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro i; enter [2]; intro j; enter [2]; intro a; enter [2]; intro b
    rw [Finset.sum_comm]
  conv_lhs => enter [2]; intro i; enter [2]; intro j; enter [2]; intro a; rw [Finset.sum_comm]
  conv_lhs => enter [2]; intro i; enter [2]; intro j; rw [Finset.sum_comm]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.cubEval_expand (T : Fin m → Fin n → Mat ℝ n n) (w : Fin N → ℝ)
    (g : Fin N → Vec ℝ n) (i : Fin m) : -- --- CONCL ---
    PolyZonotope.cubEval T (∑ j, w j • g j) i
      = ∑ j₁, ∑ j₂, ∑ j₃, w j₁ * w j₂ * w j₃
          * ∑ k, g j₁ k * (g j₂ ⬝ᵥ (T i k *ᵥ g j₃)) := by -- --- PROOF ---
  -- the point's coordinates as sums
  have hx : ∀ k, (∑ j, w j • g j) k = ∑ j, w j * g j k := fun k => by
    simp [Finset.sum_apply]
  -- the triple sum of the trilinear form in the exact layer
  have hT := PolyZonotope.aux_trilinear_expand (fun k r s => T i k r s)
    (fun j k => w j * g j k) (fun j r => w j * g j r) (fun j s => w j * g j s)
  simp only [PolyZonotope.cubEval, dotProduct, Matrix.mulVec, hx]
  -- the form is the same sum with the factors regrouped
  have h1 : ∑ k, (∑ j, w j * g j k) * ∑ r, (∑ j, w j * g j r) * ∑ s, T i k r s * ∑ j, w j * g j s
      = ∑ k, ∑ r, ∑ s, T i k r s * (∑ j, w j * g j k) * (∑ j, w j * g j r)
          * (∑ j, w j * g j s) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  rw [h1, hT]
  refine Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun j₂ _ =>
    Finset.sum_congr rfl fun j₃ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
