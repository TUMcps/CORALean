module

public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The sign vectors have mean zero and covariance `2ᵐ I`

[1, Sec. III-B (initial guess)]: the `2ᵐ` points `G u`, `u ∈ {-1, 1}ᵐ` — the columns of `G [B
-B]` — have mean `0` and second moment `∑ (G u)(G u)ᵀ = 2ᵐ G Gᵀ`, so their principal axes are
those of the initial guess `m G Gᵀ` of [1, Eq. 13]. Flipping one sign is a bijection of the sign
vectors that negates that coordinate and keeps the others, which is the orthogonality of the
rows of `B` the paper states.

## Inputs
* `G` – generator matrix

## Hypotheses
* none

## Conclusion
* sign sums are centered with covariance `2^m G Gᵀ`

## References

* [1] V. Gaßmann and M. Althoff. "Scalable Zonotope-Ellipsoid Conversions using the Euclidean
      Zonotope Norm". In Proc. of the 2020 American Control Conference (ACC), pp. 4715-4721,
      2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `σ(s)ⱼ = ±1`. -/
def aux_sgn (s : Fin m → Bool) (j : Fin m) : ℝ := if s j then 1 else -1

/-- Flipping coordinate `j` negates `σⱼ` and keeps the rest, so `∑ σⱼ f = 0` when `f` ignores
`sⱼ`. -/
theorem aux_sum_flip (j : Fin m) (f : (Fin m → Bool) → ℝ)
    (hf : ∀ s, f (Function.update s j (!s j)) = f s) :
    ∑ s : Fin m → Bool, aux_sgn s j * f s = 0 := by -- --- PROOF ---
  let e : (Fin m → Bool) ≃ (Fin m → Bool) :=
    Function.Involutive.toPerm (fun s => Function.update s j (!s j)) fun s => by
      funext k
      by_cases hk : k = j
      · subst hk
        simp
      · simp [Function.update_of_ne hk]
  have h := Equiv.sum_comp e fun s => aux_sgn s j * f s
  have hflip : ∀ s, aux_sgn (e s) j * f (e s) = -(aux_sgn s j * f s) := fun s => by
    show aux_sgn (Function.update s j (!s j)) j * f (Function.update s j (!s j)) = _
    rw [hf]
    simp only [aux_sgn, Function.update_self]
    cases s j <;> simp
  simp only [hflip, Finset.sum_neg_distrib] at h
  linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.sign_sum_covariance (G : Mat ℝ n m) : -- --- CONCL ---
    (∑ s : Fin m → Bool, G *ᵥ fun j => if s j then (1 : ℝ) else -1) = 0 ∧
      ∀ a b, (∑ s : Fin m → Bool, (G *ᵥ fun j => if s j then (1 : ℝ) else -1) a *
        (G *ᵥ fun j => if s j then (1 : ℝ) else -1) b) =
        2 ^ m * (G * Gᵀ) a b := by -- --- PROOF ---
  -- the first moments of the signs vanish, the second are `2ᵐ` on the diagonal
  have h1 : ∀ j, ∑ s : Fin m → Bool, aux_sgn s j = 0 := fun j => by
    simpa using aux_sum_flip j (fun _ => 1) fun _ => rfl
  have h2 : ∀ j k, ∑ s : Fin m → Bool, aux_sgn s j * aux_sgn s k =
      if j = k then 2 ^ m else 0 := fun j k => by
    split_ifs with hjk
    · subst hjk
      have : ∀ s : Fin m → Bool, aux_sgn s j * aux_sgn s j = 1 := fun s => by
        simp only [aux_sgn]
        split_ifs <;> norm_num
      simp [this, Fintype.card_bool]
    · exact aux_sum_flip j (fun s => aux_sgn s k) fun s => by
        simp [aux_sgn, Function.update_of_ne (Ne.symm hjk)]
  refine ⟨?_, fun a b => ?_⟩
  · funext a
    simp only [Finset.sum_apply, Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    exact Finset.sum_eq_zero fun j _ => by
      rw [show (∑ s : Fin m → Bool, if s j then (1 : ℝ) else -1) = ∑ s, aux_sgn s j from rfl,
        h1, mul_zero]
  · -- expand both products, then sum the signs first
    have hexp : ∀ s : Fin m → Bool, (G *ᵥ fun j => if s j then (1 : ℝ) else -1) a *
        (G *ᵥ fun j => if s j then (1 : ℝ) else -1) b =
        ∑ j, ∑ k, G a j * G b k * (aux_sgn s j * aux_sgn s k) := fun s => by
      simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum, aux_sgn]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [Finset.sum_congr rfl fun s _ => hexp s, Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin m → Bool))), ← Finset.mul_sum, h2]
    simp [Matrix.mul_apply, Finset.mul_sum, mul_comm]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
