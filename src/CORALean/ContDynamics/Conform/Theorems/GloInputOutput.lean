module

public import CORALean.ContDynamics.Conform.Theorems.NarxWindowStep
public import CORALean.ContDynamics.Conform.Theorems.SumWindow
public import CORALean.ContDynamics.Conform.Theorems.UnrollAffine
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# [1, Cor. 2]: the GLO approximation of an input-output model

The NARX model `y_k = h(y_{k-n_p:k-1}, u_{k-n_p:k})` expanded along a reference with remainder
`l_k` (`h` replaced by the Taylor hypothesis `hy`, as [1, Cor. 1] does for `f` and `g`) gives, for
`k ≥ n_p`, `y_k - ȳ_k = C̄_k (x₀ - x̄₀) + ∑ᵢ D̄_{k,i} (uᵢ - ūᵢ) + ē_k`, `x₀ = (y₀, …, y_{n_p-1})`,
with (15b), (15c) and `ē_k = E ∑_{j ≤ k-n_p} (∏_{l<j} A_ext,k-l) Eᵀ l_{k-j}`: the window recursion
of `narx_window_step` inserted into itself. `B_{k,i}` is zero outside `0 ≤ i ≤ n_p`, which the
printed `B_ext,k-j,k-i-j` needs. A linear `h` has `l = 0` and so `ē = 0`.

## Inputs
* `np` – number of lags
* `A` – output Jacobians
* `B` – input Jacobians
* `l` – remainders
* `y` – outputs
* `yb` – reference outputs
* `u` – inputs
* `ub` – reference inputs
* `k` – step

## Hypotheses
* `hp` – at least one lag
* `hy` – the Taylor expansion holds
* `hk` – step at least the number of lags

## Conclusion
* the output equals the linearization along the reference plus the remainder terms

## References

* [1] L. Lützow and M. Althoff. "Reachset-Conformant System Identification". IEEE
      Transactions on Automatic Control, 71(5):3014-3029, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {ny nu : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `B_ext,k,i` is zero outside `0 ≤ i ≤ n_p`. -/
theorem aux_narxBext_eq_zero (np : ℕ) (B : ℕ → Mat ℝ ny nu) {i : ℤ}
    (h : i < 0 ∨ (np : ℤ) < i) : -- --- CONCL ---
    Conform.narxBext np B i = 0 := by -- --- PROOF ---
  ext r c
  simp only [Conform.narxBext, Matrix.of_apply, Matrix.zero_apply]
  rw [if_neg]
  rintro ⟨h1, h2, -⟩
  omega

/-- The input sums of the unrolled recursion, regrouped by the input they hit. -/
theorem aux_regroup_inputs (np k : ℕ) (hk : np ≤ k) (E : Mat ℝ ny (np * ny))
    (P : ℕ → Mat ℝ (np * ny) (np * ny)) (B : ℕ → ℕ → Mat ℝ ny nu)
    (δ : ℕ → Vec ℝ nu) : -- --- CONCL ---
    ∑ j ∈ Finset.range (k - np + 1), ∑ i ∈ Finset.range (np + 1),
        (E * (P j * Conform.narxBext np (B (k - j)) i)) *ᵥ δ (k - j - i)
      = ∑ i ∈ Finset.range (k + 1), (E * ∑ j ∈ Finset.range (k - np + 1),
          P j * Conform.narxBext np (B (k - j)) ((k : ℤ) - i - j)) *ᵥ δ i := by -- --- PROOF ---
  simp only [Matrix.mul_sum, Matrix.sum_mulVec]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  -- only the inputs `k - j - n_p … k - j` meet a nonzero block
  have hsub : ∑ i ∈ (Finset.range (np + 1)).image (fun i' => k - j - i'),
      (E * (P j * Conform.narxBext np (B (k - j)) ((k : ℤ) - i - j))) *ᵥ δ i
      = ∑ i ∈ Finset.range (k + 1),
      (E * (P j * Conform.narxBext np (B (k - j)) ((k : ℤ) - i - j))) *ᵥ δ i := by
    refine Finset.sum_subset (fun i hi => ?_) fun i _ hi => ?_
    · obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_range.mpr (by omega)
    · rw [aux_narxBext_eq_zero np (B (k - j)) ?_]
      · simp
      · by_contra hc
        rw [not_or, not_lt, not_lt] at hc
        exact hi (Finset.mem_image.mpr ⟨k - j - i, Finset.mem_range.mpr (by omega), by omega⟩)
  rw [← hsub, Finset.sum_image (fun a ha b hb hab => by
    have := Finset.mem_range.mp ha
    have := Finset.mem_range.mp hb
    have hab' : k - j - a = k - j - b := hab
    omega)]
  refine Finset.sum_congr rfl fun i' hi' => ?_
  have hi'' := Finset.mem_range.mp hi'
  -- the integer index `k - i - j` at `i = k - j - i'` is `i'`
  rw [show ((k : ℤ) - ((k - j - i' : ℕ) : ℤ) - j) = (i' : ℤ) by
    push_cast [Nat.cast_sub (by omega : i' ≤ k - j), Nat.cast_sub (by omega : j ≤ k)]; ring]

/-- `E` reads `y_k - ȳ_k` off the deviation of the window that ends at `k - 1`. -/
theorem aux_readout (np : ℕ) (hp : 0 < np) (y yb : ℕ → Vec ℝ ny) (m : ℕ) : -- --- CONCL ---
    Conform.narxE np ny *ᵥ (NonlinearARX.stack np y m - NonlinearARX.stack np yb m)
      = y (m + np - 1) - yb (m + np - 1) := by -- --- PROOF ---
  funext j
  simp only [Matrix.mulVec, dotProduct, Pi.sub_apply]
  rw [Conform.sum_window]
  simp only [Conform.narxE, Matrix.of_apply, NonlinearARX.stack, Equiv.symm_apply_apply]
  rw [Finset.sum_eq_single (⟨np - 1, by omega⟩ : Fin np)
    (fun b _ hb => Finset.sum_eq_zero fun j' _ => by
      rw [if_neg (by rintro ⟨h, _⟩; exact hb (Fin.ext (by simp only; omega))), zero_mul]) (by simp)]
  rw [Finset.sum_eq_single j (fun j' _ hj => by
    rw [if_neg (by rintro ⟨_, h⟩; exact hj h), zero_mul]) (by simp)]
  rw [if_pos ⟨by simp only; omega, rfl⟩, one_mul, show m + (np - 1) = m + np - 1 by omega]

/-- Shifting the time origin by `n_p` leaves the product of the latest factors unchanged. -/
theorem aux_prodJac_shift (np m0 j : ℕ) (hj : j ≤ m0 + 1) (A : ℕ → Mat ℝ ny ny) : -- --- CONCL ---
    Conform.prodJac (fun m => A (np + m)) (m0 + 1) j
      = Conform.prodJac A (np + m0 + 1) j := by -- --- PROOF ---
  simp only [Conform.prodJac]
  congr 1
  refine List.map_congr_left fun l hl => ?_
  have := List.mem_range.mp hl
  congr 1
  omega


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Cor. 2]: the linearized NARX output is `ȳ_k + C̄_k δx₀ + ∑ᵢ D̄_{k,i} δuᵢ + ē_k`. -/
theorem Conform.glo_inputOutput (np : ℕ) (hp : 0 < np) (A : ℕ → ℕ → Mat ℝ ny ny)
    (B : ℕ → ℕ → Mat ℝ ny nu) (l : ℕ → Vec ℝ ny) (y yb : ℕ → Vec ℝ ny) (u ub : ℕ → Vec ℝ nu)
    (hy : ∀ k, np ≤ k → y k = yb k
      + ∑ i ∈ Finset.range np, A k (i + 1) *ᵥ (y (k - (i + 1)) - yb (k - (i + 1)))
      + ∑ i ∈ Finset.range (np + 1), B k i *ᵥ (u (k - i) - ub (k - i)) + l k)
    (k : ℕ) (hk : np ≤ k) : -- --- CONCL ---
    y k = yb k
      + (Conform.narxE np ny * Conform.prodJac (fun t => Conform.narxAext np (A t)) (k + 1)
          (k - np + 1)) *ᵥ (NonlinearARX.stack np y 0 - NonlinearARX.stack np yb 0)
      + ∑ i ∈ Finset.range (k + 1),
          (Conform.narxE np ny * ∑ j ∈ Finset.range (k - np + 1),
            Conform.prodJac (fun t => Conform.narxAext np (A t)) (k + 1) j *
              Conform.narxBext np (B (k - j)) ((k : ℤ) - i - j)) *ᵥ (u i - ub i)
      + Conform.narxE np ny *ᵥ ∑ j ∈ Finset.range (k - np + 1),
          Conform.prodJac (fun t => Conform.narxAext np (A t)) (k + 1) j *ᵥ
            ((Conform.narxE np ny)ᵀ *ᵥ l (k - j)) := by -- --- PROOF ---
  obtain ⟨m0, rfl⟩ := Nat.exists_eq_add_of_le hk
  set Ae : ℕ → Mat ℝ (np * ny) (np * ny) := fun t => Conform.narxAext np (A t) with hAe
  set d : ℕ → Vec ℝ (np * ny) :=
    fun m => NonlinearARX.stack np y m - NonlinearARX.stack np yb m with hd
  set w : ℕ → Vec ℝ (np * ny) := fun m =>
    ∑ i ∈ Finset.range (np + 1), Conform.narxBext np (B (np + m)) i *ᵥ
      (u (np + m - i) - ub (np + m - i)) + (Conform.narxE np ny)ᵀ *ᵥ l (np + m) with hw
  -- the window deviation obeys an affine recursion in the shifted time
  have hrec : ∀ m, d (m + 1) = (fun m => Ae (np + m)) m *ᵥ d m + w m := fun m => by
    have h := Conform.narx_window_step np A B l y yb u ub hy (np + m) (by omega)
    rw [Nat.add_sub_cancel_left] at h
    exact h.trans (add_assoc _ _ _)
  have hU := Conform.unroll_affine (fun m => Ae (np + m)) d w hrec (m0 + 1)
  have hread := aux_readout np hp y yb (m0 + 1)
  rw [show m0 + 1 + np - 1 = np + m0 by omega] at hread
  have hyk : y (np + m0) = yb (np + m0) + Conform.narxE np ny *ᵥ d (m0 + 1) := by
    have : y (np + m0) - yb (np + m0) = Conform.narxE np ny *ᵥ d (m0 + 1) := hread.symm
    rw [← this]; abel
  have hP : ∀ j, j ≤ m0 + 1 →
      Conform.prodJac (fun m => Ae (np + m)) (m0 + 1) j = Conform.prodJac Ae (np + m0 + 1) j :=
    fun j hj => aux_prodJac_shift np m0 j hj Ae
  -- the sum of the unrolled recursion, newest term first
  have hS : Conform.narxE np ny *ᵥ ∑ i ∈ Finset.range (m0 + 1),
        Conform.prodJac (fun m => Ae (np + m)) (m0 + 1) (m0 + 1 - i - 1) *ᵥ w i
      = ∑ j ∈ Finset.range (m0 + 1), Conform.narxE np ny *ᵥ
          (Conform.prodJac Ae (np + m0 + 1) j *ᵥ w (m0 + 1 - 1 - j)) := by
    rw [mulVec_sum, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    rw [show m0 + 1 - (m0 + 1 - 1 - j) - 1 = j by omega, hP j (by omega)]
  rw [Nat.add_sub_cancel_left, hyk, hU, hP _ le_rfl, mulVec_add, ← mulVec_mulVec, hS]
  -- each term splits into its input part and its remainder part
  have hterm : ∀ j ∈ Finset.range (m0 + 1), Conform.narxE np ny *ᵥ
        (Conform.prodJac Ae (np + m0 + 1) j *ᵥ w (m0 + 1 - 1 - j))
      = ∑ i ∈ Finset.range (np + 1), (Conform.narxE np ny * (Conform.prodJac Ae (np + m0 + 1) j *
          Conform.narxBext np (B (np + m0 - j)) i)) *ᵥ (u (np + m0 - j - i) - ub (np + m0 - j - i))
        + Conform.narxE np ny *ᵥ (Conform.prodJac Ae (np + m0 + 1) j *ᵥ
          ((Conform.narxE np ny)ᵀ *ᵥ l (np + m0 - j))) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    simp only [hw]
    rw [show np + (m0 + 1 - 1 - j) = np + m0 - j by omega, mulVec_add, mulVec_add, mulVec_sum,
      mulVec_sum]
    simp only [mulVec_mulVec]
  have hreg := aux_regroup_inputs np (np + m0) hk (Conform.narxE np ny)
    (Conform.prodJac Ae (np + m0 + 1)) B (fun i => u i - ub i)
  rw [Nat.add_sub_cancel_left] at hreg
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, hreg, mulVec_sum]
  abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
