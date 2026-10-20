module

public import CORALean.ContDynamics.LinearSys.Krylov.Operations.ArnoldiBasis
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.ArnoldiHessenberg
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ArnoldiRelation
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.PowMulVecOfHessenberg

@[expose] public section

/-!
# The Krylov approximation is exact below the Krylov order

After `ξ = m + 1` passes of [1, Alg. 1], `V H^j e₁ = C^j v / ‖v‖` for `j ≤ m`: the Taylor
coefficients of `‖v‖ V e^{Ht} e₁`, [1]'s (2), agree with those of `e^{Ct} v` up to order
`ξ - 1`. From the Arnoldi relation (`arnoldi_relation`), which holds for every column, and
`H` being upper Hessenberg, through `pow_mulVec_of_hessenberg`; the residual
`h_{ξ+1,ξ} v⁽ξ⁺¹⁾` of the last column is first reached at `j = ξ`. Orthogonality of `V` is
not used. A pass stores what earlier passes stored unchanged, which is what lets the
relation, stated at pass `k + 1`, be read in the matrices of pass `ξ`.

## Inputs
* `C` – matrix
* `v` – start vector
* `m` – Krylov order
* `j` – power

## Hypotheses
* `hj` – power at most the Krylov order

## Conclusion
* the Krylov approximation of the power applied to the start vector is exact

## References

* [1] M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the
  Krylov Subspace". IEEE Transactions on Automatic Control, 65(2):477-492, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A pass keeps the vectors stored before it. -/
theorem Krylov.aux_arnoldi_fst_le (C : Mat ℝ n n) (v : Vec ℝ n) {p q i : ℕ} (hpq : p ≤ q)
    (hi : i ≤ p) : -- --- CONCL ---
    (Krylov.arnoldi C v q).1 i = (Krylov.arnoldi C v p).1 i := by -- --- PROOF ---
  induction q, hpq using Nat.le_induction with
  | base => rfl
  | succ q hpq ih =>
    rw [← ih]
    simp only [Krylov.arnoldi]
    rw [Function.update_of_ne (by omega)]

/-- A pass keeps the Hessenberg columns stored before it. -/
theorem Krylov.aux_arnoldi_snd_le (C : Mat ℝ n n) (v : Vec ℝ n) {p q k : ℕ} (hpq : p ≤ q)
    (hk : k < p) (i : ℕ) : -- --- CONCL ---
    (Krylov.arnoldi C v q).2 i k = (Krylov.arnoldi C v p).2 i k := by -- --- PROOF ---
  induction q, hpq using Nat.le_induction with
  | base => rfl
  | succ q hpq ih =>
    rw [← ih]
    simp only [Krylov.arnoldi]
    rw [if_neg (by omega)]

/-- `h_{i,k} = 0` below the subdiagonal: `H` is upper Hessenberg. -/
theorem Krylov.aux_arnoldi_snd_eq_zero (C : Mat ℝ n n) (v : Vec ℝ n) {i k : ℕ} (hik : k + 1 < i) :
    ∀ p, (Krylov.arnoldi C v p).2 i k = 0
  | 0 => rfl
  | p + 1 => by
    simp only [Krylov.arnoldi]
    split_ifs with h1 h2 h3
    · omega
    · omega
    · rfl
    · exact Krylov.aux_arnoldi_snd_eq_zero C v hik p


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1] is exact below the Krylov order: `V H^j e₁ = C^j v / ‖v‖` for `j ≤ m`,
`ξ = m + 1`. -/
theorem Krylov.arnoldiBasis_mulVec_pow (C : Mat ℝ n n) (v : Vec ℝ n) (m : ℕ) {j : ℕ}
    (hj : j ≤ m) : -- --- CONCL ---
    Krylov.arnoldiBasis C v (m + 1) *ᵥ
        (Krylov.arnoldiHessenberg C v (m + 1) ^ j *ᵥ Pi.single 0 1)
      = ‖v‖₂⁻¹ • (C ^ j *ᵥ v) := by -- --- PROOF ---
  set K := Krylov.arnoldi C v (m + 1) with hK
  -- the relation of column `k < m`, read in the matrices of pass `m + 1`
  have hrel : ∀ k : Fin (m + 1), (k : ℕ) + 1 < m + 1 → ∀ i,
      (C * Krylov.arnoldiBasis C v (m + 1)) i k
        = (Krylov.arnoldiBasis C v (m + 1) * Krylov.arnoldiHessenberg C v (m + 1)) i k := by
    intro k hk i
    have hR := congrFun (Krylov.arnoldi_relation C v (k : ℕ)) i
    have hV : ∀ l ≤ (k : ℕ) + 1, (Krylov.arnoldi C v ((k : ℕ) + 1)).1 l = K.1 l :=
      fun l hl => (Krylov.aux_arnoldi_fst_le C v (by omega) hl).symm
    have hH : ∀ l, (Krylov.arnoldi C v ((k : ℕ) + 1)).2 l k = K.2 l k :=
      fun l => (Krylov.aux_arnoldi_snd_le C v (by omega) (Nat.lt_succ_self _) l).symm
    rw [hV k (Nat.le_succ _), hV (k + 1) le_rfl, hH] at hR
    have hsum : ∀ l ∈ Finset.range ((k : ℕ) + 1),
        ((Krylov.arnoldi C v ((k : ℕ) + 1)).2 l k • (Krylov.arnoldi C v ((k : ℕ) + 1)).1 l) i
          = K.2 l k * K.1 l i := by
      intro l hl
      rw [hV l (by have := Finset.mem_range.mp hl; omega), hH]
      rfl
    rw [Pi.add_apply, Finset.sum_apply, Finset.sum_congr rfl hsum, Pi.smul_apply,
      smul_eq_mul] at hR
    -- both sides as sums over `Fin (m + 1)`, the entries past `k + 1` being zero
    simp only [Matrix.mul_apply, Krylov.arnoldiBasis, Krylov.arnoldiHessenberg, Matrix.of_apply]
    rw [Fin.sum_univ_eq_sum_range (fun l => K.1 l i * K.2 l k) (m + 1)]
    have hzero : ∀ l ∈ Finset.range (m + 1), l ∉ Finset.range ((k : ℕ) + 2) →
        K.1 l i * K.2 l k = 0 := by
      intro l _ hl
      rw [Krylov.aux_arnoldi_snd_eq_zero C v (by simp at hl; omega), mul_zero]
    rw [← Finset.sum_subset (Finset.range_subset_range.2 (by omega)) hzero, Finset.sum_range_succ]
    have hCi : ∑ l : Fin n, C i l * K.1 k l = (C *ᵥ K.1 k) i := rfl
    rw [hCi, hR]
    simp only [mul_comm]
  have hx : ∀ i : Fin (m + 1), m + 1 ≤ (i : ℕ) + j → (Pi.single 0 1 : Fin (m + 1) → ℝ) i = 0 :=
    fun i hi => Pi.single_eq_of_ne (fun h => by rw [h] at hi; simp at hi; omega) 1
  rw [← Krylov.pow_mulVec_of_hessenberg C (Krylov.arnoldiBasis C v (m + 1))
    (Krylov.arnoldiHessenberg C v (m + 1))
    (fun i k hik => Krylov.aux_arnoldi_snd_eq_zero C v hik (m + 1)) hrel j _ hx,
    mulVec_single_one]
  -- the first column is `v⁽¹⁾ = v / ‖v‖`, stored at pass `0`
  have hcol : (Krylov.arnoldiBasis C v (m + 1)).col 0 = ‖v‖₂⁻¹ • v := by
    funext i
    simp only [Matrix.col_apply, Krylov.arnoldiBasis, Matrix.of_apply, Fin.val_zero]
    rw [Krylov.aux_arnoldi_fst_le C v (Nat.zero_le _) le_rfl]
    rfl
  rw [hcol, mulVec_smul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
