module

public import CORALean.ContDynamics.LinearSys.Krylov.Operations.ErrorBoundFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.DecayProductFloatBound
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ErrorLeColumnResidual
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.QuadLeQuadBoundUp
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ResidualNormFloatBound
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.StartErrorFloatBound

@[expose] public section

/-!
# The float bound covers the Krylov error of any stored basis

[1, Thm. 3] for a basis and a Hessenberg matrix that are only stored floats.
For any basis vectors `V` and Hessenberg entries `H` stored as floats, upper Hessenberg, with
`μA` bounding the quadratic form of `A` and `ε_j` the residual norms of the columns,
`‖e^{sA}c - ν V_k e^{sT_k}e₁‖₂` is at most `Krylov.errorBoundFloat` for every `s ∈ [0, t]`, when
`tμ` is within `expUp`'s range: `Krylov.error_le_column_residual` at the real objects the floats
denote, then each factor bounded by its float counterpart. Orthogonality of `V` and normalization
of its first column are not used; their failure is in the residuals and in `ρ`.

## Inputs
* `p` – Newton steps per norm
* `q` – squarings of the exponential
* `A` – matrix
* `c` – start vector
* `ν` – scale of the first basis vector
* `V` – basis vectors
* `H` – Hessenberg entries
* `m` – order minus one
* `t` – time
* `μA` – bound of the quadratic form of `A`
* `ε` – bounds of the residual norms

## Hypotheses
* `hq` – at least one squaring
* `hH` – Hessenberg entries below the subdiagonal zero
* `hμA` – quadratic form of `A` bounded
* `hε` – residual norms bounded
* `ht` – time nonnegative
* `hcap` – `tμ` within the exponential's range

## Conclusion
* the Krylov error over `[0, t]` is at most the float bound

## References

* [1] [T. Jawecki, W. Auzinger and O. Koch. "Computable upper error bounds for Krylov approximations
      to matrix exponentials and associated φ-functions". BIT Numerical Mathematics,
      2020.](../../../../../../references/2020/jawecki-bit-krylov-error-bounds.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The residual's sum over `Fin (j + 2)` is the product `V T` plus the `τ w` of the last column,
as the entries below the subdiagonal vanish. -/
private theorem aux_sum_split (H : ℕ → ℕ → ℝ) (f : ℕ → ℝ) (m j : ℕ) (hj : j < m + 1)
    (hH : ∀ i, j + 1 < i → H i j = 0) : -- --- CONCL ---
    ∑ i : Fin (j + 2), H i j * f i =
      ∑ i : Fin (m + 1), H i j * f i +
        (if j = m then H (m + 1) j * f (m + 1) else 0) := by -- --- PROOF ---
  rw [Fin.sum_univ_eq_sum_range (fun i => H i j * f i) (j + 2),
    Fin.sum_univ_eq_sum_range (fun i => H i j * f i) (m + 1)]
  by_cases h : j = m
  · subst h
    simp [Finset.sum_range_succ]
  · have hlt : j + 2 ≤ m + 1 := by omega
    rw [if_neg h, add_zero]
    refine Finset.sum_subset (Finset.range_mono hlt) fun i hi hni => ?_
    have : j + 1 < i := by simp at hi hni; omega
    rw [hH i this, zero_mul]


/-- The columns of `A V - V T - τ w e_m*` are the residuals the float bound covers. -/
private theorem aux_delta_col {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}
    (A : Mat 𝕋 n n)
    (V : ℕ → Vector 𝕋 n) (H : ℕ → ℕ → 𝕋) (m : ℕ) (hH : ∀ i j, j + 1 < i → toReal (H i j) = 0)
    (j : Fin (m + 1)) (i : Fin n) : -- --- CONCL ---
    ((toRealMat A * (Matrix.of fun (r : Fin n) (j : Fin (m + 1)) => toReal (V j)[r]) -
      (Matrix.of fun (r : Fin n) (j : Fin (m + 1)) => toReal (V j)[r]) *
        (Matrix.of fun (i j : Fin (m + 1)) => toReal (H i j)) -
      toReal (H (m + 1) m) • vecMulVec (fun r : Fin n => toReal (V (m + 1))[r])
        (Pi.single (Fin.last m) 1 : Fin (m + 1) → ℝ)) : Mat ℝ n (m + 1)) i j =
    (toRealMat A *ᵥ fun l => toReal (V j)[l]) i -
        ∑ i' : Fin (j + 2), toReal (H i' j) * toReal (V i')[i] := by -- --- PROOF ---
  -- the three parts of the entry: `A V`, `V T` and `τ w e*`
  have hsplit := aux_sum_split (fun a b => toReal (H a b)) (fun a => toReal (V a)[i]) m j
    j.isLt (fun a ha => hH a j ha)
  have e1 : (toRealMat A * (Matrix.of fun (r : Fin n) (j : Fin (m + 1)) => toReal (V j)[r])) i j =
      (toRealMat A *ᵥ fun l => toReal (V j)[l]) i := by
    simp [Matrix.mul_apply, mulVec, dotProduct]
  have e2 : ((Matrix.of fun (r : Fin n) (j : Fin (m + 1)) => toReal (V j)[r]) *
      (Matrix.of fun (i j : Fin (m + 1)) => toReal (H i j))) i j =
      ∑ i' : Fin (m + 1), toReal (H i' j) * toReal (V i')[i] := by
    simp [Matrix.mul_apply, mul_comm]
  have hj : (j = Fin.last m) ↔ ((j : ℕ) = m) := Fin.ext_iff
  -- the last-column term is there for `j = m` only
  have e3 : (toReal (H (m + 1) m) • vecMulVec (fun r : Fin n => toReal (V (m + 1))[r])
      (Pi.single (Fin.last m) 1 : Fin (m + 1) → ℝ)) i j =
      if (j : ℕ) = m then toReal (H (m + 1) j) * toReal (V (m + 1))[i] else 0 := by
    by_cases h : (j : ℕ) = m
    · have := hj.2 h
      rw [if_pos h]
      simp only [Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, this, Pi.single_eq_same,
        mul_one]
      simp [Fin.val_last]
    · have := mt hj.1 h
      simp [Matrix.smul_apply, vecMulVec_apply, this, h, Pi.single_eq_of_ne]
  rw [hsplit, Matrix.sub_apply, Matrix.sub_apply, e1, e2, e3]
  ring


/-- The float arithmetic of the bound: each factor of the real bound is under its rounded-up one. -/
private theorem aux_chain (p q : ℕ) (A : Mat 𝕋 n n) (c : Vec 𝕋 n) (ν : 𝕋)
    (V : ℕ → Vector 𝕋 n) (H : ℕ → ℕ → 𝕋) (m : ℕ) (t μA : 𝕋) (ε : ℕ → 𝕋) (hq : 1 ≤ q)
    (hε : ∀ j, j < m + 1 → ‖fun r => (toRealMat A *ᵥ fun l => toReal (V j)[l]) r -
        ∑ i : Fin (j + 2), toReal (H i j) * toReal (V i)[r]‖₂ ≤ toReal (ε j))
    (ht : 0 ≤ toReal t)
    (μ : 𝕋) (hμ : μ = maximum FloatOps.zero (maximum μA
        (Krylov.quadBoundUp fun i j : Fin (m + 1) => H i j)))
    (hcap : le (mulUp t μ) (nsmulDown (2 ^ (q - 1)) one) = true) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) (toReal t)) (hμ0 : 0 ≤ toReal μ)
    {Pabs τ wnorm : ℝ} (hPabs : 0 ≤ Pabs)
    (hP : Pabs * |τ| = ∏ j ∈ Finset.range (m + 1), |toReal (H (j + 1) j)|)
    (hw0 : 0 ≤ wnorm)
    (hwle : wnorm ≤ toReal (normUp p fun l : Fin n => (V (m + 1))[l]))
    {ρ : ℝ} (hρ : ρ ≤ toReal (Krylov.startErrorFloat p c ν (V 0)))
    (hρ0 : 0 ≤ ρ) : -- --- CONCL ---
    Real.exp (s * toReal μ) *
      (|toReal ν| * (|τ| * wnorm * (Pabs * s ^ (m + 1) / (Nat.factorial (m + 1) : ℝ)) +
        (∑ j : Fin (m + 1), toReal (ε j)) * s) + ρ) ≤
      toReal (Krylov.errorBoundFloat p q μA ε c ν V H (m + 1) t) := by -- --- PROOF ---
  subst hμ
  set μ : 𝕋 := maximum FloatOps.zero (maximum μA
    (Krylov.quadBoundUp fun i j : Fin (m + 1) => H i j)) with hμ
  set X : ℝ := |τ| * wnorm * (Pabs * s ^ (m + 1) / (Nat.factorial (m + 1) : ℝ)) with hXdef
  have hs0 : 0 ≤ s := hs.1
  have hst : s ≤ toReal t := hs.2
  -- the argument of the exponential is within its range
  have hcapR : toReal (mulUp t μ) ≤ 2 ^ q / 2 := by
    have h1 := toReal_le_of_le hcap
    have h2 := nsmulDown_le (2 ^ (q - 1)) (one : 𝕋)
    rw [toReal_one, mul_one] at h2
    refine h1.trans (h2.trans (le_of_eq ?_))
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    simp [pow_succ]
  have hE : Real.exp (s * toReal μ) ≤ toReal (expUp q (mulUp t μ)) :=
    calc Real.exp (s * toReal μ) ≤ Real.exp (toReal (mulUp t μ)) :=
          Real.exp_le_exp.2 ((mul_le_mul_of_nonneg_right hst hμ0).trans (mul_le_mulUp t μ))
      _ ≤ _ := le_expUp q (mulUp t μ) hcapR
  -- the decay product
  set wn : 𝕋 := normUp p (fun l : Fin n => (V (m + 1))[l]) with hwn
  have hdec := Krylov.decayProduct_bound wn t H hw0 hwle ht (m + 1)
  have hX : X ≤
      toReal (Krylov.decayProductFloat wn t H (m + 1)) := by
    refine le_trans ?_ hdec
    have hf : (0 : ℝ) < (Nat.factorial (m + 1) : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hP0 : 0 ≤ ∏ j ∈ Finset.range (m + 1), |toReal (H (j + 1) j)| :=
      Finset.prod_nonneg fun j _ => abs_nonneg _
    calc X
        = wnorm * (Pabs * |τ|) * s ^ (m + 1) / (Nat.factorial (m + 1) : ℝ) := by
          simp only [hXdef]; ring
      _ = wnorm * (∏ j ∈ Finset.range (m + 1), |toReal (H (j + 1) j)|) * s ^ (m + 1) /
          (Nat.factorial (m + 1) : ℝ) := by rw [hP]
      _ ≤ _ := by
        refine div_le_div_of_nonneg_right ?_ hf.le
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs0 hst _) (mul_nonneg hw0 hP0)
  -- the residuals' share and the start vector
  set S : 𝕋 := sumUp fun j : Fin (m + 1) => ε j with hS
  have hSsum : (∑ j : Fin (m + 1), toReal (ε j)) ≤ toReal S := sum_le_sumUp _
  have hS0 : 0 ≤ ∑ j : Fin (m + 1), toReal (ε j) :=
    Finset.sum_nonneg fun j _ => (norm₂_nonneg _).trans (hε j j.isLt)
  have hY : (∑ j : Fin (m + 1), toReal (ε j)) * s ≤ toReal (mulUp S t) :=
    calc _ ≤ (∑ j : Fin (m + 1), toReal (ε j)) * toReal t :=
          mul_le_mul_of_nonneg_left hst hS0
      _ ≤ toReal S * toReal t := mul_le_mul_of_nonneg_right hSsum ht
      _ ≤ _ := mul_le_mulUp _ _
  -- the nonnegative parts and their sum
  have hX0 : 0 ≤ X :=
    mul_nonneg (mul_nonneg (abs_nonneg _) hw0)
      (div_nonneg (mul_nonneg hPabs (pow_nonneg hs0 _)) (Nat.cast_nonneg _))
  have hsum : X +
      (∑ j : Fin (m + 1), toReal (ε j)) * s ≤
      toReal (addUp (Krylov.decayProductFloat wn t H (m + 1)) (mulUp S t)) :=
    (add_le_add hX hY).trans (add_le_addUp _ _)
  have hsum0 : 0 ≤ X +
      (∑ j : Fin (m + 1), toReal (ε j)) * s := add_nonneg hX0 (mul_nonneg hS0 hs0)
  -- the float bound of the whole bracket
  have hB : |toReal ν| * (X +
      (∑ j : Fin (m + 1), toReal (ε j)) * s) + ρ ≤
      toReal (addUp (mulUp (absolute ν) (addUp (Krylov.decayProductFloat wn t H (m + 1))
        (mulUp S t))) (Krylov.startErrorFloat p c ν (V 0))) := by
    refine le_trans ?_ (add_le_addUp _ _)
    refine add_le_add ?_ hρ
    calc |toReal ν| * (X +
          (∑ j : Fin (m + 1), toReal (ε j)) * s)
        ≤ |toReal ν| * toReal (addUp (Krylov.decayProductFloat wn t H (m + 1)) (mulUp S t)) :=
          mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
      _ = toReal (absolute ν) * toReal (addUp (Krylov.decayProductFloat wn t H (m + 1))
          (mulUp S t)) := by rw [toReal_absolute]
      _ ≤ _ := mul_le_mulUp _ _
  have hB0 : 0 ≤ |toReal ν| * (|τ| * wnorm * (Pabs * s ^ (m + 1) /
      (Nat.factorial (m + 1) : ℝ)) + (∑ j : Fin (m + 1), toReal (ε j)) * s) + ρ :=
    add_nonneg (mul_nonneg (abs_nonneg _) hsum0) hρ0
  exact (mul_le_mul hE hB hB0 ((Real.exp_pos _).le.trans hE)).trans (mul_le_mulUp _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem Krylov.error_le_errorBoundFloat (p q : ℕ) (A : Mat 𝕋 n n) (c : Vec 𝕋 n) (ν : 𝕋)
    (V : ℕ → Vector 𝕋 n) (H : ℕ → ℕ → 𝕋) (m : ℕ) (t μA : 𝕋) (ε : ℕ → 𝕋) (hq : 1 ≤ q)
    (hH : ∀ i j, j + 1 < i → toReal (H i j) = 0)
    (hμA : ∀ x : Vec ℝ n, x ⬝ᵥ (toRealMat A *ᵥ x) ≤ toReal μA * (x ⬝ᵥ x))
    (hε : ∀ j, j < m + 1 → ‖fun r => (toRealMat A *ᵥ fun l => toReal (V j)[l]) r -
        ∑ i : Fin (j + 2), toReal (H i j) * toReal (V i)[r]‖₂ ≤ toReal (ε j))
    (ht : 0 ≤ toReal t)
    (hcap : le (mulUp t (maximum zero (maximum μA
        (Krylov.quadBoundUp fun i j : Fin (m + 1) => H i j)))) (nsmulDown (2 ^ (q - 1)) one) =
      true) : -- --- CONCL ---
    ∀ s ∈ Set.Icc (0 : ℝ) (toReal t),
      ‖exp (s • toRealMat A) *ᵥ (fun r => toReal (c r)) -
          toReal ν • ((Matrix.of fun (r : Fin n) (j : Fin (m + 1)) => toReal (V j)[r]) *ᵥ
            (exp (s • Matrix.of fun (i j : Fin (m + 1)) => toReal (H i j)) *ᵥ Pi.single 0 1))‖₂ ≤
        toReal (Krylov.errorBoundFloat p q μA ε c ν V H (m + 1) t) := by -- --- PROOF ---
  intro s hs
  -- the real objects the floats denote
  set Ar : Mat ℝ n n := toRealMat A with hAr
  set Vr : Mat ℝ n (m + 1) := Matrix.of fun (r : Fin n) (j : Fin (m + 1)) => toReal (V j)[r]
    with hVr
  set Tr : Mat ℝ (m + 1) (m + 1) := Matrix.of fun (i j : Fin (m + 1)) => toReal (H i j) with hTr
  set τ : ℝ := toReal (H (m + 1) m) with hτ
  set w : Vec ℝ n := fun r => toReal (V (m + 1))[r] with hw
  set Δ : Mat ℝ n (m + 1) := Ar * Vr - Vr * Tr -
    τ • vecMulVec w (Pi.single (Fin.last m) 1) with hΔ
  set μT : 𝕋 := Krylov.quadBoundUp fun i j : Fin (m + 1) => H i j with hμT
  set μ : 𝕋 := maximum zero (maximum μA μT) with hμ
  have hμ0 : 0 ≤ toReal μ := by
    rw [hμ, toReal_maximum, toReal_zero]; exact le_max_left _ _
  have hμAμ : toReal μA ≤ toReal μ := by
    rw [hμ, toReal_maximum, toReal_maximum, toReal_zero]
    exact le_max_of_le_right (le_max_left _ _)
  have hμTμ : toReal μT ≤ toReal μ := by
    rw [hμ, toReal_maximum, toReal_maximum, toReal_zero]
    exact le_max_of_le_right (le_max_right _ _)
  have hK : Ar * Vr = Vr * Tr + τ • vecMulVec w (Pi.single (Fin.last m) 1) + Δ := by
    rw [hΔ]; abel
  -- the columns of the residual are the ones the float bound covers
  have hcol : ∀ j : Fin (m + 1), ‖fun i => Δ i j‖₂ ≤ toReal (ε j) := by
    intro j
    refine le_trans (le_of_eq ?_) (hε j j.isLt)
    congr 1
    funext i
    exact aux_delta_col A V H m hH j i
  have hHT : ∀ i k : Fin (m + 1), (k : ℕ) + 1 < i → Tr i k = 0 := fun i k hik => by
    simp only [hTr, Matrix.of_apply]; exact hH i k hik
  have hxx : ∀ {l : ℕ} (x : Vec ℝ l), 0 ≤ x ⬝ᵥ x := fun x =>
    Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  have hAμ : ∀ x : Vec ℝ n, x ⬝ᵥ (Ar *ᵥ x) ≤ toReal μ * (x ⬝ᵥ x) := fun x =>
    (hμA x).trans (mul_le_mul_of_nonneg_right hμAμ (hxx x))
  have hTμ : ∀ x : Vec ℝ (m + 1), x ⬝ᵥ (Tr *ᵥ x) ≤ toReal μ * (x ⬝ᵥ x) := fun x =>
    (Krylov.quad_le_quadBoundUp (fun i j : Fin (m + 1) => H i j) x).trans
      (mul_le_mul_of_nonneg_right hμTμ (hxx x))
  -- the start vector
  set ρF : 𝕋 := Krylov.startErrorFloat p c ν (V 0) with hρF
  have hv0 : (Vr *ᵥ (Pi.single 0 1 : Fin (m + 1) → ℝ)) = fun r => toReal (V 0)[r] := by
    funext r
    simp [hVr, mulVec, dotProduct, Pi.single_apply]
  have hc : ‖(fun r => toReal (c r)) - toReal ν • (Vr *ᵥ (Pi.single 0 1 : Fin (m + 1) → ℝ))‖₂ ≤
      toReal ρF := by
    rw [hv0]
    exact Krylov.startError_le_startErrorFloat p c ν (V 0)
  -- the real bound of the error at `s`
  have h := CORALean.Real.Krylov.error_le_column_residual Ar Vr Tr τ w Δ (fun j => toReal (ε j))
    (fun r => toReal (c r)) (toReal ν) (toReal ρF) (toReal μ) hK hcol hc hHT hAμ hTμ hs.1
  refine h.trans ?_
  -- the real bound, then each factor against its float one
  have hP : (|∏ j : Fin m, Tr j.succ j.castSucc|) * |τ| =
      ∏ j ∈ Finset.range (m + 1), |toReal (H (j + 1) j)| := by
    rw [Finset.prod_range_succ, ← Finset.abs_prod, hτ]
    congr 2
    rw [← Fin.prod_univ_eq_prod_range (fun j => toReal (H (j + 1) j)) m]
    simp [hTr]
  exact aux_chain p q A c ν V H m t μA ε hq hε ht μ hμ hcap hs hμ0 (abs_nonneg _) hP
    (norm₂_nonneg w)
    (norm₂_le_normUp p (m := fun l : Fin n => (V (m + 1))[l]) fun j => le_rfl) le_rfl
    ((norm₂_nonneg _).trans hc)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
