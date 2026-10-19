module

public import CORALean.Global.DmdcData
public import CORALean.Global.DmdCandidateFit
public import CORALean.Global.DmdCandidateLeastSquares

@[expose] public section

/-!
# The dynamic mode decomposition with control fits consistent data and is least squares

Known input matrix [1, Eq. 18]: `Ā = (X' - B Υ) Ṽ Σ̃⁻¹ Ũᵀ`, the candidate for the right-hand
side `X' - B Υ` [1, Eq. 17]. Unknown input matrix: `Ḡ = X' Ṽ Σ̃⁻¹ Ũᵀ` for the SVD
`Ω = Ũ Σ̃ Ṽᵀ` of the stacked snapshots [1, Eq. 26], `[Ā, B̄] = [X' Ṽ Σ̃⁻¹ Ũ₁ᵀ, X' Ṽ Σ̃⁻¹ Ũ₂ᵀ]`
[1, Eq. 28] with
`Ũ = [Ũ₁; Ũ₂]` split at the state rows. At the full rank of `Ω`, no truncation, both reproduce
data that obeys the system, `Ā x_k + B̄ u_k = x_{k+1}`, and minimize the squared error of the
fit; if `Ũ` is square (`r = n`, known `B`), `Ā` is `A`. With `Υ = 0` the formula of [1, Eq. 18]
is that of [1, Eq. 7], as the paper remarks [1, Sec. III-B]. The paper truncates at `p` below
the full rank, which is not covered.

## References

* [1] J. L. Proctor, S. L. Brunton and J. N. Kutz. "Dynamic mode decomposition with control".
      SIAM Journal on Applied Dynamical Systems, 15(1):142-161, 2016 (arXiv:1409.6358).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n l N r p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 18] and the remark after it: with `Υ = 0` the right-hand side `X' - B Υ` is `X'`. -/
theorem dmdcKnownB_zero_input (X2 : Mat ℝ n N) (B : Mat ℝ n l) (V : Mat ℝ p r) (s : Fin r → ℝ)
    (W : Mat ℝ N r) (k : ℕ) :
    dmdCandidate (X2 - B * (0 : Mat ℝ l N)) V s W k = dmdCandidate X2 V s W k := by
  rw [Matrix.mul_zero, sub_zero]

/-- [1, Eq. 18]: for data of `x_{k+1} = A' x_k + B u_k` the candidate for `X' - B Υ`, full
rank, reproduces `X' - B Υ = A' X`. -/
theorem dmdcKnownB_fit (x xNext : Fin N → Vec ℝ n) (u : Fin N → Vec ℝ l) (A' : Mat ℝ n n)
    (B : Mat ℝ n l) (V : Mat ℝ n r) (s : Fin r → ℝ) (W : Mat ℝ N r)
    (hX : dmdcCols x = V * Matrix.diagonal s * Wᵀ) (hV : Vᵀ * V = 1) (hW : Wᵀ * W = 1)
    (hs : ∀ i, s i ≠ 0) (hdata : ∀ k, xNext k = A' *ᵥ x k + B *ᵥ u k) : -- --- STMT ---
    dmdCandidate (dmdcCols xNext - B * dmdcCols u) V s W r * dmdcCols x
      = dmdcCols xNext - B * dmdcCols u := by -- --- PROOF ---
  have h := (dmdc_data_sub x xNext u A' B).mp ((dmdc_data_matrix x xNext u A' B).mp hdata)
  exact dmdCandidate_mul_eq (dmdcCols x) _ V s W hX hV hW hs A' h

/-- [1, Eq. 18]: the candidate for `X' - B Υ` is a least-squares fit of it by `A X`. -/
theorem dmdcKnownB_leastSquares (x xNext : Fin N → Vec ℝ n) (u : Fin N → Vec ℝ l)
    (B : Mat ℝ n l) (V : Mat ℝ n r) (s : Fin r → ℝ) (W : Mat ℝ N r)
    (hX : dmdcCols x = V * Matrix.diagonal s * Wᵀ) (hV : Vᵀ * V = 1) (hW : Wᵀ * W = 1)
    (hs : ∀ i, s i ≠ 0) (A : Mat ℝ n n) : -- --- STMT ---
    ∑ i, ∑ a, ((dmdcCols xNext - B * dmdcCols u
        - dmdCandidate (dmdcCols xNext - B * dmdcCols u) V s W r * dmdcCols x) a i) ^ 2
      ≤ ∑ i, ∑ a, ((dmdcCols xNext - B * dmdcCols u - A * dmdcCols x) a i) ^ 2 :=
  dmdCandidate_leastSquares _ _ V s W hX hV hW hs A

/-- [1, Eq. 44]: a square `Ũ` (`r = n`, the data spans the state space) recovers `A'`. -/
theorem dmdCandidate_eq_of_square (X1 X2 : Mat ℝ n N) (V : Mat ℝ n r) (s : Fin r → ℝ)
    (W : Mat ℝ N r) (hX : X1 = V * Matrix.diagonal s * Wᵀ)
    (hVV : V * Vᵀ = 1) (hW : Wᵀ * W = 1) (hs : ∀ i, s i ≠ 0) (A' : Mat ℝ n n)
    (hdata : X2 = A' * X1) : dmdCandidate X2 V s W r = A' := by -- --- PROOF ---
  have hDD : Matrix.diagonal s * Matrix.diagonal (fun i : Fin r => if (i : ℕ) < r then (s i)⁻¹
      else 0) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; simp [i.isLt, mul_inv_cancel₀ (hs i)]
  unfold dmdCandidate
  rw [hdata, hX]
  calc A' * (V * Matrix.diagonal s * Wᵀ) * W
        * Matrix.diagonal (fun i : Fin r => if (i : ℕ) < r then (s i)⁻¹ else 0) * Vᵀ
      = A' * V * (Matrix.diagonal s * ((Wᵀ * W)
        * Matrix.diagonal (fun i : Fin r => if (i : ℕ) < r then (s i)⁻¹ else 0))) * Vᵀ := by
        simp only [Matrix.mul_assoc]
    _ = A' := by rw [hW, Matrix.one_mul, hDD, Matrix.mul_one, Matrix.mul_assoc, hVV,
      Matrix.mul_one]

/-- [1, Eq. 26]: for data of `x_{k+1} = A' x_k + B' u_k` the candidate `Ḡ` for `X'` from the
SVD of `Ω`, full rank, gives `Ā x_k + B̄ u_k = x_{k+1}` (`[Ā, B̄]` the blocks of `Ḡ`). -/
theorem dmdcUnknownB_fit (x xNext : Fin N → Vec ℝ n) (u : Fin N → Vec ℝ l) (A' : Mat ℝ n n)
    (B' : Mat ℝ n l) (V : Mat ℝ (n + l) r) (s : Fin r → ℝ) (W : Mat ℝ N r)
    (hΩ : dmdcCols (fun k => dmdcRegressor (x k) (u k)) = V * Matrix.diagonal s * Wᵀ)
    (hV : Vᵀ * V = 1) (hW : Wᵀ * W = 1) (hs : ∀ i, s i ≠ 0)
    (hdata : ∀ k, xNext k = A' *ᵥ x k + B' *ᵥ u k) (k : Fin N) : -- --- STMT ---
    (dmdcBlocks (dmdCandidate (dmdcCols xNext) V s W r)).1 *ᵥ x k
      + (dmdcBlocks (dmdCandidate (dmdcCols xNext) V s W r)).2 *ᵥ u k
      = xNext k := by -- --- PROOF ---
  have hG := (dmdc_data_stack x xNext u A' B').mp hdata
  have hfit := dmdCandidate_mul_eq _ _ V s W hΩ hV hW hs _ hG
  rw [← dmdcBlocks_mulVec]
  funext i
  have := congrFun (congrFun hfit i) k
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, dmdcCols] using this

/-- [1, Eq. 26]: `Ḡ` is a least-squares fit of `X'` by `G Ω`. -/
theorem dmdcUnknownB_leastSquares (x xNext : Fin N → Vec ℝ n) (u : Fin N → Vec ℝ l)
    (V : Mat ℝ (n + l) r) (s : Fin r → ℝ) (W : Mat ℝ N r)
    (hΩ : dmdcCols (fun k => dmdcRegressor (x k) (u k)) = V * Matrix.diagonal s * Wᵀ)
    (hV : Vᵀ * V = 1) (hW : Wᵀ * W = 1) (hs : ∀ i, s i ≠ 0) (G : Mat ℝ n (n + l)) : -- --- STMT ---
    ∑ i, ∑ a, ((dmdcCols xNext - dmdCandidate (dmdcCols xNext) V s W r
        * dmdcCols (fun k => dmdcRegressor (x k) (u k))) a i) ^ 2
      ≤ ∑ i, ∑ a, ((dmdcCols xNext
        - G * dmdcCols (fun k => dmdcRegressor (x k) (u k))) a i) ^ 2 :=
  dmdCandidate_leastSquares _ _ V s W hΩ hV hW hs G

/-- [1, Eq. 28]: the blocks of `Ḡ = X' Ṽ Σ̃⁻¹ Ũᵀ` are `X' Ṽ Σ̃⁻¹ Ũ₁ᵀ` and
`X' Ṽ Σ̃⁻¹ Ũ₂ᵀ`, `Ũ₁`, `Ũ₂` the state and input rows of `Ũ`. -/
theorem dmdcBlocks_candidate (X2 : Mat ℝ n N) (V : Mat ℝ (n + l) r) (s : Fin r → ℝ)
    (W : Mat ℝ N r) (q : ℕ) : -- --- STMT ---
    dmdcBlocks (dmdCandidate X2 V s W q)
      = (X2 * W * Matrix.diagonal (fun i : Fin r => if (i : ℕ) < q then (s i)⁻¹ else 0)
          * (Matrix.of fun a j => V (Fin.castAdd l a) j)ᵀ,
         X2 * W * Matrix.diagonal (fun i : Fin r => if (i : ℕ) < q then (s i)⁻¹ else 0)
          * (Matrix.of fun b j => V (Fin.natAdd n b) j)ᵀ) := by -- --- PROOF ---
  unfold dmdCandidate dmdcBlocks
  ext i j <;> simp [Matrix.mul_apply, Matrix.transpose_apply]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
