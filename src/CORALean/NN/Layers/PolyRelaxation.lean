import CORALean.NN.Layers.Activation

/-!
# The polynomial abstraction of an activation function

CORA's `computeApproxPoly` [1, Alg. 1]: on a neuron's input interval the activation is
enclosed by a polynomial of degree `n` and a remaining error, where `Relaxation`
carries the degree-1 case. Spending a higher order on a neuron that deserves it
is the whole precision gain of the refinement loop, and a first-order
abstraction has no way to spend it.

Which polynomial is fitted owes no proof. CORA's `poly_method` picks between
least squares, Taylor, Bernstein and Singh, and every one of them is sound the
moment `sound` holds; a better fit is more precise and never more correct. That
is the freedom `reduceBy_outer` has at every partition, and `Relaxation.ofDeriv`
at every slope inside its bracket.

Coefficients are indexed by degree, `c 0` the constant term, where CORA stores
them highest first. That is what makes the recentring in `PolySampling` a shift
of `c 0` rather than of `coeffs[end]`.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

/-- A polynomial in the monomial basis, `c i` the coefficient of `t ^ i`. -/
def evalPoly {n : ℕ} (c : Fin (n + 1) → ℝ) (t : ℝ) : ℝ := ∑ i, c i * t ^ (i : ℕ)

/-- The derivative of `evalPoly c`, written out rather than differentiated, so
that a caller can bound it without unfolding anything. -/
def evalPolyDeriv {n : ℕ} (c : Fin (n + 1) → ℝ) (t : ℝ) : ℝ :=
  ∑ i, c i * ((i : ℕ) * t ^ ((i : ℕ) - 1))

theorem hasDerivAt_evalPoly {n : ℕ} (c : Fin (n + 1) → ℝ) (t : ℝ) :
    HasDerivAt (evalPoly c) (evalPolyDeriv c t) t := by -- --- PROOF ---
  -- termwise, the power rule scaled by the coefficient
  have hterm : ∀ i : Fin (n + 1), i ∈ Finset.univ →
      HasDerivAt (fun x : ℝ => c i * x ^ (i : ℕ)) (c i * ((i : ℕ) * t ^ ((i : ℕ) - 1))) t :=
    fun i _ => HasDerivAt.const_mul (c i) (hasDerivAt_pow (i : ℕ) t)
  have hsum := HasDerivAt.sum hterm
  -- the sum of the term functions is `evalPoly` itself, read pointwise
  have hfun : (∑ i : Fin (n + 1), fun x : ℝ => c i * x ^ (i : ℕ)) = evalPoly c := by
    funext x
    rw [Finset.sum_apply]
    rfl
  rwa [hfun] at hsum

/-- The constant coefficient moved by `s`, the recentring `computeApproxError`
performs so that what is left of the error is a radius. -/
def shiftConst {n : ℕ} (c : Fin (n + 1) → ℝ) (s : ℝ) : Fin (n + 1) → ℝ :=
  fun i => c i + (if i = 0 then s else 0)

theorem evalPoly_shiftConst {n : ℕ} (c : Fin (n + 1) → ℝ) (s t : ℝ) :
    evalPoly (shiftConst c s) t = evalPoly c t + s := by -- --- PROOF ---
  have hterm : ∀ i : Fin (n + 1), shiftConst c s i * t ^ (i : ℕ)
      = c i * t ^ (i : ℕ) + (if i = 0 then s else 0) := by
    intro i
    by_cases hi : i = 0
    · -- only the constant term is touched, and there `t ^ 0` is one
      rw [hi]
      simp only [shiftConst, Fin.val_zero, pow_zero, mul_one]
    · simp only [shiftConst, if_neg hi, add_zero]
  show ∑ i, shiftConst c s i * t ^ (i : ℕ) = (∑ i, c i * t ^ (i : ℕ)) + s
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (0 : Fin (n + 1)) fun _ => s,
    if_pos (Finset.mem_univ (0 : Fin (n + 1)))]

/-- A degree-1 polynomial as `Relaxation` writes its affine map. -/
theorem evalPoly_one (c : Fin 2 → ℝ) (t : ℝ) : evalPoly c t = c 1 * t + c 0 := by
  show ∑ i, c i * t ^ (i : ℕ) = _
  rw [Fin.sum_univ_two]
  show c 0 * t ^ (0 : ℕ) + c 1 * t ^ (1 : ℕ) = _
  ring

/-- An enclosure of `σ` by a polynomial of degree `n` on every interval, CORA's
`computeApproxPoly` together with the error `computeApproxError` leaves. -/
structure PolyRelaxation (σ : ℝ → ℝ) (n : ℕ) where
  coeffs : ℝ → ℝ → Fin (n + 1) → ℝ
  error : ℝ → ℝ → ℝ
  sound {l u t : ℝ} (hl : l ≤ t) (hu : t ≤ u) :
    |σ t - evalPoly (coeffs l u) t| ≤ error l u

/-- The affine relaxation is the order-1 case: `offset` and `slope` are the two
coefficients, and `sound` is the same inequality read through `evalPoly_one`. -/
def Relaxation.toPoly {σ : ℝ → ℝ} (R : Relaxation σ) : PolyRelaxation σ 1 where
  coeffs l u := ![R.offset l u, R.slope l u]
  error := R.error
  sound {l u _t} hl hu := by
    rw [evalPoly_one]
    show |σ _ - (R.slope l u * _ + R.offset l u)| ≤ R.error l u
    exact R.sound hl hu

/-- And back, so nothing distinguishes the two at order 1: the same data, read
as a slope and an offset rather than as two coefficients. -/
def PolyRelaxation.toRelaxation {σ : ℝ → ℝ} (P : PolyRelaxation σ 1) : Relaxation σ where
  slope l u := P.coeffs l u 1
  offset l u := P.coeffs l u 0
  error := P.error
  sound {l u _t} hl hu := by
    rw [← evalPoly_one (P.coeffs l u)]
    exact P.sound hl hu


-- =======================================  MAIN THEOREM  ======================================= --

/-- The two round-trip, which is what makes "order 1" a reading of `Relaxation`
rather than a second notion standing beside it. -/
theorem Relaxation.toPoly_toRelaxation {σ : ℝ → ℝ} (R : Relaxation σ) :
    R.toPoly.toRelaxation = R := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
