import CORALean.NN.Layers.PolyRelaxation

/-!
# A relaxation read at a higher degree

An order pattern gives each neuron of a layer its own order [1, Eq. 23], while
one activation layer evaluates one coefficient list, so the neurons' fits have
to meet at a common degree. Padding with zero coefficients takes them there:
`evalPoly` never sees the added terms and `error` is untouched, so a neuron
below the layer's maximum order pays nothing for the neurons above it.

That exactness is why a common degree is no restriction, and it is what makes a
family of relaxations `Fin n → PolyRelaxation σ M` rather than a ragged one: a
degree per neuron in the *type* would put a `Fin (deg i)` inside the layer's
data and make `evalPoly`'s coefficient list dependently typed.

The padded coefficient is a `dite` on the index rather than a `Fin.castLE`,
which maps the smaller index type and so runs the wrong way.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {σ : ℝ → ℝ} {k M : ℕ}

/-- Coefficients read at degree `M`, the ones the original does not have zero. -/
def padCoeffs (c : Fin (k + 1) → ℝ) (M : ℕ) : Fin (M + 1) → ℝ :=
  fun j => if h : (j : ℕ) < k + 1 then c ⟨(j : ℕ), h⟩ else 0

/-- Padding adds only zero terms, so it changes no value of the polynomial. -/
theorem evalPoly_padCoeffs (c : Fin (k + 1) → ℝ) (h : k ≤ M) (t : ℝ) :
    evalPoly (padCoeffs c M) t = evalPoly c t := by
  -- both sides are one sum over ℕ, cut at a different length
  have hL : evalPoly (padCoeffs c M) t
      = ∑ j ∈ Finset.range (M + 1), (if hj : j < k + 1 then c ⟨j, hj⟩ else 0) * t ^ j := by
    show (∑ i : Fin (M + 1), (if hj : (i : ℕ) < k + 1 then c ⟨(i : ℕ), hj⟩ else 0) * t ^ (i : ℕ))
      = _
    exact Fin.sum_univ_eq_sum_range
      (fun j : ℕ => (if hj : j < k + 1 then c ⟨j, hj⟩ else 0) * t ^ j) (M + 1)
  have hfin : (∑ i : Fin (k + 1),
        (if hj : (i : ℕ) < k + 1 then c ⟨(i : ℕ), hj⟩ else 0) * t ^ (i : ℕ))
      = ∑ j ∈ Finset.range (k + 1), (if hj : j < k + 1 then c ⟨j, hj⟩ else 0) * t ^ j :=
    Fin.sum_univ_eq_sum_range
      (fun j : ℕ => (if hj : j < k + 1 then c ⟨j, hj⟩ else 0) * t ^ j) (k + 1)
  have hR : (∑ j ∈ Finset.range (k + 1), (if hj : j < k + 1 then c ⟨j, hj⟩ else 0) * t ^ j)
      = evalPoly c t := by
    rw [← hfin]
    -- inside `k + 1` the padding branch is never taken
    show _ = ∑ i : Fin (k + 1), c i * t ^ (i : ℕ)
    exact Finset.sum_congr rfl fun j _ => by rw [dif_pos j.isLt]
  rw [hL, ← hR]
  -- and past `k + 1` the padded coefficient is zero, so the term drops out
  have hsub : Finset.range (k + 1) ⊆ Finset.range (M + 1) := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  refine (Finset.sum_subset hsub ?_).symm
  intro j _ hj
  rw [dif_neg (by simpa using hj), zero_mul]

/-- A relaxation at a higher degree, which is how the neurons of one layer meet
at a common one. -/
def PolyRelaxation.padTo (P : PolyRelaxation σ k) (M : ℕ) (h : k ≤ M) : PolyRelaxation σ M where
  coeffs l u := padCoeffs (P.coeffs l u) M
  error := P.error
  sound {_l _u _t} hl hu := by
    rw [evalPoly_padCoeffs _ h]
    exact P.sound hl hu

/-- Padding leaves the error alone, which is what makes it free. -/
theorem PolyRelaxation.padTo_error (P : PolyRelaxation σ k) (M : ℕ) (h : k ≤ M) :
    (P.padTo M h).error = P.error := rfl

end CORALean.Real
