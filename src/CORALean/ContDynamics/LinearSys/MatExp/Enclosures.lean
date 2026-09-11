import CORALean.ContSet.Interval.Real.Interval

/-!
# Interval matrices: enclosing a matrix exponential

[1, Eq. (3.2)–(3.3)]: truncate the exponential series at `η` and widen
by what the tail can still amount to. The truncation is the centre, the tail
bound the radius.

The bound holds only where the series is dominated by a geometric one, which is
`‖x‖ / (η + 2) < 1` — a joint condition on the step and the order, and the
hypothesis of every theorem here.

`exp` needs a norm on `Mat`, which is a choice rather than an instance, so every
file reasoning about these must make the same one — the `l∞` operator norm.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}

/-- The series truncated at `η`, which is the centre of the enclosure. -/
noncomputable def MatExp.expTaylor (x : Mat ℝ n n) (η : ℕ) : Mat ℝ n n :=
  ∑ i ∈ Finset.range (η + 1), ((Nat.factorial i : ℝ)⁻¹) • x ^ i

/-- What the neglected terms can still amount to, which is the radius. Sound
only under `‖x‖ / (η + 2) < 1`; without it the geometric bound diverges and this
is meaningless rather than merely loose. -/
noncomputable def MatExp.expRemainderBound (x : Mat ℝ n n) (η : ℕ) : ℝ :=
  (‖x‖ ^ (η + 1) / Nat.factorial (η + 1)) * (1 - ‖x‖ / ((η : ℝ) + 2))⁻¹

noncomputable def MatExp.expEnclosure (x : Mat ℝ n n) (η : ℕ) : Interval (Mat ℝ n n) where
  inf := fun i j => MatExp.expTaylor x η i j - MatExp.expRemainderBound x η
  sup := fun i j => MatExp.expTaylor x η i j + MatExp.expRemainderBound x η

/-- The `E(r) · r` of [1]: what the orders past `η` contribute to an input
solution over a step, the exponential's remainder bound scaled by the step and
constant in the entry, the bound being on the norm. -/
noncomputable def MatExp.inputRemainder (A : Mat ℝ n n) (r : ℝ) (η : ℕ) :
    Interval (Mat ℝ n n) where
  inf := fun _ _ => -(r * MatExp.expRemainderBound (r • A) η)
  sup := fun _ _ => r * MatExp.expRemainderBound (r • A) η

/-- `∫₀ᵗ e^{Aσ} dσ`, as the series `∑ᵢ Aⁱ t^{i+1}/(i+1)!`: `Matrix` carries no
metrizable-space instance Bochner integration can see, so `expIntegral_mulVec`
ties it back to the integral one vector at a time. -/
noncomputable def MatExp.expIntegral (A : Mat ℝ n n) (t : ℝ) : Mat ℝ n n :=
  ∑' i : ℕ, (((Nat.factorial (i + 1) : ℝ))⁻¹ * t ^ (i + 1)) • A ^ i

/-- Where `s ↦ s ^ i - s` bottoms out: `i ^ (-1/(i-1))`, the only stationary
point, and the minimum because the map is convex. -/
noncomputable def MatExp.corrCritical (i : ℕ) : ℝ :=
  (i : ℝ) ^ (-(1:ℝ) / ((i : ℝ) - 1))

/-- How far below zero `s ^ i - s` reaches on `[0,1]`. [1] writes this
`i^(-i/(i-1)) - i^(-1/(i-1))`, which `aux_corrCoeff_eq` confirms; in this form the
exponent is a natural number and the bound is provable as stated. -/
noncomputable def MatExp.corrCoeff (i : ℕ) : ℝ :=
  MatExp.corrCritical i ^ i - MatExp.corrCritical i

/-- What order `i` contributes to the correction, at the far end of its range.
The interval it spans is between this and zero, on whichever side its sign puts
it. -/
noncomputable def MatExp.corrTerm (A : Mat ℝ n n) (r : ℝ) (i : ℕ) (j k : Fin n) : ℝ :=
  MatExp.corrCoeff i * r ^ i * (((Nat.factorial i : ℝ))⁻¹ * (A ^ i) j k)

/-- What order `i+2` contributes to the *integrated* correction. The same shape
as `corrTerm`, one factorial further along and one matrix power back, which is
what integrating each order of the exponential does to it. -/
noncomputable def MatExp.constCorrTerm (A : Mat ℝ n n) (r : ℝ) (i : ℕ) (j k : Fin n) :
    ℝ :=
  MatExp.corrCoeff (i + 2) * r ^ (i + 2)
    * (((Nat.factorial (i + 2) : ℝ))⁻¹ * (A ^ (i + 1)) j k)

/-- The `F̃ = A⁻¹F` of [1], without the inverse: orders `1` through `η` of
`∫₀ᵗ e^{Aσ}dσ - (t/r)∫₀ʳ e^{Aσ}dσ` exactly, and everything past `η` in `E(r)·r`,
integrating the exponential's tail scaling it by at most the step. -/
noncomputable def MatExp.constCorrectionMatrix (A : Mat ℝ n n) (r : ℝ) (η : ℕ) :
    Interval (Mat ℝ n n) where
  inf := fun j k => (∑ i ∈ Finset.range η, min (MatExp.constCorrTerm A r i j k) 0)
    - r * MatExp.expRemainderBound (r • A) η
  sup := fun j k => (∑ i ∈ Finset.range η, max (MatExp.constCorrTerm A r i j k) 0)
    + r * MatExp.expRemainderBound (r • A) η


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `F` of [1]: the orders up to `η` exactly, everything past `η` in the same
remainder that bounds the exponential, and indexed from `2`, the constant and
linear terms of the interpolation error cancelling. -/
noncomputable def MatExp.correctionMatrix (A : Mat ℝ n n) (r : ℝ) (η : ℕ) :
    Interval (Mat ℝ n n) where
  inf := fun j k => (∑ i ∈ Finset.range (η - 1), min (MatExp.corrTerm A r (i + 2) j k) 0)
    - MatExp.expRemainderBound (r • A) η
  sup := fun j k => (∑ i ∈ Finset.range (η - 1), max (MatExp.corrTerm A r (i + 2) j k) 0)
    + MatExp.expRemainderBound (r • A) η

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
