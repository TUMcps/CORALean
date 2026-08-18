import CORALean.Arithmetic.Real.MatSet.IntervalMat.IntervalMat

/-!
# Interval matrices: enclosing a matrix exponential

Althoff's thesis (2010), Sec. 3.2, Eq. (3.2)–(3.3): truncate the exponential
series at `η` and widen by what the tail can still amount to. The truncation is
the centre, the tail bound the radius.

The bound holds only where the series is dominated by a geometric one, which is
`‖x‖ / (η + 2) < 1` — a joint condition on the step and the order, and the
hypothesis of every theorem here.

`exp` needs a norm on `Mat`, which is a choice rather than an instance, so every
file reasoning about these must make the same one — the `l∞` operator norm.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}

/-- The series truncated at `η`, which is the centre of the enclosure. -/
noncomputable def IntervalMat.expTaylor (x : Mat ℝ n n) (η : ℕ) : Mat ℝ n n :=
  ∑ i ∈ Finset.range (η + 1), ((Nat.factorial i : ℝ)⁻¹) • x ^ i

/-- What the neglected terms can still amount to, which is the radius. Sound
only under `‖x‖ / (η + 2) < 1`; without it the geometric bound diverges and this
is meaningless rather than merely loose. -/
noncomputable def IntervalMat.expRemainderBound (x : Mat ℝ n n) (η : ℕ) : ℝ :=
  (‖x‖ ^ (η + 1) / Nat.factorial (η + 1)) * (1 - ‖x‖ / ((η : ℝ) + 2))⁻¹

noncomputable def IntervalMat.expEnclosure (x : Mat ℝ n n) (η : ℕ) : IntervalMat n n where
  inf := fun i j => IntervalMat.expTaylor x η i j - IntervalMat.expRemainderBound x η
  sup := fun i j => IntervalMat.expTaylor x η i j + IntervalMat.expRemainderBound x η

end CORALean.Arithmetic.Real
