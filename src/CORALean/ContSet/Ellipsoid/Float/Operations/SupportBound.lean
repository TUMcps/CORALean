import CORALean.ContSet.Ellipsoid.Float.Ellipsoid
import CORALean.ContSet.Ellipsoid.Real.Operations.SupportBound
import CORALean.ContSet.InflatedContSet.Operations.Bound
import CORALean.ContSet.Interval.Float.Operations.OfBounds
import CORALean.Global.Float.EuclideanNorm

/-!
# An ellipsoid answers a direction in floats, and still without a linear program

The exact value is `⟨d, q⟩ + ‖Gᵀd‖₂`, and the norm is a square root the scalar
has not got. It needs none: the caller hands in a proposed length `s`, and
`Global.Float.EuclideanNorm` turns `s` into a bound by one multiplication in
each rounding direction, so an ellipsoid costs the layer no new scalar operation.

The candidate is not trusted and is not required to be a square root of
anything, nor even to be positive: a wrong one fails the check and yields no
bound, and a negative one certifies through `absolute`.

Two roundings are chosen before the check. The direction is pulled back through
`Gᵀ` by a dot product whose exact value has either sign, so its magnitude is the
larger of the up rounding and the negated down one — `Zonotope.nominalBoundDot`'s
two-sided choice. The centre's dot product rounds up, once.

The direction arrives as a float vector together with the fact that it denotes
the dot product with it, which a matrix row satisfies by `rfl`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- The magnitude of the direction pulled back into generator space, coordinate
by coordinate. `sqSumUp` of this is what a candidate is checked against. -/
def Ellipsoid.pullbackAbs (E : Ellipsoid 𝕋 n) (a : Vec 𝕋 n) (j : Fin E.k) : 𝕋 :=
  maximum (dotUp a fun i => E.G i j) (neg (dotDown a fun i => E.G i j))

/-- A functional given by a float vector is the dot product with it, so its
`dualVec` is that vector read as reals. -/
theorem Ellipsoid.aux_dualVec {c : Vec ℝ n →ₗ[ℝ] ℝ} {a : Vec 𝕋 n}
    (hc : ∀ x : Vec ℝ n, c x = ∑ i, toReal (a i) * x i) (i : Fin n) :
    Real.dualVec c i = toReal (a i) := by
  rw [Real.dualVec, hc]
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl, mul_one]
  · intro b _ hb
    rw [if_neg (Ne.symm hb), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The pulled-back direction as a dot product of stored floats, which is what
the two roundings bracket. -/
theorem Ellipsoid.aux_pullback (E : Ellipsoid 𝕋 n) {c : Vec ℝ n →ₗ[ℝ] ℝ} {a : Vec 𝕋 n}
    (hc : ∀ x : Vec ℝ n, c x = ∑ i, toReal (a i) * x i) (j : Fin E.k) :
    (InflatedContSet.nominal E).pullback c j = ∑ i, toReal (a i) * toReal (E.G i j) := by
  show ∑ i, toReal (E.G i j) * Real.dualVec c i = _
  exact Finset.sum_congr rfl fun i _ => by
    rw [Ellipsoid.aux_dualVec hc i, mul_comm]

theorem Ellipsoid.abs_pullback_le (E : Ellipsoid 𝕋 n) {c : Vec ℝ n →ₗ[ℝ] ℝ} {a : Vec 𝕋 n}
    (hc : ∀ x : Vec ℝ n, c x = ∑ i, toReal (a i) * x i) (j : Fin E.k) :
    |(InflatedContSet.nominal E).pullback c j| ≤ toReal (E.pullbackAbs a j) := by
  rw [E.aux_pullback hc j, Ellipsoid.pullbackAbs, toReal_maximum, toReal_neg]
  refine abs_le.mpr ⟨?_, ?_⟩
  · have hdown := dotDown_le a fun i => E.G i j
    have hm := le_max_right (toReal (dotUp a fun i => E.G i j))
      (-toReal (dotDown a fun i => E.G i j))
    linarith
  · have hup := le_dotUp a fun i => E.G i j
    have hm := le_max_left (toReal (dotUp a fun i => E.G i j))
      (-toReal (dotDown a fun i => E.G i j))
    linarith

/-- The exact bound's value covered by the stored float, which is where the
candidate is spent. -/
theorem Ellipsoid.aux_supportBound_le (E : Ellipsoid 𝕋 n) {c : Vec ℝ n →ₗ[ℝ] ℝ}
    {a : Vec 𝕋 n} (hc : ∀ x : Vec ℝ n, c x = ∑ i, toReal (a i) * x i) {s : 𝕋}
    (hs : toReal (sqSumUp (E.pullbackAbs a)) ≤ toReal (mulDown s s)) :
    ((InflatedContSet.nominal E).supportBound c).val
      ≤ toReal (addUp (dotUp a E.q) (absolute s)) := by
  have h₁ : c (InflatedContSet.nominal E).q ≤ toReal (dotUp a E.q) := by
    rw [hc]
    exact le_dotUp a E.q
  have h₂ : ‖(InflatedContSet.nominal E).pullback c‖₂ ≤ toReal (absolute s) :=
    norm₂_le_of_sq_le (E.abs_pullback_le hc) hs
  have h₃ := add_le_addUp (dotUp a E.q) (absolute s)
  show c (InflatedContSet.nominal E).q + ‖(InflatedContSet.nominal E).pullback c‖₂ ≤ _
  linarith

/-- The nominal bound; `hs` is the whole of what the candidate owes, and it is
one float comparison. Not `FloatBound.ofSupportBound`: the exact bound's value
is a square root, which would carry noncomputability into a float bound. -/
def Ellipsoid.nominalBoundDot (E : Ellipsoid 𝕋 n) {c : Vec ℝ n →ₗ[ℝ] ℝ} (a : Vec 𝕋 n)
    (hc : ∀ x : Vec ℝ n, c x = ∑ i, toReal (a i) * x i) (s : 𝕋)
    (hs : toReal (sqSumUp (E.pullbackAbs a)) ≤ toReal (mulDown s s)) :
    FloatBound 𝕋 (nominalSet E) c where
  val := addUp (dotUp a E.q) (absolute s)
  le x hx := le_trans (((InflatedContSet.nominal E).supportBound c).le x hx)
    (E.aux_supportBound_le hc hs)

/-- The whole set: the nominal bound and the error box's own, added upward. -/
def Ellipsoid.boundDot (E : Ellipsoid 𝕋 n) {c : Vec ℝ n →ₗ[ℝ] ℝ} (a : Vec 𝕋 n)
    (hc : ∀ x : Vec ℝ n, c x = ∑ i, toReal (a i) * x i) (s : 𝕋)
    (hs : toReal (sqSumUp (E.pullbackAbs a)) ≤ toReal (mulDown s s)) :
    FloatBound 𝕋 E.construct c :=
  InflatedContSet.boundOfParts (E.nominalBoundDot a hc s hs) (E.err.boundDot a hc)

end CORALean.Float
