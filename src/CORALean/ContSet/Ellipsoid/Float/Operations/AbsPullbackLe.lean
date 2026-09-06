import CORALean.ContSet.Ellipsoid.Float.Operations.PullbackAbs
import CORALean.ContSet.Ellipsoid.Real.Operations.SupportBound
import CORALean.ContSet.InflatedContSet.Operations.Bound

/-!
# The pulled-back direction never leaves `pullbackAbs`

The direction is pulled back through `Gᵀ` by a dot product whose exact value
has either sign, so its magnitude is the larger of the up rounding and the
negated down one.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A functional given by a float vector is the dot product with it, so its
`dualVec` is that vector read as reals. -/
theorem Ellipsoid.aux_dualVec {c : Vec ℝ n →ₗ[ℝ] ℝ} {a : Vec 𝕋 n}
    (hc : ∀ x : Vec ℝ n, c x = ∑ i, toReal (a i) * x i) (i : Fin n) :
    Real.dualVec c i = toReal (a i) := by -- --- PROOF ---
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


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.abs_pullback_le (E : Ellipsoid 𝕋 n) {c : Vec ℝ n →ₗ[ℝ] ℝ} {a : Vec 𝕋 n}
    (hc : ∀ x : Vec ℝ n, c x = ∑ i, toReal (a i) * x i) (j : Fin E.k) :
    |(InflatedContSet.nominal E).pullback c j| ≤ toReal (E.pullbackAbs a j) := by -- --- PROOF ---
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

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
