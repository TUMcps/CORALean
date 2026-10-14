module

public import CORALean.ContSet.Ellipsoid.Float.Operations.EnclosePointsCov
public import CORALean.ContSet.Ellipsoid.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Interval.Float.Theorems.Basic

@[expose] public section

/-!
# The float `enclosePoints` with `'cov'` encloses the points

Outer: every point lies in `Ellipsoid.enclosePointsCov steps pts T U`, for every `T`, `U` and
`steps`, with no orthogonality or spanning hypothesis, unlike the real layer's
`Real.Ellipsoid.enclosePointsCov_mem`. The point's factor vector has square sum at most `1`, either
certified or `0`, so `c + G u` is in the nominal ellipsoid; the remainder lies between the two
roundings the error box was hulled from. Not exact.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n N : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point is in the set when some factor vector of length at most `1` leaves a remainder whose
two roundings lie in the error box. -/
theorem Ellipsoid.aux_mem_of_remainder (E : Ellipsoid 𝕋 n) (p : Vec 𝕋 n) (u : Vec 𝕋 E.k)
    (hsq : ∑ j, toReal (u j) ^ 2 ≤ 1)
    (hlo : ∀ i, toReal (E.I_error.inf i)
      ≤ toReal (subDown (p i) (addUp (E.q i) (dotUp (fun j => E.G i j) u))))
    (hhi : ∀ i, toReal (subUp (p i) (addDown (E.q i) (dotDown (fun j => E.G i j) u)))
      ≤ toReal (E.I_error.sup i)) :
    toRealVec p ∈ E.construct := by -- --- PROOF ---
  -- the factor vector has length at most one
  have hnorm : ‖toRealVec u‖₂ ≤ 1 := by
    have h2 : ‖toRealVec u‖₂ ^ 2 ≤ 1 ^ 2 := by
      rw [norm₂_sq, one_pow]
      exact hsq
    exact (pow_le_pow_iff_left₀ (norm₂_nonneg _) zero_le_one two_ne_zero).mp h2
  -- the nominal point `q + G u`, and the remainder in the box
  refine ⟨fun i => toReal (E.q i) + ∑ j, toReal (E.G i j) * toRealVec u j,
    Ellipsoid.mem_nominalSet_iff.mpr ⟨toRealVec u, hnorm, fun _ => rfl⟩,
    fun i => toReal (p i) - (toReal (E.q i) + ∑ j, toReal (E.G i j) * toRealVec u j),
    fun i => ?_, ?_⟩
  · -- the remainder lies between the two roundings the box was compared with
    have d₁ := le_dotUp (fun j => E.G i j) u
    have d₂ := dotDown_le (fun j => E.G i j) u
    have a₁ := add_le_addUp (E.q i) (dotUp (fun j => E.G i j) u)
    have a₂ := addDown_le_add (E.q i) (dotDown (fun j => E.G i j) u)
    have s₁ := subDown_le_sub (p i) (addUp (E.q i) (dotUp (fun j => E.G i j) u))
    have s₂ := sub_le_subUp (p i) (addDown (E.q i) (dotDown (fun j => E.G i j) u))
    have l₁ := hlo i
    have l₂ := hhi i
    show toReal (E.I_error.inf i)
        ≤ toReal (p i) - (toReal (E.q i) + ∑ j, toReal (E.G i j) * toReal (u j))
      ∧ toReal (p i) - (toReal (E.q i) + ∑ j, toReal (E.G i j) * toReal (u j))
        ≤ toReal (E.I_error.sup i)
    constructor <;> linarith
  · -- the point is the nominal point plus the remainder
    funext i
    simp only [Pi.add_apply, toRealVec]
    ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.enclosePointsCov_mem (steps : ℕ) (pts : Fin N → Vec 𝕋 n) (T U : Mat 𝕋 n n)
    (j : Fin N) :
    toRealVec (pts j) ∈ (Ellipsoid.enclosePointsCov steps pts T U).construct := by -- --- PROOF ---
  unfold Ellipsoid.enclosePointsCov
  extract_lets cV c OV orientedMatrix ntV nt maxDist r D TUV GV G shrink uV u lo hi err
  refine Ellipsoid.aux_mem_of_remainder _ _ (u j) ?_ (fun i => ?_) (fun i => ?_)
  · -- the factor vector is either certified or zero
    show ∑ i : Fin n, toReal ((uV[j.val]'j.isLt)[i.val]'i.isLt) ^ 2 ≤ 1
    simp only [uV, Vector.getElem_ofFn]
    split_ifs with h
    · exact le_trans (sq_sum_le_sqSumUp fun i => by rw [toReal_absolute]; simp)
        ((toReal_le_of_le h).trans_eq toReal_one)
    · simp [toReal_zero]
  · -- the box's lower end is under this point's lower rounding
    show toReal (err.inf i) ≤ toReal (lo j i)
    simp only [err, Interval.materialise_eq]
    exact minimumOver_le (fun j => lo j i) j
  · show toReal (hi j i) ≤ toReal (err.sup i)
    simp only [err, Interval.materialise_eq]
    exact le_maximumOver (fun j => hi j i) j

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
