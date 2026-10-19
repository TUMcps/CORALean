module

public import CORALean.ContSet.Ellipsoid.Float.Operations.EnclosePointsCov
public import CORALean.ContSet.Ellipsoid.Float.Theorems.AddSubMemNominalSet
public import CORALean.ContSet.Ellipsoid.Float.Theorems.InflateSubPosSemidef
public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructOfFactor
public import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Float.Theorems.Basic

@[expose] public section

/-!
# The float `enclosePoints` with `'cov'` encloses the points

Outer: every point lies in `Ellipsoid.enclosePointsCov steps pts T U`, for every `T`, `U` and
`steps`, with no orthogonality or spanning hypothesis, unlike the real layer's
`Real.Ellipsoid.enclosePointsCov_mem`. The point's factor vector has square sum at most `1`, either
certified or `0`, so `c + G u` is in the ellipsoid of `G Gᵀ`, which the stored shape dominates
(`inflate_sub_posSemidef`), so in the nominal part (`add_sub_mem_nominalSet`); the remainder lies
between the two roundings the error box was hulled from. Not exact.

## Inputs
* `steps` – Newton steps for `sqrt maxDist`
* `pts` – points
* `T` – rotation proposed by the caller
* `U` – rotation proposed by the caller
* `j` – point index

## Hypotheses
* none

## Conclusion
* every point lies in the enclosing ellipsoid
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n N : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point is in the set when the stored shape dominates `G Gᵀ` and some factor vector of length
at most `1` leaves a remainder whose two roundings lie in the error box. -/
theorem Ellipsoid.aux_mem_of_remainder (E : Ellipsoid 𝕋 n) (G : Mat 𝕋 n n)
    (hG : (toRealMat E.Q - toRealMat G * (toRealMat G)ᵀ).PosSemidef) (p u : Vec 𝕋 n)
    (hsq : ∑ j, toReal (u j) ^ 2 ≤ 1)
    (hlo : ∀ i, toReal (E.I_error.inf i)
      ≤ toReal (subDown (p i) (addUp (E.q i) (dotUp (G i) u))))
    (hhi : ∀ i, toReal (subUp (p i) (addDown (E.q i) (dotDown (G i) u)))
      ≤ toReal (E.I_error.sup i)) : -- --- CONCL ---
    toRealVec p ∈ E.construct := by -- --- PROOF ---
  -- the factor vector has length at most one
  have hnorm : ‖toRealVec u‖₂ ≤ 1 := by
    have h2 : ‖toRealVec u‖₂ ^ 2 ≤ 1 ^ 2 := by
      rw [norm₂_sq, one_pow]
      exact hsq
    exact (pow_le_pow_iff_left₀ (norm₂_nonneg _) zero_le_one two_ne_zero).mp h2
  -- the nominal point `q + G u`, in the ellipsoid of `G Gᵀ`, so in the nominal part
  have hF : toRealVec E.q + toRealMat G *ᵥ toRealVec u
      ∈ (Real.Ellipsoid.ofFactor (toRealMat G) (toRealVec E.q)).construct := by
    rw [Real.Ellipsoid.construct_ofFactor]
    exact ⟨toRealVec u, hnorm, rfl⟩
  have hy := Ellipsoid.add_sub_mem_nominalSet (Or.inr hG) hF
  rw [show (Real.Ellipsoid.ofFactor (toRealMat G) (toRealVec E.q)).q = toRealVec E.q from rfl,
    add_sub_cancel] at hy
  refine ⟨_, hy, toRealVec p - (toRealVec E.q + toRealMat G *ᵥ toRealVec u), fun i => ?_,
    by abel⟩
  -- the remainder lies between the two roundings the box was compared with
  have d₁ : (toRealMat G *ᵥ toRealVec u) i ≤ toReal (dotUp (G i) u) := le_dotUp (G i) u
  have d₂ : toReal (dotDown (G i) u) ≤ (toRealMat G *ᵥ toRealVec u) i := dotDown_le (G i) u
  have a₁ := add_le_addUp (E.q i) (dotUp (G i) u)
  have a₂ := addDown_le_add (E.q i) (dotDown (G i) u)
  have s₁ := subDown_le_sub (p i) (addUp (E.q i) (dotUp (G i) u))
  have s₂ := sub_le_subUp (p i) (addDown (E.q i) (dotDown (G i) u))
  have l₁ := hlo i
  have l₂ := hhi i
  show toReal (E.I_error.inf i) ≤ toReal (p i) - (toReal (E.q i) + _)
    ∧ toReal (p i) - (toReal (E.q i) + _) ≤ toReal (E.I_error.sup i)
  constructor <;> linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.enclosePointsCov_mem (steps : ℕ) (pts : Fin N → Vec 𝕋 n) (T U : Mat 𝕋 n n)
    (j : Fin N) :
    toRealVec (pts j) ∈ (Ellipsoid.enclosePointsCov steps pts T U).construct := by -- --- PROOF ---
  unfold Ellipsoid.enclosePointsCov
  extract_lets cV c OV orientedMatrix ntV nt maxDist r D TUV GV G shrink uV u lo hi err
  refine Ellipsoid.aux_mem_of_remainder _ G ?_ _ (u j) ?_ (fun i => ?_) (fun i => ?_)
  · -- the stored shape dominates `G Gᵀ`
    refine Ellipsoid.inflate_sub_posSemidef (Interval.mem_mat_iff.mp ?_) fun i k => ?_
    · exact Interval.matMul_outer _ _ (Interval.mem_point G) (Interval.mem_point Gᵀ)
    · simp only [Matrix.mul_apply, Matrix.transpose_apply]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
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
