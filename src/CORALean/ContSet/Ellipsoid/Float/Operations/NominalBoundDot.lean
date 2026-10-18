module

public import CORALean.ContSet.Ellipsoid.Float.Theorems.QuadLeQuadUp
public import CORALean.ContSet.Ellipsoid.Float.Theorems.Basic
public import CORALean.ContSet.Ellipsoid.Real.Operations.SupportBound
public import CORALean.Global.Float.EuclideanNorm
public import CORALean.ContSet.InflatedContSet.Operations.Bound

@[expose] public section

/-!
# `Ellipsoid.nominalBoundDot`

The nominal bound, CORA's `supportFunc_` `aᵀq + √(aᵀ Q a)` with the square root replaced by a
proposed length `s`: `hs`, `aᵀ Q a ≤ s²` from above (`quadUp`), is the whole of what the candidate
owes, and it is one float comparison. Through `FloatBound.ofExistsBound`: the exact bound's value
is a square root, so only an existential keeps it out of the float. Where `Q` is refused the
nominal part is the center, and the bound holds the more.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A functional given by a float vector is the dot product with it, so its
`dualVec` is that vector read as reals. -/
theorem Ellipsoid.aux_dualVec {c : Vec ℝ n →ₗ[ℝ] ℝ} {a : Vec 𝕋 n}
    (hc : ∀ x : Vec ℝ n, c x = ∑ i, toReal (a i) * x i) :
    Real.dualVec c = toRealVec a := by -- --- PROOF ---
  funext i
  rw [Real.dualVec, hc, Finset.sum_eq_single i]
  · rw [if_pos rfl, mul_one]
    rfl
  · intro b _ hb
    rw [if_neg (Ne.symm hb), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The exact bound's value covered by the stored float, which is where the
candidate is spent. -/
theorem Ellipsoid.aux_supportBound_le (E : Ellipsoid 𝕋 n) {c : Vec ℝ n →ₗ[ℝ] ℝ}
    {a : Vec 𝕋 n} (hc : ∀ x : Vec ℝ n, c x = ∑ i, toReal (a i) * x i) {s : 𝕋}
    (hs : toReal (E.quadUp a) ≤ toReal (mulDown s s)) : -- --- STMT ---
    ((InflatedContSet.nominal E).ellipsoid.supportBound c).val
      ≤ toReal (addUp (dotUp a E.q) (absolute s)) := by -- --- PROOF ---
  have h₁ : c (InflatedContSet.nominal E).ellipsoid.q ≤ toReal (dotUp a E.q) := by
    rw [hc, E.nominal_q]
    exact le_dotUp a E.q
  -- the nominal quadratic form is the stored one, or `0`
  have hquad : Real.dualVec c ⬝ᵥ ((InflatedContSet.nominal E).ellipsoid.Q *ᵥ Real.dualVec c)
      ≤ max 0 (toReal s * toReal s) := by
    rw [Ellipsoid.aux_dualVec hc, Ellipsoid.nominal_Q_eq]
    split_ifs
    · exact le_trans (le_trans (E.quad_le_quadUp a) (le_trans hs (mulDown_le_mul s s)))
        (le_max_right _ _)
    · simp
  have h₂ :
      Real.sqrt (Real.dualVec c ⬝ᵥ ((InflatedContSet.nominal E).ellipsoid.Q *ᵥ Real.dualVec c))
      ≤ toReal (absolute s) := by
    rw [toReal_absolute, ← Real.sqrt_mul_self (abs_nonneg (toReal s)), abs_mul_abs_self]
    refine le_trans (Real.sqrt_le_sqrt hquad) (Real.sqrt_le_sqrt ?_)
    exact max_le (mul_self_nonneg _) le_rfl
  have h₃ := add_le_addUp (dotUp a E.q) (absolute s)
  show c (InflatedContSet.nominal E).ellipsoid.q + Real.sqrt _ ≤ _
  linarith


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The nominal bound; `hs` is the whole of what the candidate owes, and it is
one float comparison. Through `FloatBound.ofExistsBound`: the exact bound's
value is a square root, so only an existential keeps it out of the float. -/
def Ellipsoid.nominalBoundDot (E : Ellipsoid 𝕋 n) {c : Vec ℝ n →ₗ[ℝ] ℝ} (a : Vec 𝕋 n)
    (hc : ∀ x : Vec ℝ n, c x = ∑ i, toReal (a i) * x i) (s : 𝕋)
    (hs : toReal (E.quadUp a) ≤ toReal (mulDown s s)) :
    FloatBound 𝕋 (nominalSet E) c :=
  FloatBound.ofExistsBound (addUp (dotUp a E.q) (absolute s))
    ⟨(InflatedContSet.nominal E).ellipsoid.supportBound c, E.aux_supportBound_le hc hs⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
