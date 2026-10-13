module

public import CORALean.ContSet.Ellipsoid.Float.Operations.AbsPullbackLe
public import CORALean.Global.Float.EuclideanNorm

@[expose] public section

/-!
# `Ellipsoid.nominalBoundDot`

The nominal bound; `hs` is the whole of what the candidate owes, and it is one
float comparison. Through `FloatBound.ofExistsBound`: the exact bound's value
is a square root, so only an existential keeps it out of the float.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   07-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The exact bound's value covered by the stored float, which is where the
candidate is spent. -/
theorem Ellipsoid.aux_supportBound_le (E : Ellipsoid 𝕋 n) {c : Vec ℝ n →ₗ[ℝ] ℝ}
    {a : Vec 𝕋 n} (hc : ∀ x : Vec ℝ n, c x = ∑ i, toReal (a i) * x i) {s : 𝕋}
    (hs : toReal (sqSumUp (E.pullbackAbs a)) ≤ toReal (mulDown s s)) :
    ((InflatedContSet.nominal E).supportBound c).val
      ≤ toReal (addUp (dotUp a E.q) (absolute s)) := by -- --- PROOF ---
  have h₁ : c (InflatedContSet.nominal E).q ≤ toReal (dotUp a E.q) := by
    rw [hc]
    exact le_dotUp a E.q
  have h₂ : ‖(InflatedContSet.nominal E).pullback c‖₂ ≤ toReal (absolute s) :=
    norm₂_le_of_sq_le (E.abs_pullback_le hc) hs
  have h₃ := add_le_addUp (dotUp a E.q) (absolute s)
  show c (InflatedContSet.nominal E).q + ‖(InflatedContSet.nominal E).pullback c‖₂ ≤ _
  linarith


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The nominal bound; `hs` is the whole of what the candidate owes, and it is
one float comparison. Through `FloatBound.ofExistsBound`: the exact bound's
value is a square root, so only an existential keeps it out of the float. -/
def Ellipsoid.nominalBoundDot (E : Ellipsoid 𝕋 n) {c : Vec ℝ n →ₗ[ℝ] ℝ} (a : Vec 𝕋 n)
    (hc : ∀ x : Vec ℝ n, c x = ∑ i, toReal (a i) * x i) (s : 𝕋)
    (hs : toReal (sqSumUp (E.pullbackAbs a)) ≤ toReal (mulDown s s)) :
    FloatBound 𝕋 (nominalSet E) c :=
  FloatBound.ofExistsBound (addUp (dotUp a E.q) (absolute s))
    ⟨(InflatedContSet.nominal E).supportBound c, E.aux_supportBound_le hc hs⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
