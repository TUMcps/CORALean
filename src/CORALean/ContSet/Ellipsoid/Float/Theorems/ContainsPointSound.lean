import CORALean.ContSet.Ellipsoid.Float.Operations.ContainsPoint
import CORALean.ContSet.Ellipsoid.Float.Theorems.MemNominalSet

/-!
# A `true` from `Ellipsoid.containsPoint` proves membership

The certificate read as reals has `‖u‖₂ ≤ 1` (its square sum is at most `1`), so `q + G u` is in
the nominal ellipsoid, and the remainder `p - q - G u` lies between the two directed roundings
the test compared with the error box, so in the box.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.containsPoint_sound {E : Ellipsoid 𝕋 n} {p : Vec 𝕋 n} {u : Vec 𝕋 E.k}
    (h : E.containsPoint p u = true) : toRealVec p ∈ E.construct := by -- --- PROOF ---
  simp only [Ellipsoid.containsPoint, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨hu, hbox⟩ := h
  -- the certificate has length at most one
  have hsq : ∑ j, toReal (u j) ^ 2 ≤ 1 :=
    le_trans (sq_sum_le_sqSumUp fun j => by rw [toReal_absolute])
      ((toReal_le_of_le hu).trans_eq toReal_one)
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
  · -- the remainder lies between the two roundings the test compared with the box
    obtain ⟨hlo, hhi⟩ := hbox i
    have d₁ := le_dotUp (fun j => E.G i j) u
    have d₂ := dotDown_le (fun j => E.G i j) u
    have a₁ := add_le_addUp (E.q i) (dotUp (fun j => E.G i j) u)
    have a₂ := addDown_le_add (E.q i) (dotDown (fun j => E.G i j) u)
    have s₁ := subDown_le_sub (p i) (addUp (E.q i) (dotUp (fun j => E.G i j) u))
    have s₂ := sub_le_subUp (p i) (addDown (E.q i) (dotDown (fun j => E.G i j) u))
    have l₁ := toReal_le_of_le hlo
    have l₂ := toReal_le_of_le hhi
    show toReal (E.err.inf i)
        ≤ toReal (p i) - (toReal (E.q i) + ∑ j, toReal (E.G i j) * toReal (u j))
      ∧ toReal (p i) - (toReal (E.q i) + ∑ j, toReal (E.G i j) * toReal (u j))
        ≤ toReal (E.err.sup i)
    constructor <;> linarith
  · -- the point is the nominal point plus the remainder
    funext i
    simp only [Pi.add_apply, toRealVec]
    ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
