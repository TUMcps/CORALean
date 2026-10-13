import CORALean.ContSet.HPolytope.Float.Operations.ProjectHighDim
import CORALean.ContSet.HPolytope.Float.Operations.MemEqsIff
import CORALean.ContSet.HPolytope.Float.Operations.MemIntersectionIff
import CORALean.ContSet.HPolytope.Float.Theorems.LiftExact

/-!
# `HPolytope.projectHighDim` is exact over a floating-point scalar

The lifted polytope is `P` read at the coordinates `dims` (`lift_exact`, for an injective
`dims`), and the unit rows with the zero interval pin every coordinate `dims` misses to `0`:
the same two conditions as over ℝ, with nothing rounded.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.projectHighDim_exact (P : HPolytope 𝕋 (Vec 𝕋 n)) {dims : Fin n → Fin N}
    (hdims : Function.Injective dims) :
    (P.projectHighDim dims).construct
      = {x | (fun k => x (dims k)) ∈ P.construct
          ∧ ∀ j, (∀ k, dims k ≠ j) → x j = 0} := by -- --- PROOF ---
  ext x
  unfold HPolytope.projectHighDim
  dsimp only
  -- for every finset of the coordinates `dims` leaves out
  suffices key : ∀ s : Finset (Fin N), (∀ j, j ∈ s ↔ ∀ k, dims k ≠ j) →
      (x ∈ ((P.lift_ dims).intersection (HPolytope.eqs
        (fun r j => if j = s.orderEmbOfFin rfl r then (one : 𝕋) else zero)
        ⟨fun _ => zero, fun _ => zero⟩)).construct ↔
      (fun k => x (dims k)) ∈ P.construct ∧ ∀ j, (∀ k, dims k ≠ j) → x j = 0) from
    key _ fun j => by simp
  intro s hs
  rw [HPolytope.mem_intersection_iff, HPolytope.lift_exact P hdims, HPolytope.mem_eqs_iff]
  -- a unit row reads one coordinate
  have hrow : ∀ a : Fin s.card,
      (toRealMat (fun r j => if j = s.orderEmbOfFin rfl r then (one : 𝕋) else zero :
        Mat 𝕋 _ N) *ᵥ x) a = x (s.orderEmbOfFin rfl a) := by
    intro a
    simp [Matrix.mulVec, dotProduct, toRealMat, apply_ite toReal, toReal_one, toReal_zero]
  simp only [hrow]
  refine and_congr Iff.rfl ⟨fun h j hj => ?_, fun h r => ?_⟩
  · -- a coordinate `dims` misses is one of the numbered new ones
    have hr' : j ∈ Set.range (s.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact (hs j).mpr hj
    obtain ⟨r, hr⟩ := hr'
    have := h r
    rw [hr] at this
    simp only [toReal_zero] at this
    exact le_antisymm this.2 this.1
  · have hm := Finset.orderEmbOfFin_mem s rfl r
    have := h _ ((hs _).mp hm)
    simp [this, toReal_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
