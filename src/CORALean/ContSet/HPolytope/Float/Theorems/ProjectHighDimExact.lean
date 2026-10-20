module

public import CORALean.ContSet.HPolytope.Float.Theorems.MemNominalIffExact
public import CORALean.ContSet.HPolytope.Float.Operations.ProjectHighDim
public import CORALean.ContSet.HPolytope.Float.Operations.MemLiftNominalIff
public import CORALean.ContSet.HPolytope.Float.Operations.MemStackRowsNominalIff
public import CORALean.ContSet.HPolytope.Float.Theorems.LiftExact
public import CORALean.ContSet.HPolytope.Float.Theorems.PreimageAddImage

@[expose] public section

/-!
# `HPolytope.projectHighDim` is exact over a floating-point scalar

The lifted polytope is `P` read at the coordinates `dims` (`lift_exact`, for an injective
`dims`), and the unit rows with the right-hand side `0` pin every coordinate `dims` misses to
`0`: the same two conditions as over ℝ, with nothing rounded. The lifted error box is `0` in those
coordinates too, so it moves the selected ones only.

## Inputs
* `P` – H-polytope
* `dims` – indices indexed by `Fin n`

## Hypotheses
* `hdims` – `dims` is injective

## Conclusion
* `HPolytope.projectHighDim` is exact over a floating-point scalar
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.projectHighDim_exact (P : HPolytope 𝕋 (Vec 𝕋 n)) {dims : Fin n → Fin N}
    (hdims : Function.Injective dims) : -- --- CONCL ---
    (P.projectHighDim dims).construct
      = {x | (fun k => x (dims k)) ∈ P.construct
          ∧ ∀ j, (∀ k, dims k ≠ j) → x j = 0} := by -- --- PROOF ---
  unfold HPolytope.projectHighDim
  dsimp only
  -- for every finset of the coordinates `dims` leaves out
  suffices key : ∀ s : Finset (Fin N), (∀ j, j ∈ s ↔ ∀ k, dims k ≠ j) →
      ({ (P.lift_ dims).stackRows (HPolytope.eqs
          (fun r j => if j = s.orderEmbOfFin rfl r then (one : 𝕋) else zero)
          (fun _ => zero)) with I_error := (P.lift_ dims).I_error }
        : HPolytope 𝕋 (Vec 𝕋 N)).construct
        = {x | (fun k => x (dims k)) ∈ P.construct ∧ ∀ j, (∀ k, dims k ≠ j) → x j = 0} from
    key _ fun j => by simp
  intro s hs
  -- the unit rows of the new coordinates, and the description they complete
  set R : Mat 𝕋 s.card N := fun r j => if j = s.orderEmbOfFin rfl r then (one : 𝕋) else zero
    with hR
  set X : HPolytope 𝕋 (Vec 𝕋 N) := { (P.lift_ dims).stackRows (HPolytope.eqs R fun _ => zero)
    with I_error := (P.lift_ dims).I_error } with hX
  -- the pinned coordinates, as a constraint a shift by the lifted box does not notice
  have hS : ∀ (e : Vec ℝ n) (j : Fin N), (∀ k, dims k ≠ j) →
      Function.ExtendByZero.hom ℝ dims e j = 0 := fun e j hj => by
    rw [Function.ExtendByZero.hom_apply, Function.extend_apply' _ _ _ (by simpa using hj)]
    rfl
  have hN : InflatedContSet.nominalSet X
      = ⇑(LinearMap.funLeft ℝ ℝ dims).toAddMonoidHom ⁻¹' P.nominal.construct
        ∩ {x | ∀ j, (∀ k, dims k ≠ j) → x j = 0} := by
    ext y
    show y ∈ ((P.lift_ dims).stackRows (HPolytope.eqs R fun _ => zero)).nominal.construct ↔
      (fun k => y (dims k)) ∈ P.nominal.construct ∧ ∀ j, (∀ k, dims k ≠ j) → y j = 0
    rw [HPolytope.mem_stackRows_nominal_iff, HPolytope.mem_lift_nominal_iff P hdims]
    refine and_congr Iff.rfl ?_
    rw [HPolytope.mem_nominal_iff_exact ⟨fun _ => toReal_zero, fun _ => toReal_zero⟩]
    -- a unit row reads one coordinate
    have hrow : ∀ a : Fin s.card, (toRealMat R *ᵥ y) a = y (s.orderEmbOfFin rfl a) := by
      intro a
      simp [hR, Matrix.mulVec, dotProduct, toRealMat, apply_ite toReal, toReal_one, toReal_zero]
    constructor
    -- the pinned coordinates are the new ones, and the rows say they are zero
    · rintro ⟨-, h⟩ j hj
      -- a coordinate `dims` misses is one of the numbered new ones
      have hr' : j ∈ Set.range (s.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]
        exact (hs j).mpr hj
      obtain ⟨r, hr⟩ := hr'
      have := h r
      simp only [HPolytope.eqs, hrow, toReal_zero] at this
      rw [hr] at this
      exact this
    -- and conversely a zero there meets every unit row
    · intro h
      refine ⟨fun i => i.elim0, fun r => ?_⟩
      have hm := Finset.orderEmbOfFin_mem s rfl r
      have := h _ ((hs _).mp hm)
      simp only [HPolytope.eqs, hrow, toReal_zero]
      exact this
  -- the lifted rows plus the lifted box are the lift of the sum
  have key := HPolytope.preimage_inter_add_image
    (LinearMap.funLeft ℝ ℝ dims).toAddMonoidHom (Function.ExtendByZero.hom ℝ dims)
    (fun e => funext fun k => hdims.extend_apply _ _ k) P.nominal.construct
    P.I_error.construct {x | ∀ j, (∀ k, dims k ≠ j) → x j = 0}
    (fun x e => ⟨fun h j hj => by simpa [hS e j hj] using h j hj,
      fun h j hj => by simp [hS e j hj, h j hj]⟩)
  ext x
  show x ∈ _ + (P.lift_ dims).I_error.construct ↔ _
  rw [hN, HPolytope.lift_errorBox P hdims]
  refine (Set.ext_iff.mp key x).trans ?_
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
  exact Iff.rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
