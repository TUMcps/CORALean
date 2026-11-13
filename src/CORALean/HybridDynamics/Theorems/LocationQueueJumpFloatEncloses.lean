module

public import CORALean.HybridDynamics.Operations.LocationQueueJumpFloat
public import CORALean.HybridDynamics.Theorems.ZonoGirardMemberFloatMem
public import CORALean.HybridDynamics.Theorems.JumpFloatOuter
public import CORALean.ContSet.HPolytope.Float.Theorems.HyperplaneSound
public import CORALean.ContSet.Interval.Float.Theorems.RepresentsaEmptySetSound
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# `Location.queueJumpFloat` holds the reset of every state of a crossing

A state `z` of a set the group keeps (`Location.queueSetsFloat`) on the guard is in the cut of
the group, so its coordinates in `B` are in the box, which is not certified empty, and `z` is in
the set it maps back to; the reset of `z` is in the jump set (`Transition.jumpFloat_outer`). The
entry is for the target location and starts at `tlo` plus the first set index of the group times
the step.

## Inputs
* `ℓ` – location
* `chk` – whether `checkFlow` is on
* `Bf` – the basis of a crossing, from the guard normal and offset and the sets that meet the guard
* `Δ` – time step
* `idx` – branch number
* `tlo` – lower end of the start time
* `thi` – upper end of the start time
* `Rs` – sets of the stay
* `g` – transition
* `j₀` – first set index of the group
* `js` – the other set indices
* `e` – the transition
* `R` – the set of the state
* `z` – state

## Hypotheses
* `he` – the transition is the `g`-th
* `hkept` – the set is among those `checkFlow` keeps of the group
* `hz` – the set holds the state
* `hguard` – the state is in the guard

## Conclusion
* the entry is a queue entry that holds the reset of the state
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float ContSetLike Matrix SoundFloatArithmetic

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The entry of a crossing holds the reset of every state of its sets on the guard. -/
theorem Location.queueJumpFloat_encloses
    (ℓ : Location 𝒵[𝕋] (fun k => HPolytope 𝕋 (Vec 𝕋 k)) L 𝕋 n) (chk : Bool) (Bf : BasisRule 𝕋 n)
    (Δ : ℚ) (idx : ℕ) (tlo thi : ℚ)
    (Rs : List (Zonotope (Vec 𝕋 n))) {g j₀ : ℕ} {js : List ℕ}
    {e : Transition (fun k => HPolytope 𝕋 (Vec 𝕋 k)) L 𝕋 n} (he : ℓ.trans[g]? = some e)
    {R : Zonotope (Vec 𝕋 n)}
    (hkept : ∀ nv γ, e.guard.hyperplane? = some (nv, γ) →
      R ∈ ℓ.queueSetsFloat chk nv γ (j₀ :: js) Rs)
    {z : Vec ℝ n} (hz : z ∈ toSet R) (hguard : z ∈ toSet e.guard) : -- --- CONCL ---
    ∀ r ∈ ℓ.queueJumpFloat chk Bf Δ idx tlo thi Rs (g, j₀ :: js),
      ∃ c, r = some c ∧ c.loc = e.target ∧ e.reset z ∈ toSet c.set ∧
        c.tlo = tlo + j₀ * Δ := by -- --- PROOF ---
  intro r (h : ℓ.queueJumpFloat chk Bf Δ idx tlo thi Rs (g, j₀ :: js) = some r)
  unfold Location.queueJumpFloat at h
  rw [he] at h
  simp only [Option.pure_def, Option.bind_eq_bind] at h
  obtain ⟨e', he', h⟩ := Option.bind_eq_some_iff.mp h
  cases he'
  obtain ⟨⟨nv, γ⟩, hhp, h⟩ := Option.bind_eq_some_iff.mp h
  -- the sets of the group, the first one being `R₀`
  have hmemfm : R ∈ ℓ.queueSetsFloat chk nv γ (j₀ :: js) Rs := hkept nv γ hhp
  cases hfm : ℓ.queueSetsFloat chk nv γ (j₀ :: js) Rs with
  | nil => rw [hfm] at hmemfm; simp at hmemfm
  | cons R₀ Rr =>
    rw [hfm] at hmemfm h
    dsimp only at h
    have hg : z ⬝ᵥ toRealVec nv = toReal γ :=
      HPolytope.dotProduct_of_hyperplane _ hguard (nv, γ) hhp
    -- the coordinates of the state are in the box, which is therefore not empty
    set B := Bf nv γ (R₀ :: Rr) with hBdef
    have hbox := Location.zonoGirardBoxFloat_mem B R₀ Rr nv γ hmemfm hz hg
    have hne : (Location.zonoGirardBoxFloat B R₀ Rr nv γ).representsa_emptySet = false := by
      cases hb : (Location.zonoGirardBoxFloat B R₀ Rr nv γ).representsa_emptySet
      · rfl
      · rw [Interval.representsa_emptySet_sound hb] at hbox
        exact absurd hbox (Set.notMem_empty _)
    rw [if_neg (by simp [hne])] at h
    cases h
    refine ⟨_, rfl, rfl, ?_, rfl⟩
    -- and the state is in the set the box maps back to
    have hZ := Location.zonoGirardMemberFloat_mem B R₀ Rr nv γ hmemfm hz hg
    exact e.jumpFloat_outer (R := _) Set.inter_subset_left hZ hguard

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
