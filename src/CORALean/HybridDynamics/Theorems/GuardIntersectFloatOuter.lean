module

public import CORALean.ContSet.HPolytope.Float.Instances
public import CORALean.ContSet.HPolytope.Float.Theorems.ContractBoxOuter
public import CORALean.ContSet.Interval.Float.Theorems.OrOuter
public import CORALean.ContSet.Interval.Float.Theorems.RepresentsaEmptySetSound
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.HybridDynamics.Operations.GuardIntersectFloat
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# `Location.guardIntersectFloat` holds every state that meets the guard

A state in one of the time-interval sets, in the invariant and in the guard
lies in that set's cut, which is then not certified empty and so is joined into
the hull — and the hull is `some`. This is the `hinter` that
`Transition.jumpFloat_outer` asks for, computed.

## Inputs
* `ℓ` – location
* `guard` – guard
* `Rs` – reach sets
* `R` – reach set
* `x` – trajectory of the stay

## Hypotheses
* `hR` – the reach set is among the given ones
* `hx` – state lies in the reach set
* `hinv` – the sets are an invariant
* `hguard` – state lies in the guard

## Conclusion
* the float guard intersection is a box holding the state
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float ContSet

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point of the start or of any box folded in is a point of the hull. -/
private theorem aux_mem_foldl_or {x : Vec ℝ n} :
    ∀ (Is : List (Interval (Vec 𝕋 n))) (J : Interval (Vec 𝕋 n)),
      (x ∈ J.construct ∨ ∃ I ∈ Is, x ∈ I.construct) → x ∈ (Is.foldl Interval.or J).construct
  | [], _, h => h.resolve_right (by simp)
  | I :: Is, J, h => by
    rw [List.foldl_cons]
    refine aux_mem_foldl_or Is _ ?_
    rcases h with hJ | ⟨I', hI', hx⟩
    · exact Or.inl (Interval.or_outer J I (Or.inl hJ))
    · rcases List.mem_cons.mp hI' with rfl | hI'
      · exact Or.inl (Interval.or_outer J I' (Or.inr hx))
      · exact Or.inr ⟨I', hI', hx⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Location.guardIntersectFloat_outer
    (ℓ : Location 𝒵[𝕋] (fun k => HPolytope 𝕋 (Vec 𝕋 k)) L 𝕋 n)
    (guard : HPolytope 𝕋 (Vec 𝕋 n)) {Rs : List (Zonotope (Vec 𝕋 n))}
    {R : Zonotope (Vec 𝕋 n)} (hR : R ∈ Rs)
    {x : Vec ℝ n} (hx : x ∈ construct R) (hinv : x ∈ construct ℓ.inv)
    (hguard : x ∈ construct guard) : -- --- CONCL ---
    ∃ Rg, ℓ.guardIntersectFloat guard Rs = some Rg ∧ x ∈ Rg.construct := by -- --- PROOF ---
  -- the cut of `R` holds `x`, so it is not certified empty
  set J := guard.contractBox (ℓ.inv.contractBox R.interval) with hJ
  have hxJ : x ∈ J.construct := guard.contractBox_outer _
    ⟨ℓ.inv.contractBox_outer _ ⟨Zonotope.interval_contains R hx, hinv⟩, hguard⟩
  have hne : J.representsa_emptySet = false := by
    cases hb : J.representsa_emptySet
    · rfl
    · have := Interval.representsa_emptySet_sound hb
      rw [this] at hxJ
      exact absurd hxJ (Set.notMem_empty x)
  have hmem : J ∈ (Rs.map fun R => guard.contractBox (ℓ.inv.contractBox R.interval)).filter
      fun I => !I.representsa_emptySet :=
    List.mem_filter.mpr ⟨List.mem_map.mpr ⟨R, hR, rfl⟩, by simp [hne]⟩
  -- so the filtered list is not empty, and its hull holds `x`
  unfold Location.guardIntersectFloat
  dsimp only
  generalize ((Rs.map fun R => guard.contractBox (ℓ.inv.contractBox R.interval)).filter
    fun I => !I.representsa_emptySet) = l at hmem
  cases l with
  | nil => simp at hmem
  | cons I Is =>
    refine ⟨_, rfl, ?_⟩
    rw [Interval.materialise_eq]
    rcases List.mem_cons.mp hmem with rfl | hIs
    · exact aux_mem_foldl_or Is J (Or.inl hxJ)
    · exact aux_mem_foldl_or Is I (Or.inr ⟨J, hIs, hxJ⟩)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
