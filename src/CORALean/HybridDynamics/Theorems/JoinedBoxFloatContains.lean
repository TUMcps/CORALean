module

public import CORALean.HybridDynamics.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Interval.Float.Theorems.OrOuter

@[expose] public section

/-!
# `Location.joinedBoxFloat` holds the states of every set

The joined box of the zonotopes `R₀ :: Rs` holds each state of each of them.

## Inputs
* `R₀` – initial zonotope
* `Rs` – reach sets
* `R` – reach set
* `x` – state

## Hypotheses
* `hR` – the reach set is among the given ones
* `hx` – state lies in the reach set

## Conclusion
* state lies in the joined box
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The joined box of the zonotopes `R₀ :: Rs` holds the states of each of them. -/
theorem Location.joinedBoxFloat_contains (R₀ : Zonotope (Vec 𝕋 n))
    (Rs : List (Zonotope (Vec 𝕋 n))) {R : Zonotope (Vec 𝕋 n)} (hR : R ∈ R₀ :: Rs)
    {x : Vec ℝ n} (hx : x ∈ R.toSet) : -- --- CONCL ---
    x ∈ (Location.joinedBoxFloat R₀ Rs).toSet := by -- --- PROOF ---
  have hfold : ∀ (Is : List (Interval (Vec 𝕋 n))) (J : Interval (Vec 𝕋 n)) (y : Vec ℝ n),
      (y ∈ J.toSet ∨ ∃ I ∈ Is, y ∈ I.toSet) → y ∈ (Is.foldl Interval.or J).toSet := by
    intro Is
    induction Is with
    | nil => exact fun J y h => h.resolve_right (by simp)
    | cons I Is ih =>
      intro J y h
      rw [List.foldl_cons]
      refine ih _ y ?_
      rcases h with hJ | ⟨I', hI', hy⟩
      · exact Or.inl (Interval.or_outer J I (Or.inl hJ))
      · rcases List.mem_cons.mp hI' with rfl | hI'
        · exact Or.inl (Interval.or_outer J I' (Or.inr hy))
        · exact Or.inr ⟨I', hI', hy⟩
  refine hfold _ _ x ?_
  rcases List.mem_cons.mp hR with rfl | hR'
  · exact Or.inl (Zonotope.interval_contains _ hx)
  · exact Or.inr ⟨_, List.mem_map.mpr ⟨R, hR', rfl⟩, Zonotope.interval_contains _ hx⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
