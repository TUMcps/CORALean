module

public import CORALean.HybridDynamics.Operations.TransitionSynchronizeGuard
public import CORALean.ContSet.HPolytope.Float.Theorems.IntersectionOuter

@[expose] public section

/-!
# `Transition.synchronizeGuard` contains the intersection

The synchronized guard contains the intersection of the guards: stacking the rows loses nothing,
and folding each error box into its rows (`HPolytope.intersection`) only enlarges.

## Inputs
* `g` – guards of the components

## Hypotheses
* none

## Conclusion
* the synchronized guard contains the intersection of the guards
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q k : ℕ} {L : Fin k → Type}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The accumulator of the guard fold contains the intersection so far. -/
theorem aux_synchronizeGuard_fold (g : Fin q → HPolytope 𝕋 (Vec 𝕋 n)) (l : List (Fin q))
    (P : HPolytope 𝕋 (Vec 𝕋 n)) : -- --- CONCL ---
    P.construct ∩ ⋂ i ∈ l, (g i).construct ⊆
      (l.foldl (fun guard i => HPolytope.intersection guard (g i))
        P).construct := by -- --- PROOF ---
  induction l generalizing P with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons]
    intro x hx
    refine ih _ ⟨HPolytope.intersection_outer P (g a) ⟨hx.1, ?_⟩, ?_⟩
    · exact Set.mem_iInter₂.mp hx.2 a List.mem_cons_self
    · exact Set.mem_iInter₂.mpr fun i hi =>
        Set.mem_iInter₂.mp hx.2 i (List.mem_cons_of_mem _ hi)


-- =======================================  MAIN THEOREM  ======================================= --

/-- The synchronized guard contains the intersection of the guards. -/
theorem Transition.synchronizeGuard_outer (g : Fin q → HPolytope 𝕋 (Vec 𝕋 n)) : -- --- CONCL ---
    ⋂ i, (g i).construct ⊆ (Transition.synchronizeGuard g).construct := by -- --- PROOF ---
  unfold Transition.synchronizeGuard
  intro x hx
  refine aux_synchronizeGuard_fold g _ _ ⟨HPolytope.mem_fullspace x, ?_⟩
  simp only [Set.mem_iInter] at hx ⊢
  exact fun i _ => hx i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
