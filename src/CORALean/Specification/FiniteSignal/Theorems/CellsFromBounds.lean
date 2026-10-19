module

public import CORALean.Specification.FiniteSignal.Operations.CellsFrom
public import Mathlib.Data.List.Pairwise
public import Mathlib.Order.Basic

@[expose] public section

/-!
# The cells are ordered

The cells of strictly increasing breakpoints after `a` are intervals `[lo,hi]` with `a ≤ lo ≤ hi`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem FiniteSignal.cellsFrom_bounds {T V : Type} [LinearOrder T] : -- --- CONCL ---
    ∀ (a : T) (L : List (T × V)), (L.map Prod.fst).Pairwise (· < ·) → (∀ x ∈ L, a ≤ x.1) →
      ∀ c ∈ FiniteSignal.cellsFrom a L, a ≤ c.1.1 ∧ c.1.1 ≤ c.1.2
  | _, [], _, _, c, hc => by simp [FiniteSignal.cellsFrom] at hc
  | a, (b, v) :: rest, hs, ha, c, hc => by
    rw [List.map_cons, List.pairwise_cons] at hs
    simp only [FiniteSignal.cellsFrom, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ⟨le_rfl, ha (b, v) (by simp)⟩
    · have hb : ∀ x ∈ rest, b ≤ x.1 := fun x hx => (hs.1 x.1 (List.mem_map_of_mem hx)).le
      obtain ⟨h1, h2⟩ := FiniteSignal.cellsFrom_bounds b rest hs.2 hb c hc
      exact ⟨(ha (b, v) (by simp)).trans h1, h2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
