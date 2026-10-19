module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Setting a list of sets in turn

Folding a step over a list, where each step is valid and sets one set of times `S x` to `v` and
keeps the value elsewhere, gives a valid signal that has `v` on the union of the sets and the old
value elsewhere. `toBoolSignal`, `toKleeneSignal`, `merge` and `until` set the intervals they find
in turn; the signal type is any `σ` with a validity predicate and a value at each time.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- A fold of steps that each set a set of times sets the union. -/
theorem List.foldl_set_spec {α σ β : Type} (valid : σ → Prop) (val : σ → ℝ → β) (l : List α)
    (S : α → Set ℝ) (v : β) (step : σ → α → σ)
    (hstep : ∀ sig x, x ∈ l → valid sig → valid (step sig x) ∧ ∀ t : ℝ, 0 ≤ t →
      (t ∈ S x → val (step sig x) t = v) ∧ (t ∉ S x → val (step sig x) t = val sig t))
    (s : σ) (hs : valid s) : -- --- CONCL ---
    valid (l.foldl step s) ∧ ∀ t : ℝ, 0 ≤ t →
      ((∃ x ∈ l, t ∈ S x) → val (l.foldl step s) t = v) ∧
      ((¬ ∃ x ∈ l, t ∈ S x) → val (l.foldl step s) t = val s t) := by -- --- PROOF ---
  induction l generalizing s with
  | nil => exact ⟨hs, fun t _ => ⟨fun ⟨x, hx, _⟩ => absurd hx (by simp), fun _ => rfl⟩⟩
  | cons x l ih =>
    -- the first step, then the fold over the rest
    obtain ⟨h1, h2⟩ := hstep s x List.mem_cons_self hs
    obtain ⟨h3, h4⟩ := ih (fun sig y hy => hstep sig y (List.mem_cons_of_mem _ hy)) _ h1
    refine ⟨h3, fun t ht => ⟨fun ⟨y, hy, hty⟩ => ?_, fun hn => ?_⟩⟩
    · rw [List.foldl_cons]
      by_cases hl : ∃ z ∈ l, t ∈ S z
      · exact (h4 t ht).1 hl
      · -- only the first step sets `t`
        rw [(h4 t ht).2 hl]
        rcases List.mem_cons.1 hy with rfl | hy'
        · exact (h2 t ht).1 hty
        · exact absurd ⟨y, hy', hty⟩ hl
    · rw [List.foldl_cons, (h4 t ht).2 (fun ⟨z, hz, htz⟩ => hn ⟨z, List.mem_cons_of_mem _ hz, htz⟩),
        (h2 t ht).2 (fun h => hn ⟨x, List.mem_cons_self, h⟩)]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
