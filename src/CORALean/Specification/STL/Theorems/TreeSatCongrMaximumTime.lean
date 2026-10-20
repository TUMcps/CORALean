module

public import CORALean.Specification.STL.Theorems.TreeMaximumTimeFromAdd
public import CORALean.Specification.STL.Operations.Basic

@[expose] public section

/-!
# A formula reads the trace only up to maximumTime

`maximumTime(obj)` bounds the part of a trace the satisfaction of `obj` depends on: two traces
that agree on `[0, maximumTime obj]` are satisfying together.

## Inputs
* `φ` – formula
* `ξ` – trace
* `ξ'` – second trace

## Hypotheses
* `h` – the traces agree up to the latest time

## Conclusion
* the formula holds on both or neither
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem STL.Tree.aux_le_add {s t x b : ℝ≥0} (hs : s ≤ x) (ht : t ≤ b) : s + t ≤ b + x := by
  rw [add_comm b x]
  exact add_le_add hs ht


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.sat_congr_maximumTime (φ : STL.Tree n) (ξ ξ' : ℝ≥0 → Fin n → ℝ)
    (h : ∀ s ≤ φ.maximumTime, ξ s = ξ' s) : -- --- CONCL ---
    φ.Sat ξ ↔ φ.Sat ξ' := by -- --- PROOF ---
  induction φ generalizing ξ ξ' with
  | tt | ff => rfl
  | cmp op e₁ e₂ => simp only [STL.Tree.Sat, h 0 (by simp)]
  | not φ ih => exact not_congr (ih ξ ξ' h)
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ =>
    simp only [STL.Tree.Sat, ihφ ξ ξ' fun s hs => h s (hs.trans (le_max_left _ _)),
      ihψ ξ ξ' fun s hs => h s (hs.trans (le_max_right _ _))]
  -- `next` shifts the trace by `a`
  | next a φ ih =>
    have e : (STL.Tree.next a φ).maximumTime = a + φ.maximumTime := by
      show φ.maximumTimeFrom (a + 0) = _
      rw [STL.Tree.maximumTimeFrom_eq_add]; simp [STL.Tree.maximumTime]
    rw [e] at h
    exact ih _ _ fun s hs => h _ (STL.Tree.aux_le_add hs le_rfl)
  -- a window `[a,b]` looks at shifts up to `b`
  | «finally» a b φ ih =>
    have e : (STL.Tree.finally a b φ).maximumTime = b + φ.maximumTime := rfl
    rw [e] at h
    have hφ : ∀ t ≤ b, φ.Sat (Time.shift ξ t) ↔ φ.Sat (Time.shift ξ' t) := fun t ht =>
      ih _ _ fun s hs => h _ (STL.Tree.aux_le_add hs ht)
    simp only [STL.Tree.Sat, STL.Tree.HasUntilWitness]
    exact exists_congr fun t => and_congr_right fun h1 => and_congr_right fun h2 =>
      and_congr (hφ t h2) Iff.rfl
  | globally a b φ ih =>
    have e : (STL.Tree.globally a b φ).maximumTime = b + φ.maximumTime := rfl
    rw [e] at h
    have hφ : ∀ t ≤ b, φ.Sat (Time.shift ξ t) ↔ φ.Sat (Time.shift ξ' t) := fun t ht =>
      ih _ _ fun s hs => h _ (STL.Tree.aux_le_add hs ht)
    simp only [STL.Tree.Sat, STL.Tree.HasUntilWitness]
    exact not_congr (exists_congr fun t => and_congr_right fun h1 => and_congr_right fun h2 =>
      and_congr (not_congr (hφ t h2)) Iff.rfl)
  -- `until` and `release` read both operands at shifts up to `b`
  | «until» a b φ ψ ihφ ihψ =>
    have e : (STL.Tree.until a b φ ψ).maximumTime =
        b + max φ.maximumTime ψ.maximumTime := rfl
    rw [e] at h
    have hφ : ∀ t ≤ b, φ.Sat (Time.shift ξ t) ↔ φ.Sat (Time.shift ξ' t) := fun t ht =>
      ihφ _ _ fun s hs => h _ (STL.Tree.aux_le_add (hs.trans (le_max_left _ _)) ht)
    have hψ : ∀ t ≤ b, ψ.Sat (Time.shift ξ t) ↔ ψ.Sat (Time.shift ξ' t) := fun t ht =>
      ihψ _ _ fun s hs => h _ (STL.Tree.aux_le_add (hs.trans (le_max_right _ _)) ht)
    exact exists_congr fun t => and_congr_right fun h1 => and_congr_right fun h2 =>
      and_congr (hψ t h2) (forall_congr' fun t' => forall_congr' fun h3 => hφ t' (h3.trans h2))
  -- the same for the dual
  | release a b φ ψ ihφ ihψ =>
    have e : (STL.Tree.release a b φ ψ).maximumTime =
        b + max φ.maximumTime ψ.maximumTime := rfl
    rw [e] at h
    have hφ : ∀ t ≤ b, φ.Sat (Time.shift ξ t) ↔ φ.Sat (Time.shift ξ' t) := fun t ht =>
      ihφ _ _ fun s hs => h _ (STL.Tree.aux_le_add (hs.trans (le_max_left _ _)) ht)
    have hψ : ∀ t ≤ b, ψ.Sat (Time.shift ξ t) ↔ ψ.Sat (Time.shift ξ' t) := fun t ht =>
      ihψ _ _ fun s hs => h _ (STL.Tree.aux_le_add (hs.trans (le_max_right _ _)) ht)
    exact not_congr <| exists_congr fun t => and_congr_right fun h1 => and_congr_right fun h2 =>
      and_congr (not_congr (hψ t h2))
        (forall_congr' fun t' => forall_congr' fun h3 => not_congr (hφ t' (h3.trans h2)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
