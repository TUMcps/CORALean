module

public import CORALean.Specification.STL.Theorems.TreeMinimumTimeFromAdd
public import CORALean.Specification.STL.Operations.Basic

@[expose] public section

/-!
# A formula reads the trace only from minimumTime on

`minimumTime(obj)` bounds from below the part of a trace the satisfaction of `obj` depends on: two
traces that agree from `minimumTime obj` on are satisfying together. The bound is the one CORA
computes, which for a `finally` or `globally` is its lower bound without the offset of the inner
formula, so it is a lower bound that need not be attained.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.sat_congr_minimumTime (φ : STL.Tree n) (ξ ξ' : ℝ≥0 → Fin n → ℝ)
    (h : ∀ s, φ.minimumTime ≤ s → ξ s = ξ' s) : φ.Sat ξ ↔ φ.Sat ξ' := by -- --- PROOF ---
  induction φ generalizing ξ ξ' with
  | tt | ff => rfl
  | cmp op e₁ e₂ => simp only [STL.Tree.Sat, h 0 le_rfl]
  | not φ ih => exact not_congr (ih ξ ξ' h)
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ =>
    simp only [STL.Tree.Sat, ihφ ξ ξ' fun s hs => h s ((min_le_left _ _).trans hs),
      ihψ ξ ξ' fun s hs => h s ((min_le_right _ _).trans hs)]
  -- `next` shifts the trace by `a`
  | next a φ ih =>
    have e : (STL.Tree.next a φ).minimumTime = a + φ.minimumTime := by
      show φ.minimumTimeFrom (a + 0) = _
      rw [STL.Tree.minimumTimeFrom_eq_add]; simp [STL.Tree.minimumTime]
    rw [e] at h
    exact ih _ _ fun s hs => h _ (by rw [add_comm s a]; exact add_le_add_right hs a)
  -- a window `[a,b]` looks at shifts from `a` on
  | «finally» a b φ ih =>
    have e : (STL.Tree.finally a b φ).minimumTime = a := by simp [STL.Tree.minimumTime,
      STL.Tree.minimumTimeFrom]
    rw [e] at h
    have hφ : ∀ t, a ≤ t → (φ.Sat (Time.shift ξ t) ↔ φ.Sat (Time.shift ξ' t)) :=
      fun t (ht : a ≤ t) =>
      ih (Time.shift ξ t) (Time.shift ξ' t) fun s hs =>
        h (s + t) (ht.trans le_add_self)
    exact exists_congr fun t => and_congr_right fun h1 => and_congr_right fun h2 => hφ t h1
  -- the same for `globally`
  | globally a b φ ih =>
    have e : (STL.Tree.globally a b φ).minimumTime = a := by simp [STL.Tree.minimumTime,
      STL.Tree.minimumTimeFrom]
    rw [e] at h
    have hφ : ∀ t, a ≤ t → (φ.Sat (Time.shift ξ t) ↔ φ.Sat (Time.shift ξ' t)) :=
      fun t (ht : a ≤ t) =>
      ih (Time.shift ξ t) (Time.shift ξ' t) fun s hs =>
        h (s + t) (ht.trans le_add_self)
    exact forall_congr' fun t => forall_congr' fun h1 => forall_congr' fun h2 => hφ t h1
  -- `until` and `release` start at the present: every shift is read
  | «until» a b φ ψ ihφ ihψ | release a b φ ψ ihφ ihψ =>
    have hφ : ∀ t, φ.Sat (Time.shift ξ t) ↔ φ.Sat (Time.shift ξ' t) := fun t =>
      ihφ (Time.shift ξ t) (Time.shift ξ' t) fun s hs => h (s + t) zero_le
    have hψ : ∀ t, ψ.Sat (Time.shift ξ t) ↔ ψ.Sat (Time.shift ξ' t) := fun t =>
      ihψ (Time.shift ξ t) (Time.shift ξ' t) fun s hs => h (s + t) zero_le
    simp only [STL.Tree.Sat, hφ, hψ]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
