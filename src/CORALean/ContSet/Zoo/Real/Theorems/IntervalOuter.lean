module

public import CORALean.ContSet.Zoo.Real.Operations.Interval
public import CORALean.ContSet.Taylm.Real.Theorems.BoundsMem
public import CORALean.ContSet.Interval.Real.Operations.IntersectionExact

@[expose] public section

/-!
# `Zoo.interval` encloses the range

The intersection of sound enclosures is sound: whatever interval `Zoo.interval` returns holds
the function's value at every box point. Outer, not exact: each member is only an enclosure, and
the Taylor model's is the interval-arithmetic bound `Taylm.bounds`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zoo.interval_outer {Z : Zoo n} {f : Vec ℝ n → ℝ} (h : Z.Encloses f) {I : Interval (Vec ℝ 1)}
    (hI : Z.interval = some I) {t : Vec ℝ n} (ht : t ∈ Taylm.box n) :
    (fun _ => f t : Vec ℝ 1) ∈ I.construct := by -- --- PROOF ---
  have hT : ∀ T, Z.taylm = some T → (fun _ => f t : Vec ℝ 1) ∈
      (Taylm.interval fun _ : Fin 1 => T).construct := fun T hT i => by
    exact Taylm.bounds_mem (h.1 T hT) ht
  unfold Zoo.interval at hI
  rcases hz : Z.taylm with _ | T <;> rcases hv : Z.ivl with _ | J <;>
    simp [hz, hv] at hI
  · exact hI ▸ h.2 J hv t ht
  · exact hI ▸ hT T hz
  · rw [← hI, Interval.intersection_exact]; exact ⟨hT T hz, h.2 J hv t ht⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
