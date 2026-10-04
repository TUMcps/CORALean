import CORALean.ContSet.Ellipsoid.Real.Operations.Enclose
import CORALean.ContSet.Ellipsoid.Real.Operations.OfPoint
import CORALean.ContSet.ContSet.ContSet

/-!
# CORA's `ellipsoid/enclose` misses the set its header documents

The header of `@ellipsoid/enclose.m` documents `{a x₁ + (1 - a) x₂ | x₁ ∈ E, x₂ ∈ E2, a ∈ [0,1]}`
with `E2 = M*E + Eplus`, but the code sets `E2 = M*Eplus` and adds nothing. For `E = {0}`, `M = 0`
and `Eplus = {1}` the documented set contains `1` (at `a = 0`: `x₂ = M 0 + 1`), while the segments
between `E` and the `E2` the code hands to `convHull` are `{0}`. What `convHull` returns is an
enclosure of those segments, so nothing in the code makes it reach the documented set. Read from
the source, not run.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise


-- =======================================  MAIN THEOREM  ======================================= --

/-- The documented set `segments E (M E + Eplus)` is not inside the segments between `E` and the
`E2 = M Eplus` the code uses. -/
theorem Ellipsoid.enclose_cora_counterexample :
    ∃ (E Eplus : Ellipsoid 1) (M : Mat ℝ 1 1),
      ¬ segments E.construct ((M *ᵥ ·) '' E.construct + Eplus.construct) ⊆
        segments E.construct ((Ellipsoid.mtimes M Eplus).construct) := by -- --- PROOF ---
  refine ⟨Ellipsoid.ofPoint 0, Ellipsoid.ofPoint (fun _ => 1), 0, fun h => ?_⟩
  -- a point ellipsoid is the singleton of its centre
  have hpt : ∀ v : Vec ℝ 1, (Ellipsoid.ofPoint v).construct = {v} := by
    intro v
    ext x
    constructor
    · rintro ⟨u, -, rfl⟩
      simp [Ellipsoid.ofPoint]
    · rintro rfl
      exact ⟨0, by simp [CORALean.norm₂], by simp [Ellipsoid.ofPoint]⟩
  -- the documented set contains `1`, at `a = 0`
  have hm : (fun _ => (1 : ℝ) : Vec ℝ 1) ∈ segments (Ellipsoid.ofPoint (0 : Vec ℝ 1)).construct
      ((fun y => (0 : Mat ℝ 1 1) *ᵥ y) '' (Ellipsoid.ofPoint (0 : Vec ℝ 1)).construct +
        (Ellipsoid.ofPoint (fun _ => (1 : ℝ) : Vec ℝ 1)).construct) := by
    refine ⟨0, by rw [hpt]; rfl, fun _ => 1, ?_, 0, by simp, by simp⟩
    rw [hpt, hpt]
    exact ⟨0, ⟨0, rfl, by simp⟩, fun _ => 1, rfl, by simp⟩
  -- the segments of the code's arguments are `{0}`
  obtain ⟨y₁, h₁, y₂, h₂, l, -, ht⟩ := h hm
  rw [hpt] at h₁
  have h₂' : y₂ = 0 := by
    obtain ⟨u, -, rfl⟩ := h₂
    simp [Ellipsoid.mtimes, Ellipsoid.ofPoint]
  rw [Set.mem_singleton_iff] at h₁
  subst h₁ h₂'
  have := congrFun ht 0
  simp at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
