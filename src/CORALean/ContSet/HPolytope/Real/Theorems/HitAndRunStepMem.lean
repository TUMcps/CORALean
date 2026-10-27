module

public import CORALean.ContSet.HPolytope.Real.Operations.HitAndRunStep
public import CORALean.ContSet.HPolytope.Real.Theorems.MemAddSmulIffChord

@[expose] public section

/-!
# Hit-and-Run never leaves the polytope

`[1, Sec. 3, Mixing Algorithm]` generates "points all within the region `S`": from an interior
point, any direction `d` and any `u ∈ [0, 1]`, the point `HPolytope.hitAndRunStep` returns
satisfies every inequality. The point lies on the chord, which `MemAddSmulIffChord` identifies
with `{t | x + t d ∈ S}`.

## Inputs
* `P` – H-polytope
* `x` – point
* `d` – direction
* `u` – real number

## Hypotheses
* `hx` – `x` is strictly inside every inequality
* `hu₀` – `0 ≤ u`
* `hu₁` – `u ≤ 1`

## Conclusion
* hit-and-Run never leaves the polytope

## References

* [1] [R. L. Smith. "Efficient Monte Carlo Procedures for Generating Points Uniformly Distributed
      Over Bounded Regions". Operations Research,
      1984.](../../../../../../references/1984/smith-or-uniform-points.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.hitAndRunStep_mem (P : HPolytope α) (x d : α) (u : ℝ) (hx : ∀ i, P.A i x < P.b i)
    (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1) : -- --- CONCL ---
    ∀ y ∈ P.hitAndRunStep x d u,
      ∀ i, P.A i y ≤ P.b i := by -- --- PROOF ---
  intro y (hy : P.hitAndRunStep x d u = some y)
  -- the two ends of the chord
  obtain ⟨tLow, hlo, tHigh, hhi, rfl⟩ : ∃ tLow, P.chordLow x d = some tLow ∧
      ∃ tHigh, P.chordHigh x d = some tHigh ∧ y = x + (tLow + u * (tHigh - tLow)) • d := by
    unfold HPolytope.hitAndRunStep at hy
    obtain ⟨a, ha, hb⟩ := Option.bind_eq_some_iff.mp hy
    obtain ⟨b, hb', rfl⟩ := Option.map_eq_some_iff.mp hb
    exact ⟨a, ha, b, hb', rfl⟩
  -- `t = 0` is on the chord, so `t̲ ≤ 0 ≤ t̄`
  have h0 := (HPolytope.mem_add_smul_iff_chord P x d hx 0).mp (fun i => by simpa using (hx i).le)
  have hl : tLow ≤ 0 := h0.1 tLow hlo
  have hh : 0 ≤ tHigh := h0.2 tHigh hhi
  -- the draw is between them
  refine (HPolytope.mem_add_smul_iff_chord P x d hx _).mpr ⟨fun s hs => ?_, fun s hs => ?_⟩
  · rw [hlo] at hs; cases hs
    nlinarith [mul_nonneg hu₀ (sub_nonneg.mpr (hl.trans hh))]
  · rw [hhi] at hs; cases hs
    nlinarith [mul_nonneg (sub_nonneg.mpr hu₁) (sub_nonneg.mpr (hl.trans hh))]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
