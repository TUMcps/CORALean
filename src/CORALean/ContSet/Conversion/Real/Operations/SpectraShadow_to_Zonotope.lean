module

public import CORALean.ContSet.Conversion.Real.SpectraShadow_to_Interval
public import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope

@[expose] public section

/-!
# A spectrahedral shadow as a zonotope — the construction

`SpectraShadow.base` and `SpectraShadow.zonotope` are the constructions; `SpectraShadow_to_Zonotope`
states and proves what they guarantee.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `spectraShadow(SpS.A)`: the base spectrahedron, in the space of the variables `β`. -/
def SpectraShadow.base (S : SpectraShadow α) : SpectraShadow (Vec ℝ S.m) :=
  ⟨S.k, S.m, S.A₀, S.A, 0, fun i => Pi.single i (1 : ℝ)⟩

/-- `G Z + c`, `Z` the box of the base spectrahedron as a zonotope. -/
noncomputable def SpectraShadow.zonotope (S : SpectraShadow α) : Zonotope α where
  h := S.m
  c := S.c + ∑ i, ((S.base.interval.inf i + S.base.interval.sup i) / 2) • S.G i
  G := fun j => ((S.base.interval.sup j - S.base.interval.inf j) / 2) • S.G j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
