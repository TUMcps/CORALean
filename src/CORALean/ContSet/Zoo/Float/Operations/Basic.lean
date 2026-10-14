module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Times
public import CORALean.ContSet.Taylm.Float.Operations.Basic
public import CORALean.ContSet.Taylm.Float.Operations.Rdivide
public import CORALean.ContSet.Taylm.Float.Operations.Times
public import CORALean.ContSet.Zoo.Float.Zoo

@[expose] public section

/-!
# `ContSet/Zoo/Float/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ======================================  `Zoo.interval`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The intersection of the members' interval enclosures: the Taylor model's range bound `bounds`
(`Taylm.interval` at one component) meets the stored interval; a missing member leaves the other. -/
def Zoo.interval (Z : Zoo 𝕋 n) : Option (Interval (Vec 𝕋 1)) :=
  Option.merge Interval.intersection
    (Z.taylm.map fun T => ⟨fun _ => T.bounds.1, fun _ => T.bounds.2⟩) Z.ivl


-- =======================================  `Zoo.minus`  ======================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- As `plus`, with `Taylm.minus` and `Interval.minus`. -/
def Zoo.minus (Z₁ Z₂ : Zoo 𝕋 n) : Zoo 𝕋 n :=
  ⟨Option.map₂ Taylm.minus Z₁.taylm Z₂.taylm, Option.map₂ Interval.minus Z₁.ivl Z₂.ivl⟩


-- ======================================  `Zoo.rdivide`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- As `plus`, with `Taylm.rdivide` and `Interval.rdivide`. -/
def Zoo.rdivide (Z₁ Z₂ : Zoo 𝕋 n) : Zoo 𝕋 n :=
  ⟨Option.map₂ Taylm.rdivide Z₁.taylm Z₂.taylm, Option.map₂ Interval.rdivide Z₁.ivl Z₂.ivl⟩


-- =======================================  `Zoo.times`  ======================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- As `plus`, with `Taylm.times` and `Interval.times`. -/
def Zoo.times (Z₁ Z₂ : Zoo 𝕋 n) : Zoo 𝕋 n :=
  ⟨Option.map₂ Taylm.times Z₁.taylm Z₂.taylm, Option.map₂ Interval.times Z₁.ivl Z₂.ivl⟩


-- =======================================  `Zoo.uminus`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Every member negated: `Taylm.uminus` and `Interval.uminus`, both exact in floats. -/
def Zoo.uminus (Z : Zoo 𝕋 n) : Zoo 𝕋 n := ⟨Z.taylm.map Taylm.uminus, Z.ivl.map Interval.uminus⟩


-- =======================================  `Zoo.uplus`  ======================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The zoo itself. -/
def Zoo.uplus (Z : Zoo 𝕋 n) : Zoo 𝕋 n := Z

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
