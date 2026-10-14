module

public import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
public import CORALean.ContSet.Zonotope.Float.Operations.Basic

@[expose] public section

/-!
# `ContSet/ZonoBundle/Float/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- ====================================  `ZonoBundle.empty`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- The bundle of the points `0` and `e₀`, for `0 < n`, as over ℝ: two point zonotopes
whose intersection is empty. The second centre is `one` in the first coordinate
and `zero` elsewhere. -/
def ZonoBundle.empty (n : ℕ) (hn : 0 < n) : ZonoBundle (Vec 𝕋 n) :=
  ⟨2, ![Zonotope.origin n, Zonotope.point fun i => if i = ⟨0, hn⟩ then one else zero]⟩

end CORALean.Float


-- ===================================  `ZonoBundle.origin`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- A bundle of the one zonotope `Zonotope.origin`, as in CORA. -/
def ZonoBundle.origin (n : ℕ) : ZonoBundle (Vec 𝕋 n) := ⟨1, fun _ => Zonotope.origin n⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
