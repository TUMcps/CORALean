module

public import CORALean.ContSet.Capsule.Float.Capsule
public import CORALean.ContSet.Capsule.Float.Operations.RepresentsaPoint
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# `ContSet/Capsule/Float/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Float

section

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  `Capsule.center`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA returns the field `c`; so does this. -/
def Capsule.center (C : Capsule 𝕋 n) : Vec 𝕋 n := C.c


-- =====================================  `Capsule.empty`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Radius `-1`, as over ℝ: `neg one` reads as `-1`, which no point is within. -/
def Capsule.empty (n : ℕ) : Capsule 𝕋 n := ⟨fun _ => zero, fun _ => zero, neg one⟩


-- =====================================  `Capsule.origin`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- No direction, no radius, centred at the origin: `zero` reads as `0`, so nothing rounds. -/
def Capsule.origin (n : ℕ) : Capsule 𝕋 n := ⟨fun _ => zero, fun _ => zero, zero⟩

end


section

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  `Capsule.radius`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `norm(g, 2) + r` with the norm rounded up: `normUp` of the generator, added to the radius
upward. `k` is the number of Newton steps of the root (`Global/Float/Sqrt`). -/
def Capsule.radius (k : ℕ) (C : Capsule 𝕋 n) : 𝕋 :=
  let length := normUp k C.g
  addUp length C.r


-- ===============================  `Capsule.representsa_origin`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `@capsule/representsa_.m` at `origin`, tolerance `0`: a point whose centre is `0`. -/
def Capsule.representsa_origin (C : Capsule 𝕋 n) : Bool :=
  (List.finRange n).all (fun i => le (C.c i) zero && le zero (C.c i)) && C.representsa_point

end

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
