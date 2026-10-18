module

public import CORALean.ContSet.Capsule.Float.Capsule
public import CORALean.ContSet.Capsule.Float.Operations.RepresentsaPoint
public import CORALean.ContSet.Interval.Float.Operations.Basic
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

/-- Radius `-1`, as over ℝ: `neg one` reads as `-1`, which no point is within; no error box. -/
def Capsule.empty (n : ℕ) : Capsule 𝕋 n :=
  ⟨fun _ => zero, fun _ => zero, neg one, Interval.origin n⟩


-- =====================================  `Capsule.origin`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- No direction, no radius, centered at the origin: `zero` reads as `0`, so nothing rounds. -/
def Capsule.origin (n : ℕ) : Capsule 𝕋 n := ⟨fun _ => zero, fun _ => zero, zero, Interval.origin n⟩

end


section

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ===================================  `Capsule.errorNorm`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A bound on the Euclidean norm of every point of the error box: the norm of the entrywise
larger end magnitude, rounded up. `k` is the number of Newton steps of the root. -/
def Capsule.errorNorm (k : ℕ) (C : Capsule 𝕋 n) : 𝕋 := normUp k C.I_error.normMag


-- =====================================  `Capsule.radius`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---

/-- CORA's `norm(g, 2) + r`, the norm rounded up, plus `errorNorm` for the box; `k` Newton steps. -/
def Capsule.radius (k : ℕ) (C : Capsule 𝕋 n) : 𝕋 :=
  addUp (addUp (normUp k C.g) C.r) (C.errorNorm k)


-- ===============================  `Capsule.representsa_origin`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `@capsule/representsa_.m` at `origin`, tolerance `0`: a point whose center is `0`. -/
def Capsule.representsa_origin (C : Capsule 𝕋 n) : Bool :=
  (List.finRange n).all (fun i => le (C.c i) zero && le zero (C.c i)) && C.representsa_point

end

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
