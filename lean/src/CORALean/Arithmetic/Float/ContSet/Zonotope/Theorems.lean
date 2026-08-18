import CORALean.Arithmetic.Float.ContSet.Zonotope.Proofs

/-!
# What the floating-point `Zonotope` guarantees

Stated exactly as `Arithmetic.Real` states it, over the same sets of real points
and with the same generator counts.
-/

namespace CORALean.Arithmetic.Float

open Pointwise Matrix SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m h k q r : ℕ}

theorem Zonotope.mem_generatorError {G : Mat 𝕋 n h} {Δ : Mat ℝ n h} {β : Vec ℝ h}
    (hG : ∀ i j, |Δ i j| ≤ SoundFloatArithmetic.toReal (G i j)) (hβ : ∀ j, |β j| ≤ 1) :
    (fun i => ∑ j, Δ i j * β j) ∈ (Zonotope.generatorError G).construct :=
  Zonotope.Proofs.mem_generatorError hG hβ

/-! ### plus -/

omit [SoundFloatArithmetic 𝕋] in
@[simp] theorem Zonotope.plus_h (Z₁ Z₂ : Zonotope 𝕋 n) : (Z₁.plus Z₂).h = Z₁.h + Z₂.h := rfl

theorem Zonotope.plus_outer (Z₁ Z₂ : Zonotope 𝕋 n) :
    Z₁.construct + Z₂.construct ⊆ (Z₁.plus Z₂).construct :=
  Zonotope.Proofs.plus_outer Z₁ Z₂

/-! ### mtimes -/

omit [SoundFloatArithmetic 𝕋] in
@[simp] theorem Zonotope.mtimes_h (M : Mat 𝕋 m n) (Z : Zonotope 𝕋 n) :
    (Zonotope.mtimes M Z).h = Z.h := rfl

theorem Zonotope.mtimes_outer (M : Mat 𝕋 m n) (Z : Zonotope 𝕋 n) :
    ((toRealMat M) *ᵥ ·) '' Z.construct ⊆ (Zonotope.mtimes M Z).construct :=
  Zonotope.Proofs.mtimes_outer M Z

/-! ### interval -/

theorem Zonotope.interval_outer (Z : Zonotope 𝕋 n) :
    Z.construct ⊆ Z.interval.construct :=
  Zonotope.Proofs.interval_outer Z

/-! ### reduce -/

omit [SoundFloatArithmetic 𝕋] in
@[simp] theorem Zonotope.reduce_h (Z : Zonotope 𝕋 n)
    (part : Split (Fin Z.h) into (Fin q) and (Fin r)) : (Z.reduce part).h = q + n := rfl

theorem Zonotope.reduce_outer (Z : Zonotope 𝕋 n)
    (part : Split (Fin Z.h) into (Fin q) and (Fin r)) :
    Z.construct ⊆ (Z.reduce part).construct :=
  Zonotope.Proofs.reduce_outer Z part

/-! ### reduceOrder -/

theorem Zonotope.reduceOrder_outer (o : ℕ) (Z : Zonotope 𝕋 n) :
    Z.construct ⊆ (Z.reduceOrder o).construct :=
  Zonotope.Proofs.reduceOrder_outer o Z

/-! ### reduceAndAbsorb -/

omit [SoundFloatArithmetic 𝕋] in
@[simp] theorem Zonotope.reduceAndAbsorb_h (Z : Zonotope 𝕋 n)
    (part : Split (Fin Z.h) into (Fin q) and (Fin r)) :
    (Z.reduceAndAbsorb part).h = q + n := rfl

theorem Zonotope.reduceAndAbsorb_outer (Z : Zonotope 𝕋 n)
    (part : Split (Fin Z.h) into (Fin q) and (Fin r)) :
    Z.construct ⊆ (Z.reduceAndAbsorb part).construct :=
  Zonotope.Proofs.reduceAndAbsorb_outer Z part

/-! ### absorbError -/

omit [SoundFloatArithmetic 𝕋] in
@[simp] theorem Zonotope.absorbError_h (Z : Zonotope 𝕋 n) :
    Z.absorbError.h = Z.h + n := rfl

theorem Zonotope.absorbError_outer (Z : Zonotope 𝕋 n) :
    Z.construct ⊆ Z.absorbError.construct :=
  Zonotope.Proofs.absorbError_outer Z

end CORALean.Arithmetic.Float
