import CORALean.Arithmetic.Float.ContSet.Zonotope.Proofs

/-!
# What the floating-point `Zonotope` guarantees

Stated exactly as `Arithmetic.Real` states it, over the same sets of real points
and with the same generator counts.
-/

namespace CORALean.Arithmetic.Float

open Pointwise Matrix SoundFloatArithmetic

variable {F : Type} [FloatOps F] [SoundFloatArithmetic F] {n m h k q r : ℕ}

theorem Zonotope.mem_generatorError {G : Mat F n h} {Δ : Mat ℝ n h} {β : Vec ℝ h}
    (hG : ∀ i j, |Δ i j| ≤ SoundFloatArithmetic.toReal (G i j)) (hβ : ∀ j, |β j| ≤ 1) :
    (fun i => ∑ j, Δ i j * β j) ∈ (Zonotope.generatorError G).construct :=
  Zonotope.Proofs.mem_generatorError hG hβ

theorem Zonotope.plus_outer (Z₁ : Zonotope F n h) (Z₂ : Zonotope F n k) :
    Z₁.construct + Z₂.construct ⊆ (Z₁.plus Z₂).construct :=
  Zonotope.Proofs.plus_outer Z₁ Z₂

theorem Zonotope.mtimes_outer (M : Mat F m n) (Z : Zonotope F n h) :
    ((toRealMat M) *ᵥ ·) '' Z.construct ⊆ (Zonotope.mtimes M Z).construct :=
  Zonotope.Proofs.mtimes_outer M Z

theorem Zonotope.interval_outer (Z : Zonotope F n h) :
    Z.construct ⊆ Z.interval.construct :=
  Zonotope.Proofs.interval_outer Z

theorem Zonotope.reduce_outer (Z : Zonotope F n h)
    (part : Split (Fin h) into (Fin q) and (Fin r)) :
    Z.construct ⊆ (Z.reduce part).construct :=
  Zonotope.Proofs.reduce_outer Z part

theorem Zonotope.reduceAndAbsorb_outer (Z : Zonotope F n h)
    (part : Split (Fin h) into (Fin q) and (Fin r)) :
    Z.construct ⊆ (Z.reduceAndAbsorb part).construct :=
  Zonotope.Proofs.reduceAndAbsorb_outer Z part

theorem Zonotope.absorbError_outer (Z : Zonotope F n h) :
    Z.construct ⊆ Z.absorbError.construct :=
  Zonotope.Proofs.absorbError_outer Z

end CORALean.Arithmetic.Float
