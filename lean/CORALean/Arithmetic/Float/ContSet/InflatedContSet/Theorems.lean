import CORALean.Arithmetic.Float.ContSet.InflatedContSet.Proofs

/-!
# What the error box guarantees

Three ways to weaken a nominal part together with its box, by how the operation
moves content: `mono_subset` when nothing moves between the two, `map_subset`
when an additive map pushes both through, `plus_subset` for a binary operation.
A representation discharges its operations through these and never reasons about
set addition itself. Building the box is `Interval`'s business, not this class's.
-/

namespace CORALean.Arithmetic.Float.InflatedContSet

open Pointwise FloatOps SoundFloatArithmetic

variable {F S₁ S₂ T N₁ N₂ N : Type} [FloatOps F] [SoundFloatArithmetic F] {n h : ℕ}

theorem mono_subset {M : Type} [Real.ContSet N₁ n] [Real.ContSet M n]
    [InflatedContSet S₁ N₁ F n] [InflatedContSet T M F n] {s : S₁} {t : T}
    (hnominal : nominalSet s ⊆ nominalSet t)
    (herror : (error s).construct ⊆ (error t).construct) :
    construct s ⊆ construct t :=
  Proofs.mono_subset hnominal herror

theorem map_subset {M T' : Type} {m : ℕ} [Real.ContSet N₁ n] [Real.ContSet M m]
    [InflatedContSet S₁ N₁ F n] [InflatedContSet T' M F m]
    {s : S₁} {t : T'} {f : Vec ℝ n → Vec ℝ m} {D : Set (Vec ℝ m)}
    (hadd : ∀ x y, f (x + y) = f x + f y)
    (hnominal : f '' nominalSet s ⊆ nominalSet t + D)
    (herror : f '' (error s).construct + D ⊆ (error t).construct) :
    f '' construct s ⊆ construct t :=
  Proofs.map_subset hadd hnominal herror

theorem plus_subset [Real.ContSet N₁ n] [Real.ContSet N₂ n] [Real.ContSet N n]
    [InflatedContSet S₁ N₁ F n] [InflatedContSet S₂ N₂ F n] [InflatedContSet T N F n]
    {s₁ : S₁} {s₂ : S₂} {t : T} {D : Set (Vec ℝ n)}
    (hnominal : nominalSet s₁ + nominalSet s₂ ⊆
      nominalSet t + D)
    (herror : (error s₁).construct + (error s₂).construct + D ⊆ (error t).construct) :
    construct s₁ + construct s₂ ⊆ construct t :=
  Proofs.plus_subset hnominal herror

end CORALean.Arithmetic.Float.InflatedContSet
