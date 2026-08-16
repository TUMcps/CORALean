import CORALean.Arithmetic.Float.ContSet.InflatedContSet.Proofs

/-!
# What the error box guarantees

The two ways of paying into it are sound, and composing a nominal part with it
is sound. A representation instantiating the class discharges its operations
through these three and never reasons about set addition itself.
-/

namespace CORALean.Arithmetic.Float.InflatedContSet

open Pointwise FloatOps SoundFloatArithmetic

variable {F S : Type} [FloatOps F] [SoundFloatArithmetic F] {n h : ℕ}

theorem sub_mem_residual {lo hi stored : Vec F n} {x : Vec ℝ n}
    (h : ∀ i, toReal (lo i) ≤ x i ∧ x i ≤ toReal (hi i)) :
    (fun i => x i - toReal (stored i)) ∈ (residual lo hi stored).construct :=
  Proofs.sub_mem_residual h

theorem mem_generatorError {d : Mat F n h} {Δ : Mat ℝ n h} {β : Vec ℝ h}
    (hd : ∀ i j, |Δ i j| ≤ toReal (d i j)) (hβ : ∀ j, |β j| ≤ 1) :
    (fun i => ∑ j, Δ i j * β j) ∈ (generatorError d).construct :=
  Proofs.mem_generatorError hd hβ

theorem plus_subset [InflatedContSet S F n] {s₁ s₂ t : S} {D : Set (Vec ℝ n)}
    (hnominal : nominal s₁ + nominal s₂ ⊆ nominal t + D)
    (herror : (error s₁).construct + (error s₂).construct + D ⊆ (error t).construct) :
    construct s₁ + construct s₂ ⊆ construct t :=
  Proofs.plus_subset hnominal herror

end CORALean.Arithmetic.Float.InflatedContSet
