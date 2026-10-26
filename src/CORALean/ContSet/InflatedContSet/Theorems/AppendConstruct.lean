module

public import CORALean.ContSet.InflatedContSet.Interfaces
public import CORALean.ContSet.Interval.Float.Theorems.AppendConstruct
public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

@[expose] public section

/-!
# A product of inflated sets

If the nominal part of a stored set is the pair of two others' nominal parts read through
`Fin.append`, and its error box is the two boxes side by side (`Interval.append`), then the set
itself is the pair of their sets read through `Fin.append`. Set addition is coordinatewise, so a
product of sums is a sum of products. Every Cartesian product of float representations discharges
its exactness through this.

## Inputs
* `s₁` – first inflated set
* `s₂` – second inflated set
* `t` – inflated set

## Hypotheses
* `hnominal` – `t` has the product of the nominal parts
* `herror` – `t` has the appended error boxes

## Conclusion
* `t` denotes the product of `s₁` and `s₂`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.InflatedContSet

open Pointwise

variable {𝕋 S₁ S₂ T N₁ N₂ N : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n₁ n₂ : ℕ}
variable [ContSet N₁ (Vec ℝ n₁)] [ContSet N₂ (Vec ℝ n₂)] [ContSet N (Vec ℝ (n₁ + n₂))]
variable [InflatedContSet S₁ N₁ (Vec 𝕋 n₁) (Vec ℝ n₁)] [InflatedContSet S₂ N₂ (Vec 𝕋 n₂) (Vec ℝ n₂)]
  [InflatedContSet T N (Vec 𝕋 (n₁ + n₂)) (Vec ℝ (n₁ + n₂))]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {n₁ n₂ : ℕ}

/-- Appending sums coordinatewise. -/
private theorem _root_.CORALean.aux_append_image_prod_add (A₁ B₁ : Set (Vec ℝ n₁))
    (A₂ B₂ : Set (Vec ℝ n₂)) : -- --- CONCL ---
    (fun p : Vec ℝ n₁ × Vec ℝ n₂ => Fin.append p.1 p.2) '' (A₁ ×ˢ A₂) +
        (fun p : Vec ℝ n₁ × Vec ℝ n₂ => Fin.append p.1 p.2) '' (B₁ ×ˢ B₂) =
      (fun p : Vec ℝ n₁ × Vec ℝ n₂ => Fin.append p.1 p.2) ''
        ((A₁ + B₁) ×ˢ (A₂ + B₂)) := by -- --- PROOF ---
  ext z
  constructor
  · rintro ⟨_, ⟨⟨a₁, a₂⟩, ⟨ha₁, ha₂⟩, rfl⟩, _, ⟨⟨b₁, b₂⟩, ⟨hb₁, hb₂⟩, rfl⟩, rfl⟩
    refine ⟨(a₁ + b₁, a₂ + b₂), ⟨⟨a₁, ha₁, b₁, hb₁, rfl⟩, ⟨a₂, ha₂, b₂, hb₂, rfl⟩⟩, ?_⟩
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
  · rintro ⟨⟨_, _⟩, ⟨⟨a₁, ha₁, b₁, hb₁, rfl⟩, ⟨a₂, ha₂, b₂, hb₂, rfl⟩⟩, rfl⟩
    refine ⟨Fin.append a₁ a₂, ⟨(a₁, a₂), ⟨ha₁, ha₂⟩, rfl⟩, Fin.append b₁ b₂,
      ⟨(b₁, b₂), ⟨hb₁, hb₂⟩, rfl⟩, ?_⟩
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

end


-- =======================================  MAIN THEOREM  ======================================= --

theorem append_construct {s₁ : S₁} {s₂ : S₂} {t : T}
    (hnominal : nominalSet t = (fun p : Vec ℝ n₁ × Vec ℝ n₂ => Fin.append p.1 p.2) ''
      (nominalSet s₁ ×ˢ nominalSet s₂))
    (herror : I_error t = Interval.append (I_error s₁) (I_error s₂)) : -- --- CONCL ---
    construct t = (fun p : Vec ℝ n₁ × Vec ℝ n₂ => Fin.append p.1 p.2) ''
      (construct s₁ ×ˢ construct s₂) := by -- --- PROOF ---
  show nominalSet t + (I_error t).construct = _ '' ((nominalSet s₁ + (I_error s₁).construct) ×ˢ
    (nominalSet s₂ + (I_error s₂).construct))
  rw [hnominal, herror, Interval.append_construct, aux_append_image_prod_add]

end CORALean.Float.InflatedContSet


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
