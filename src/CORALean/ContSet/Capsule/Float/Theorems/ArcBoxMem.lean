module

public import CORALean.ContSet.Capsule.Float.Operations.ArcBox
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.CosOuter
public import CORALean.ContSet.Interval.Float.Theorems.SinOuter

@[expose] public section

/-!
# `Capsule.arcBox` holds the sampled point

For a center in its box, a base angle in its box and a real step within the stored step bounds,
the exact sample `ctr + r (cos a, sin a)` at `a = a₀ + i * step` lies in the box: each interval
operation encloses its exact counterpart (`plus_outer`, `times_outer`, `cos_outer`, `sin_outer`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.arcBox_mem (p : ℕ) (step : Interval 𝕋) {s : ℝ}
    (hs : toReal step.inf ≤ s ∧ s ≤ toReal step.sup) (ctr : Interval (Vec 𝕋 2))
    (a₀ : Interval (Vec 𝕋 1)) (r : 𝕋) (i : ℕ) {c : Vec ℝ 2} (hc : c ∈ ctr.construct) {a : ℝ}
    (ha : (fun _ => a : Vec ℝ 1) ∈ a₀.construct) : -- --- STMT ---
    (![c 0 + toReal r * Real.cos (a + (i : ℝ) * s), c 1 + toReal r * Real.sin (a + (i : ℝ) * s)] :
      Vec ℝ 2) ∈ (Capsule.arcBox p step ctr a₀ r i).construct := by -- --- PROOF ---
  -- the index and the step in their boxes
  have hi := intDown_le_intUp (𝕋 := 𝕋) (i : ℤ)
  have hidx : (fun _ => (i : ℝ) : Vec ℝ 1) ∈
      (⟨fun _ => intDown (i : ℤ), fun _ => intUp (i : ℤ)⟩ : Interval (Vec 𝕋 1)).construct :=
    fun _ => (show toReal (intDown (i : ℤ) : 𝕋) ≤ (i : ℝ) ∧
        (i : ℝ) ≤ toReal (intUp (i : ℤ) : 𝕋) from
      ⟨by simpa using hi.1, by simpa using hi.2⟩)
  have hstp : (fun _ => s : Vec ℝ 1) ∈
      (⟨fun _ => step.inf, fun _ => step.sup⟩ : Interval (Vec 𝕋 1)).construct := fun _ => hs
  -- the angle, then its cosine and sine
  have hprod := Interval.times_outer
    (⟨fun _ => intDown (i : ℤ), fun _ => intUp (i : ℤ)⟩ : Interval (Vec 𝕋 1))
    ⟨fun _ => step.inf, fun _ => step.sup⟩ ⟨_, hidx, _, hstp, rfl⟩
  have hang := Interval.plus_outer a₀ _ (Set.add_mem_add ha hprod)
  have hcos := Interval.cos_outer p _ ⟨_, hang, rfl⟩
  have hsin := Interval.sin_outer p _ ⟨_, hang, rfl⟩
  -- the radius and the center's coordinates
  have hrad : (fun _ => toReal r : Vec ℝ 1) ∈
      (Interval.point fun _ => r : Interval (Vec 𝕋 1)).construct := fun _ => ⟨le_rfl, le_rfl⟩
  have hc0 : (fun _ => c 0 : Vec ℝ 1) ∈
      (⟨fun _ => ctr.inf 0, fun _ => ctr.sup 0⟩ : Interval (Vec 𝕋 1)).construct := fun _ => hc 0
  have hc1 : (fun _ => c 1 : Vec ℝ 1) ∈
      (⟨fun _ => ctr.inf 1, fun _ => ctr.sup 1⟩ : Interval (Vec 𝕋 1)).construct := fun _ => hc 1
  have hx := Interval.plus_outer _ _ (Set.add_mem_add hc0
    (Interval.times_outer _ _ ⟨_, hrad, _, hcos, rfl⟩))
  have hy := Interval.plus_outer _ _ (Set.add_mem_add hc1
    (Interval.times_outer _ _ ⟨_, hrad, _, hsin, rfl⟩))
  intro j
  fin_cases j
  · exact hx 0
  · exact hy 0

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
