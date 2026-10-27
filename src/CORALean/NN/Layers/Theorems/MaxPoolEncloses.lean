module

public import CORALean.NN.Layers.Definitions.Basic
public import CORALean.NN.Layers.Operations.MaxPool
public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.Global.Tensor
public import CORALean.NN.Layers.Theorems.Real.Basic
public import Mathlib.Tactic.Linarith
public import CORALean.NN.Layers.Theorems.SelectMatMulVec
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# What the max pooling layer encloses

Each window's maximum over ℝ, `Real.windowMax`: the pivot's value is carried by the selection
matrix, and what it misses lies in `[0, gap]` by `aux_maxPool_bounds` at the rounded-up gap.

## Inputs
* `tap` – input index of every window position
* `pivot` – position of the largest entry for each window

## Hypotheses
* none

## Conclusion
* the layer encloses the maximum over every window
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

-- `Matrix` unscoped would make `FloatOps.zero` ambiguous; only `*ᵥ` is wanted
open scoped Matrix
open Pointwise ContSet Plus Mtimes Float Float.IntervalOuter Float.OfInterval Float.FloatOps
  Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n m k : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

namespace Real
section
variable {n : ℕ}

/-- The window's maximum above its pivot, for *any* `g` bounding the other taps' reach. -/
private theorem aux_maxPool_bounds {k : ℕ} (t : Fin (k + 1) → Fin n) (p : Fin (k + 1))
    (lo hi x : Vec ℝ n) (hx : ∀ i, lo i ≤ x i ∧ x i ≤ hi i) {g : ℝ} (hg0 : 0 ≤ g)
    (hg : ∀ l, l ≠ p → hi (t l) - lo (t p) ≤ g) : -- --- CONCL ---
    0 ≤ windowMax (fun l => x (t l)) - x (t p) ∧
      windowMax (fun l => x (t l)) - x (t p) ≤ g := by -- --- PROOF ---
  refine ⟨by linarith [le_windowMax (fun l => x (t l)) p], ?_⟩
  have h : windowMax (fun l => x (t l)) ≤ x (t p) + g := by
    refine windowMax_le fun l => ?_
    by_cases hl : l = p
    · rw [hl]
      linarith
    · linarith [(hx (t l)).2, (hx (t p)).1, hg l hl]
  linarith

end
end Real


section
open Float.SoundFloatArithmetic
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m k : ℕ}

/-- A pooled window's gap is nonnegative. -/
private theorem aux_maxPoolGapUp_nonneg (tap : Fin m → Fin (k + 1) → Fin n)
    (p : Fin m → Fin (k + 1))
    (I : Interval (Vec 𝕋 n)) (j : Fin m) : 0 ≤ toReal (step_maxPoolGapUp tap p I j) := by
  have h := le_maximumOver
    (fun l => if l = p j then zero else subUp (I.sup (tap j l)) (I.inf (tap j (p j)))) (p j)
  rw [if_pos rfl, toReal_zero] at h
  exact h

end


section
open Float.SoundFloatArithmetic
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m k : ℕ}

/-- A pooled window's gap bounds every other tap's reach. -/
private theorem aux_le_maxPoolGapUp (tap : Fin m → Fin (k + 1) → Fin n) (p : Fin m → Fin (k + 1))
    (I : Interval (Vec 𝕋 n)) (j : Fin m) {l : Fin (k + 1)} (hl : l ≠ p j) :
    toReal (I.sup (tap j l)) - toReal (I.inf (tap j (p j)))
      ≤ toReal (step_maxPoolGapUp tap p I j) := by
  have h := le_maximumOver
    (fun l => if l = p j then zero else subUp (I.sup (tap j l)) (I.inf (tap j (p j)))) l
  rw [if_neg hl] at h
  exact le_trans (sub_le_subUp _ _) h

end


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.maxPool_encloses (tap : Fin m → Fin (k + 1) → Fin n)
    (pivot : Interval (Vec 𝕋 n) → Fin m → Fin (k + 1)) : -- --- CONCL ---
    (Layer.maxPool (S := S) tap pivot).Encloses
      (fun x j => Real.windowMax fun l => x (tap j l)) := by -- --- PROOF ---
  refine ⟨fun s x hx => ?_⟩
  have hbox : ∀ i, toReal ((interval s).inf i) ≤ x i ∧ x i ≤ toReal ((interval s).sup i) :=
    interval_outer s hx
  set I := interval s with hI
  set p := pivot I with hp
  set A : Mat ℝ m n := Scalar.toRealMat (selectMat (𝕋 := 𝕋) fun j => tap j (p j)) with hA
  -- what the pivot misses, which is what the box holds
  set d : Vec ℝ m := fun j => Real.windowMax (fun l => x (tap j l)) - x (tap j (p j))
    with hd
  have hsplit : (fun j => Real.windowMax fun l => x (tap j l)) = A *ᵥ x + d := by
    funext j
    have hsel : (A *ᵥ x) j = x (tap j (p j)) := by
      rw [hA]
      exact selectMat_mulVec (fun j => tap j (p j)) x j
    show Real.windowMax (fun l => x (tap j l)) = (A *ᵥ x) j + d j
    rw [hsel, hd]
    ring
  -- the window's bound, at the rounded-up gap it was stated for
  have hmem : d ∈ Interval.construct
      (⟨fun _ => zero, step_maxPoolGapUp tap p I⟩ : Interval (Vec 𝕋 m)) := by
    intro j
    have h := Real.aux_maxPool_bounds (tap j) (p j) (toRealVec I.inf) (toRealVec I.sup) x hbox
      (aux_maxPoolGapUp_nonneg tap p I j) fun l hl => aux_le_maxPoolGapUp tap p I j hl
    have hz : toReal (zero : 𝕋) ≤ d j := by
      rw [toReal_zero]
      exact h.1
    exact ⟨hz, h.2⟩
  have hA' : A ∈ ContSet.construct (selectMat (𝕋 := 𝕋) fun j => tap j (p j)) := by
    rw [ContSet.construct_mat]
    exact hA
  rw [hsplit]
  exact plus_outer _ _ (Set.add_mem_add
    (mtimes_outer _ s (Set.mem_biUnion hA' (Set.mem_image_of_mem _ hx)))
    (ofInterval_outer _ hmem))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
