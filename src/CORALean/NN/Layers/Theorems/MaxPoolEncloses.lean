module

public import CORALean.NN.Layers.Definitions.Basic
public import CORALean.NN.Layers.Operations.MaxPool
public import CORALean.NN.Layers.Theorems.LeMaxPoolGapUp
public import CORALean.NN.Layers.Theorems.Real.MaxPoolBounds
public import CORALean.NN.Layers.Theorems.MaxPoolGapUpNonneg
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
matrix, and what it misses lies in `[0, gap]` by `maxPool_bounds` at the rounded-up gap.
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


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.maxPool_encloses (tap : Fin m → Fin (k + 1) → Fin n)
    (pivot : Interval (Vec 𝕋 n) → Fin m → Fin (k + 1)) :
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
      (⟨fun _ => zero, maxPoolGapUp tap p I⟩ : Interval (Vec 𝕋 m)) := by
    intro j
    have h := Real.maxPool_bounds (tap j) (p j) (toRealVec I.inf) (toRealVec I.sup) x hbox
      (maxPoolGapUp_nonneg tap p I j) fun l hl => le_maxPoolGapUp tap p I j hl
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
