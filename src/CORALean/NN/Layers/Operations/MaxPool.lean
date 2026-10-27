module

public import CORALean.ContSet.Conversion.Float.Instances
public import CORALean.NN.Layers.Layer
public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.NN.Layers.Operations.SelectMat
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The max pooling layer

CORA's `nnMaxPool2DLayer`, which does not fit `Relaxation`: a pooled output is a function of
`k + 1` inputs over `k + 1` intervals, and its affine part is a *selection*, not a diagonal. What
carries over is the shape: an affine part through `mtimes` and a box for the rest. The affine
part is one input per window, the pivot, and the box is `[0, gap]`, a maximum never being below
its arguments; `gap` is zero exactly when the pivot dominates the window, so a stable window is
exact. `pivot` is precision and never soundness, as ReLU's slope is, so it may read `le`.

## Inputs
* `tap` – input index of every window position
* `pivot` – position of the largest entry for each window

## Output
* layer taking the maximum of every window
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

-- `Matrix` unscoped would make `FloatOps.zero` ambiguous
open ContSet Plus Mtimes Float Float.IntervalOuter Float.OfInterval Float.FloatOps

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n m k : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

section
variable {𝕋 : Type} [FloatOps 𝕋] {n m k : ℕ}

/-- Zero at the pivot, every other tap's reach rounded up. -/
@[step_of Layer.maxPool]
def step_maxPoolGapUp (tap : Fin m → Fin (k + 1) → Fin n) (p : Fin m → Fin (k + 1))
    (I : Interval (Vec 𝕋 n)) (j : Fin m) : 𝕋 :=
  maximumOver fun l =>
    if l = p j then zero else subUp (I.sup (tap j l)) (I.inf (tap j (p j)))

end


-- =====================================  MAIN DEFINITION  ====================================== --

def Layer.maxPool (tap : Fin m → Fin (k + 1) → Fin n)
    (pivot : Interval (Vec 𝕋 n) → Fin m → Fin (k + 1)) : Layer S n m where
  enclose s :=
    plus (mtimes (selectMat (𝕋 := 𝕋) fun j => tap j (pivot (interval s) j)) s)
      (ofInterval (⟨fun _ => zero, step_maxPoolGapUp tap (pivot (interval s)) (interval s)⟩ :
        Interval (Vec 𝕋 m)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
