module

public import CORALean.ContSet.Capsule.Float.Operations.Basic

@[expose] public section

/-!
# `Capsule.enclosePoints`, over a floating-point scalar

Center is the mean of points, generator runs to the farthest, radius is the max distance to the
axis. Each step rounded and checked. The farthest point is picked by comparing squared lengths,
the radius by rounded-up residual lengths with projection `t` clamped to `[-1, 1]`. The capsule
is computed (not a rounded image of an exact one), so the error box is the origin. `k` is Newton
iterations for sqrt.

## Inputs
* `k` – Newton steps for sqrt
* `N` – number of points
* `pts` – the points

## Output
* a capsule enclosing all the points
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Capsule.enclosePoints (k : ℕ) {N : ℕ} (pts : Fin N → Vec 𝕋 n) : Capsule 𝕋 n :=
  if h : 0 < N then
    let c := fun i => divUp (sumUp fun j => pts j i) (nsmulUp N one)
    let d := fun j i => subUp (pts j i) (c i)
    let dist := fun j => sqSumUp fun i => absolute (d j i)
    let jmax := (List.finRange N).foldl (fun b j => if le (dist b) (dist j) then j else b) ⟨0, h⟩
    let g := d jmax
    let t := fun j =>
      minimum (maximum (divUp (dotUp (d j) g) (sqSumUp fun i => absolute (g i))) (neg one)) one
    let res := fun j i => maximum
      (absolute (subDown (subDown (pts j i) (c i)) (mulUp (t j) (g i))))
      (absolute (subUp (subUp (pts j i) (c i)) (mulDown (t j) (g i))))
    ⟨c, g, maximumOver fun j => normUp k (res j), Interval.origin n⟩
  else Capsule.empty n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
