module

public import CORALean.ContSet.Capsule.Float.Operations.Basic

@[expose] public section

/-!
# `Capsule.enclosePoints`, over a floating-point scalar

CORA's `@capsule/enclosePoints.m`, as the exact layer reads it: the centre is the mean, the
generator runs to the point farthest from it, and the radius is the largest distance of a point from
the axis. No points give the empty capsule.

At float each step is rounded and the result is checked rather than assumed: the mean is the rounded
sum over a rounded-up count, the farthest point is picked by comparing squared lengths with the
certified `le` (a wrong pick only costs radius), and the radius is the largest rounded-up length of
the residual `p - (c + t g)` of each point against the stored centre and generator, at the
projection parameter `t` clamped to `[-1, 1]`, so the capsule holds every point whatever the
roundings. `k` is the number of Newton steps of the roots (`Global/Float/Sqrt`).
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
    ⟨c, g, maximumOver fun j => normUp k (res j)⟩
  else Capsule.empty n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
