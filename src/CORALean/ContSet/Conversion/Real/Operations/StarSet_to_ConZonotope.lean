module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import CORALean.ContSet.StarSet.Real.StarSet

@[expose] public section

/-!
# A star set as a constrained zonotope

The factor box `[l, u]` is rescaled to `[-1, 1]`: `α_k = mid_k + rad_k β_k`, with
`mid = (l + u) / 2` and `rad = (u - l) / 2`. The center moves by `G · mid`, the generators are
scaled by `rad`, and a row `a · α ≤ b` becomes `(a ∘ rad) · β ≤ b - a · mid` on the coefficients,
one halfspace each.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def StarSet.conZonotope (s : StarSet StarSet.LinPred n) : ConZonotope (Vec ℝ n) where
  h := s.m
  c := fun i => s.c i + ∑ k, s.G i k * ((s.pred.l k + s.pred.u k) / 2)
  G := fun k i => s.G i k * ((s.pred.u k - s.pred.l k) / 2)
  P :=
    { m := s.pred.cons.length
      A := fun i =>
        ∑ k, ((s.pred.cons.get i).1 k * ((s.pred.u k - s.pred.l k) / 2)) • LinearMap.proj k
      b := fun i =>
        (s.pred.cons.get i).2 - ∑ k, (s.pred.cons.get i).1 k * ((s.pred.l k + s.pred.u k) / 2)
      me := 0
      Ae := Fin.elim0
      be := Fin.elim0 }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
