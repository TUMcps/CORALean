module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import CORALean.ContSet.StarSet.Real.StarSet

@[expose] public section

/-!
# A star set as a constrained zonotope

The factor box `[l, u]` is rescaled to `[-1, 1]`: `α_k = mid_k + rad_k β_k`, with
`mid = (l + u) / 2` and `rad = (u - l) / 2`. The centre moves by `G · mid`, the generators are
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

noncomputable def StarSet.conZonotope (s : StarSet n) : ConZonotope (Vec ℝ n) where
  h := s.m
  c := fun i => s.c i + ∑ k, s.G i k * ((s.l k + s.u k) / 2)
  G := fun k i => s.G i k * ((s.u k - s.l k) / 2)
  P :=
    { m := s.cons.length
      A := fun i => ∑ k, ((s.cons.get i).1 k * ((s.u k - s.l k) / 2)) • LinearMap.proj k
      b := fun i => (s.cons.get i).2 - ∑ k, (s.cons.get i).1 k * ((s.l k + s.u k) / 2)
      me := 0
      Ae := Fin.elim0
      be := Fin.elim0 }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
