module

public import CORALean.ContSet.PolyLevelSet.Real.PolyLevelSet

@[expose] public section

/-!
# `PolyLevelSet.switch`

Each row's right-hand side `bᵢ` taken at the weight `(1 + σᵢ x^e) / 2`, `σᵢ = 1` where `sᵢ`
holds and `-1` elsewhere: one monomial `x^e` more, whose column is `-σᵢ bᵢ / 2`, and the
right-hand side halved. Where `x^e = σᵢ` the row is `P`'s own, and where `x^e = -σᵢ` its
right-hand side is gone (`eval_switch`), so a variable at `±1` switches the rows on and off.
Not one of CORA's operations: it is the lower block of [1, Thm. 1]'s union, as CORA's
`@conPolyZono/or` builds it, `[blkdiag(A₁, A₂), [-b₁; b₂] / 2]` over `b / 2`, with the selector
factor for `x^e`.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Row `i` with `bᵢ` weighted by `(1 + σᵢ x^e) / 2`, `σᵢ = 1` where `s i` and `-1` elsewhere. -/
noncomputable def PolyLevelSet.switch (P : PolyLevelSet n) (e : Fin n → ℕ) (s : Fin P.m → Bool) :
    PolyLevelSet n where
  m := P.m
  q := P.q + 1
  A i := Fin.append (P.A i) fun _ => if s i then -(2⁻¹ * P.b i) else 2⁻¹ * P.b i
  R k := Fin.append (P.R k) fun _ => e k
  b i := 2⁻¹ * P.b i
  op := P.op
  dom := P.dom

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
