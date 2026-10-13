module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.EuclideanNorm

@[expose] public section

/-!
# `Zonotope.normExactCora`, CORA's `norm(Z,2,'exact')`

`norm(Z,2,'exact')` (`@contSet/norm.m`, `@zonotope/norm_.m`: "computes maximum norm value") runs
`private/priv_norm_exact.m`. It solves `min_{b ∈ {0,1}ᵐ} 4 (b - ½)ᵀ M (b - ½)` with
`M = λ_max I - GᵀG` (l. 52-54; YALMIP at l. 126-132, MOSEK's equivalent cone program at l. 99-114
has the same minimisers), i.e. maximises `‖G u‖` over `u = 2b - 1 ∈ {-1, 1}ᵐ`, ignoring the
centre, and then returns `‖G u* + c‖` (l. 124/133, 140). `binprog` is the solver, a caller's
argument; `lmax` too, since the minimisers do not depend on it. `G = []` (l. 44-47) gives `‖c‖`
either way. One `let` per line of the source.

## References

* [1] `contSet/@zonotope/private/priv_norm_exact.m`, CORA, ll. 43-54, 123-140.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1] at the solver `binprog`, which returns a point of `{0, 1}ᵐ` (as `Bool`s) for an
objective. -/
noncomputable def Zonotope.normExactCora (Z : Zonotope (Vec ℝ n)) (lmax : ℝ)
    (binprog : ((Fin Z.h → Bool) → ℝ) → (Fin Z.h → Bool)) : ℝ :=
  -- l. 43, 49-50: `G = Z.G`, `m`, `c = Z.c`
  let G := Z.G
  let m := Z.h
  let c := Z.c
  -- l. 52: `GG = G'*G`
  let GG : Mat ℝ m m := Matrix.of fun j k => G j ⬝ᵥ G k
  -- l. 54: `M = lmax*eye(m) - GG`
  let M : Mat ℝ m m := lmax • (1 : Mat ℝ m m) - GG
  -- l. 126-127: `b = binvar(m,1)`, `obj = 4*(b-0.5)'*M*(b-0.5)`
  let half : (Fin m → Bool) → Vec ℝ m := fun b j => (if b j then 1 else 0) - 1 / 2
  let obj : (Fin m → Bool) → ℝ := fun b => 4 * (half b ⬝ᵥ (M *ᵥ half b))
  -- l. 132: `optimize([], obj, options)`
  let b := binprog obj
  -- l. 133: `x = G*value(2*(b-0.5))+c`
  let x : Vec ℝ n := ∑ j, (2 * half b j) • G j + c
  -- l. 140: `val = norm(x)`
  ‖x‖₂

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
