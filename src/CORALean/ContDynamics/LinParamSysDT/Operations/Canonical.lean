module

public import CORALean.ContDynamics.LinParamSysDT.LinParamSysDT

@[expose] public section

/-!
# The canonical-form system at a given set of matrices

`x(k+1) = A(k) x(k) + u(k)` with `A(k)` in the set: `B` the point set `{I}` and `c = 0`, so its
`IsTrajectory` is its `IsCanonicalTrajectory`. It is the system an operation handed only the matrix
set builds: the discretization `e^{AΔt}` of a `LinearSys` or `LinParamSys`, enclosed, whose input
is already in state coordinates; `LinParamSys.canonical` in discrete time.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [OfIdentity 𝕄]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(A, {I}, 0)`, `n` inputs. -/
abbrev LinParamSysDT.canonical (A : 𝕄 n n) : LinParamSysDT 𝕄 n :=
  ⟨A, n, OfIdentity.identity n, 0⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
