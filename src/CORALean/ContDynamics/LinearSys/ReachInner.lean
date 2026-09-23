import CORALean.ContDynamics.LinearSys.ReachError
import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffRep

/-!
# An inner approximation of a continuous reachable set, over a whole run

`LinearSysDT.reachInner` at the sample times of a continuous-time system: the
sampled run minus everything it owes. `reachInner_inner` puts it inside the
integral reachable set at `t = kΔt`, the states the Carathéodory runs of the
system reach — the set `reachSet` is being migrated to (#105).

`timePointStepInner` is one step of this. Chaining needs the error as a set
that `e^{AΔt}` can carry, and a ball does not stay a ball under a matrix; its
box, `timePointStepErrorBox`, stays a zonotope. That is also what gives
`reachInnerRep`: `minkDiffRep` of the run by its error, at a generator
representation `M` the caller offers and the operation checks. A wrong `M`
gives `none`, costing precision and never soundness.

An outer approximation minus its error bound is [1]'s route to an inner one;
here the bound is a zonotope, carried along the run rather than restated.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Inner- and Outer-Approximations of
      Reachable Sets". IEEE Transactions on Automatic Control, vol. 68, no. 12,
      2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The sampled run minus its own accumulated error — an inner approximation of
the reachable set at `t = kΔt`, as a set. -/
noncomputable def LinearSys.reachInner (sys : LinearSys 𝕋 n) (Δt : ℝ) (η o : ℕ) (ho : 0 < o)
    (R₀ U : Zonotope (Vec ℝ n)) (k : ℕ) : Set (Vec ℝ n) :=
  minkowskiDiff
    ((sys.discretize Δt).reach (S := 𝒵) o ho R₀ (sys.inputSolution (S := 𝒵) Δt η U) k).construct
    (sys.reachError Δt η o ho R₀ U k).construct

/-- The same difference at a representation, `none` where the caller's
generator representation `M` does not check out. -/
noncomputable def LinearSys.reachInnerRep (sys : LinearSys 𝕋 n) (Δt : ℝ) (η o : ℕ)
    (ho : 0 < o) (R₀ U : Zonotope (Vec ℝ n)) (k : ℕ)
    (M : Fin ((sys.discretize Δt).reach (S := 𝒵) o ho R₀ (sys.inputSolution (S := 𝒵) Δt η U) k).h
      → Fin (sys.reachError Δt η o ho R₀ U k).h → ℝ) : Option (Zonotope (Vec ℝ n)) :=
  ((sys.discretize Δt).reach (S := 𝒵) o ho R₀ (sys.inputSolution (S := 𝒵) Δt η U) k).minkDiffRep
    (sys.reachError Δt η o ho R₀ U k) M

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
