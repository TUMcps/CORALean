module

public import CORALean.ContDynamics.NonlinDASys.Definitions.CompositionalState
public import CORALean.ContDynamics.NonlinDASys.Operations.EnlargeInterfaceInput
public import CORALean.ContDynamics.NonlinDASys.Operations.ComposeSubsystems

@[expose] public section

/-!
# `NonlinDASys.reachNextCompositional`

[1, Alg. 2]: the reachable sets of the subsystems of a partitioned power system, one step. Each
pass re-enlarges the interface inputs of the subsystems whose assumption is not yet confirmed
(line 5, [1, Eq. 14]), runs [1, Alg. 1] on them (line 6, the argument `subReach`), joins the
local sets (line 9, [1, Eq. 15]) and tests, for every subsystem, that the joined set read at its
interface, `Υ⁽ⁱ⁾ R(τ_k)`, lies in `Λ⁽ⁱ⁾ Û⁽ⁱ⁾` (lines 10-15), until all do (line 18). Line 1's
all-false flags are the start state's. Line 16 sets `U⁽ⁱ⁾ = Λ Û ⊕ (I - Λ) U`.

The `repeat` has no stated bound: `fuel` bounds the passes, and the result is `none` where it
runs out. `sub` is the inclusion test; `[1, Alg. 2]` is described under the assumption that no
split is required.

## References

* [1] M. Althoff. "Formal and Compositional Analysis of Power Systems using Reachable Sets".
      IEEE Transactions on Power Systems, 29(5):2270-2280, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {ns n : ℕ} {m e d : Fin ns → ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2]: the `R⁽ⁱ⁾ᵈ(t_{k+1})`, `R(τ_k)` and `Û⁽ⁱ⁾` of the last pass, or `none` after
`fuel` passes without every flag set. -/
def NonlinDASys.reachNextCompositional
    (subReach : ∀ i, Zonotope (Vec ℝ (m i)) → Zonotope (Vec ℝ (e i)) × Zonotope (Vec ℝ (d i)))
    (Φ : ∀ i, Mat ℝ n (d i)) (Υ : ∀ i, Mat ℝ (m i) n) (Λ : ∀ i, Mat ℝ (m i) (m i)) (lamU : ℝ)
    (sub : ∀ {k : ℕ}, Zonotope (Vec ℝ k) → Zonotope (Vec ℝ k) → Bool) :
    ℕ → NonlinDASys.CompositionalState m e d →
      Option ((∀ i, Zonotope (Vec ℝ (e i))) × Zonotope (Vec ℝ n) × (∀ i, Zonotope (Vec ℝ (m i))))
  | 0, _ => none
  | fuel + 1, s =>
      -- 3.-8. the subsystems without a confirmed assumption, `Û⁽ⁱ⁾` by Eq. 14, Alg. 1 on it
      let pass : ∀ i, Zonotope (Vec ℝ (m i)) × Zonotope (Vec ℝ (e i)) × Zonotope (Vec ℝ (d i)) :=
        fun i =>
          if s.inputEnclosure i then (s.Uhat i, s.Rnext i, s.Rloc i)
          else
            -- 5. `Û⁽ⁱ⁾ ← ` the enlarged interface input, Eq. 14
            let Uhat := NonlinDASys.enlargeInterfaceInput lamU (Λ i) (s.U i).c (s.U i)
            -- 6. `R⁽ⁱ⁾ᵈ(t_{k+1}), R⁽ⁱ⁾(τ_k)` by Alg. 1 on subsystem `i`
            (Uhat, subReach i Uhat)
      -- 9. `R(τ_k)` composed from the subsystems
      let R : Zonotope (Vec ℝ n) :=
        NonlinDASys.composeSubsystems Φ fun i => (pass i).2.2
      -- 11.-15. the flag of subsystem `i`: `Υ⁽ⁱ⁾R ⊆ Λ⁽ⁱ⁾Û⁽ⁱ⁾`
      let inputEnclosure : Fin ns → Bool := fun i =>
        sub (Zonotope.mtimes (Υ i) R) (Zonotope.mtimes (Λ i) (pass i).1)
      -- 16. the next assumption `U⁽ⁱ⁾ ← Λ⁽ⁱ⁾Û⁽ⁱ⁾ ⊕ (1 - Λ⁽ⁱ⁾)U⁽ⁱ⁾`
      let U : ∀ i, Zonotope (Vec ℝ (m i)) := fun i =>
        (Zonotope.mtimes (Λ i) (pass i).1).plus (Zonotope.mtimes (1 - Λ i) (s.U i))
      -- 18. `until` every flag is set
      if ∀ i, inputEnclosure i = true then
        some (fun i => (pass i).2.1, R, fun i => (pass i).1)
      else
        NonlinDASys.reachNextCompositional subReach Φ Υ Λ lamU sub fuel
          ⟨inputEnclosure, U, fun i => (pass i).1, fun i => (pass i).2.1, fun i => (pass i).2.2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
