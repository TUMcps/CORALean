module

public import CORALean.ContDynamics.NonlinearSys.Definitions.IsAbstractionError
public import CORALean.ContDynamics.NonlinearSys.Definitions.IsPolyAbstractionError
public import CORALean.ContSet.PolyZonotope.Real.Instances
public import CORALean.ContSet.PolyZonotope.Real.Operations.SubsetAt
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PointMemConstruct

@[expose] public section

/-!
# A polynomial certificate is a certificate

Forgetting the dependency: read at a factor vector the error is `L`'s point there and `W` around
it, so over the whole sub-box it is a member of `L ⊞ W`, and the states the sub-box names are
`subsetAt`. That is `IsAbstractionError` at `S := 𝒫𝒵`, so every theorem downstream —
`linInput_outer`, `reach_outer_horizon`, `relinReach_outer` — applies to the polynomialization
variant unchanged. The converse fails: `L ⊞ W` says only that the error is *somewhere* in a set.
`hBa` is what `subsetAt` needs to name members rather than arbitrary points.

## Inputs
* `f` – field
* `A` – state Jacobian
* `B` – input Jacobian
* `xs` – state expansion point
* `us` – input expansion point
* `pZ` – region polynomial zonotope
* `Ba` – factor domain
* `U` – input region
* `L` – error polynomial zonotope
* `W` – remainder polynomial zonotope

## Hypotheses
* `hp` – factor counts agree
* `hBa` – factors bounded by one
* `cert` – polynomial certificate

## Conclusion
* the polynomial certificate gives an ordinary abstraction-error certificate
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Pointwise ContSet Plus PolyZonotope

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point split into a member of `S` and the rest, which lies in `T`. -/
private theorem aux_mem_add_of_sub {α : Type} [AddCommGroup α] {S T : Set α} {e v : α}
    (hv : v ∈ S) (he : e - v ∈ T) : e ∈ S + T := by
  have h := Set.add_mem_add hv he
  rwa [show v + (e - v) = e from by abel] at h


-- =======================================  MAIN THEOREM  ======================================= --

/-- The dependency dropped: a polynomial certificate over `Ba` is an ordinary
certificate over the states `Ba` names. -/
theorem IsAbstractionError.of_poly {f : Vec ℝ n → Vec ℝ m → Vec ℝ n} {A : Mat ℝ n n}
    {B : Mat ℝ n m} {xs : Vec ℝ n} {us : Vec ℝ m} {pZ : PolyZonotope (Vec ℝ n)}
    {Ba : Set (Fin pZ.p → ℝ)} {U : Set (Vec ℝ m)} {L W : PolyZonotope (Vec ℝ n)}
    {hp : L.p = pZ.p} (hBa : ∀ a ∈ Ba, ∀ k, |a k| ≤ 1)
    (cert : IsPolyAbstractionError f A B xs us pZ Ba U L hp W) :
    IsAbstractionError (S := 𝒫𝒵) f A B xs us (pZ.subsetAt Ba) U (L ⊞ W) where
  encloses x hx u hu := by
    obtain ⟨a, ha, rfl⟩ := hx
    exact plus_outer L W
      (aux_mem_add_of_sub (L.point_mem_construct fun k => hBa a ha _) (cert.encloses a ha u hu))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
