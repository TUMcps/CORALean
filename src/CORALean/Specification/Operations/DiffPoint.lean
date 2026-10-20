module

public import CORALean.Specification.Specification
public import CORALean.Global.SupportFunction.SupportFunction

@[expose] public section

/-!
# [1, Alg. 3 (exits), l. 10]: the witness difference along a direction

`diffPoint`: the difference between a reachable-set witness point and an unsafe-set witness
point along `d`, fed into `P̲`.

Real-only, a specification: it takes the difference of two witness points chosen by oracles that
quantify over every direction.

## Inputs
* `wO` – witnesses of the reachable set
* `wU` – witnesses of the unsafe set
* `d` – direction

## Output
* the difference of the witness points along the direction

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Sonnet 5
-- Written:       16-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type} [AddCommGroup α] [Module ℝ α] {O U : Set α}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3 (exits), l. 10]: the difference between a reachable-set witness point
and an unsafe-set witness point along `d`, fed into `P̲`. -/
noncomputable def diffPoint (wO : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness O d)
    (wU : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness U d) (d : α →ₗ[ℝ] ℝ) : α :=
  -- 10. `ν(Ř(t), ℓᵢ)`, the support vector of the reachable set along `ℓᵢ = d`
  let ν_R := (wO d).mem.choose
  -- 10. `ν(L, −ℓᵢ)`, the support vector of the unsafe set along `−ℓᵢ`
  let ν_L := (wU (-d)).mem.choose
  -- 10. `v̌ᵢ ← ν(Ř(t), ℓᵢ) − ν(L, −ℓᵢ)`
  ν_R - ν_L

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
