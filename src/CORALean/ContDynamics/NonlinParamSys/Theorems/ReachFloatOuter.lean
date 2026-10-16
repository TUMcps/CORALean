module

public import CORALean.ContDynamics.NonlinParamSys.Operations.ReachFloat
public import CORALean.ContDynamics.NonlinParamSys.Theorems.IsConstTrajectoryToAugment
public import CORALean.ContDynamics.NonlinearSys.Theorems.ReachFloatOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.CartProdExact
public import CORALean.ContSet.Zonotope.Float.Theorems.ProjectOuter

@[expose] public section

/-!
# The float parametric run encloses every constant-parameter run

Where `fm` encloses the lifted system, every run of `ẋ = f(x, u, p)` from `X₀` under inputs in `U`
with one parameter `p ∈ P` is, at every time of window `k`, in the `k`-th set
`NonlinParamSys.reachFloat` returns. An outer statement.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinParamSys.reachFloat_outer (sys : NonlinParamSys n m q)
    {fm : NonlinearSys.FloatModel 𝕋 (n + q) m} (h : fm.Encloses sys.augment)
    {P : Zonotope (Vec 𝕋 q)}
    {params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 m)) ℚ}
    {options : LinearSys.ReachOptions 𝕋} {Rs : List (Zonotope (Vec 𝕋 n))}
    (hR : sys.reachFloat fm P params options = some Rs) :
    ∃ N : ℕ, (N : ℝ) * toReal options.Δt = (params.tFinal : ℝ) - params.tStart ∧
      Rs.length = N ∧ ∀ {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {p : Vec ℝ q},
        sys.IsConstTrajectory (S := 𝒮)
          (Set.Icc 0 ((params.tFinal : ℝ) - params.tStart)) params.X₀.construct
          params.U.construct P.construct x u p →
        ∀ (k : ℕ) (hk : k < Rs.length), ∀ t ∈ Set.Icc ((k : ℝ) * toReal options.Δt)
          (((k : ℝ) + 1) * toReal options.Δt), x t ∈ Rs[k].construct := by -- --- PROOF ---
  unfold NonlinParamSys.reachFloat at hR
  simp only [Option.map_eq_some_iff] at hR
  obtain ⟨Ra, hRa, rfl⟩ := hR
  obtain ⟨N, hN, hlen, hout⟩ := h.reachFloat_outer hRa
  refine ⟨N, hN, by simpa using hlen, fun {x u p} traj k hk t ht => ?_⟩
  have hk' : k < Ra.length := by simpa using hk
  have haug := hout (x := fun t => Fin.append (x t) p) (u := u)
    (traj.toAugment (Z₀ := (params.X₀.cartProd P).construct) fun v hv w hw => by
      rw [Zonotope.cartProd_exact]
      exact ⟨(v, w), ⟨hv, hw⟩, rfl⟩) k hk' t ht
  have hproj := Zonotope.project_outer Ra[k] (Fin.castAdd q) ⟨_, haug, rfl⟩
  simpa [Fin.append_left] using hproj

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
