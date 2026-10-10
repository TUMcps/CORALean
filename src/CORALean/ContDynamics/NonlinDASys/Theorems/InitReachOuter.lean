import CORALean.ContDynamics.NonlinDASys.Operations.InitReach
import CORALean.ContDynamics.NonlinDASys.Definitions.LinPointCertifies
import CORALean.ContDynamics.NonlinDASys.Theorems.LinReachOuter
import CORALean.ContSet.Zonotope.Real.Theorems.SplitUnion

/-!
# `initReach` holds every run whose start set's linearization certifies it

A run of the DAE on `[0, Δt]` starting in one of the start sets is in the time-point set at
`Δt`, and in the time-interval and joint sets throughout, of one entry `initReach` returns,
provided every start set holding `x(0)` comes with a linearization that certifies the run
(`LinPoint.Certifies`, the hypotheses of `linReach_outer`). Whatever `select` splits, the two
halves cover the set they came from (`Zonotope.split_union`), so the run's start lies in one
of them, and the induction on the fuel ends in a `linReach` of a set holding it. Outer.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n p m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run starting in a set of `Rstart`, certified by the linearization of every set holding its
start, lies in the sets of one entry of `initReach` over the step. -/
theorem NonlinDASys.Trajectory.initReach_outer {sys : NonlinDASys n p m} {Δt : ℝ}
    {R₀ : Zonotope (Vec ℝ n)} {U : Zonotope (Vec ℝ m)} {x : ℝ → Vec ℝ n} {y : ℝ → Vec ℝ p}
    {u : ℝ → Vec ℝ m} (traj : sys.Trajectory (S := 𝒵) (Set.Icc 0 Δt) R₀ U x y u)
    (hΔt : 0 < Δt) {lin : Zonotope (Vec ℝ n) → NonlinDASys.LinPoint n p m}
    {select : (Z : Zonotope (Vec ℝ n)) → Option (Fin Z.h)} {q : ℕ}
    (hcert : ∀ Z : Zonotope (Vec ℝ n), x 0 ∈ Z.construct → (lin Z).Certifies sys U Δt q x y u)
    (fuel : ℕ) {Rstart : List (Zonotope (Vec ℝ n))} (hstart : ∃ Z ∈ Rstart, x 0 ∈ Z.construct) :
    ∃ R ∈ sys.initReach lin select U Δt (q + 2) fuel Rstart,
      x Δt ∈ R.1.construct ∧
        ∀ t ∈ Set.Icc 0 Δt,
          x t ∈ R.2.1.construct ∧ (x t, y t) ∈ R.2.2.construct := by -- --- PROOF ---
  induction fuel generalizing Rstart with
  | zero =>
    obtain ⟨Z, hZ, hx0⟩ := hstart
    obtain ⟨F, Rz, hF, hR, hL, hLa, hus, h0, hε⟩ := hcert Z hx0
    -- no fuel left: the entry is `linReach` of `Z`
    refine ⟨_, List.mem_map.mpr ⟨Z, hZ, rfl⟩, ?_⟩
    exact NonlinDASys.Trajectory.linReach_outer (Rinit := Z)
      ⟨hx0, traj.input, traj.flow, traj.constraint⟩ hΔt hF hR hL hLa hus h0 hε
  | succ k ih =>
    obtain ⟨Z, hZ, hx0⟩ := hstart
    rw [NonlinDASys.initReach]
    cases hs : select Z with
    -- no split: `linReach` of `Z`, as at no fuel
    | none =>
      obtain ⟨F, Rz, hF, hR, hL, hLa, hus, h0, hε⟩ := hcert Z hx0
      refine ⟨_, List.mem_flatMap.mpr ⟨Z, hZ, by simp only [hs]; exact List.mem_singleton_self _⟩,
        ?_⟩
      exact NonlinDASys.Trajectory.linReach_outer (Rinit := Z)
          ⟨hx0, traj.input, traj.flow, traj.constraint⟩ hΔt hF hR hL hLa hus h0 hε
    -- a split: the start lies in one half, and the halves are run again
    | some j =>
      have hhalf : x 0 ∈ (Z.split j).1.construct ∪ (Z.split j).2.construct := by
        rw [Zonotope.split_union]; exact hx0
      obtain ⟨R, hR, hRx⟩ := ih (Rstart := [(Z.split j).1, (Z.split j).2]) (by
        rcases hhalf with h | h
        · exact ⟨_, List.mem_cons_self .., h⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), h⟩)
      refine ⟨R, List.mem_flatMap.mpr ⟨Z, hZ, ?_⟩, hRx⟩
      simp only [hs]
      exact hR

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
