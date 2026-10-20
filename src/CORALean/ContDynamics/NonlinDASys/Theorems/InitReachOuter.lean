module

public import CORALean.ContDynamics.NonlinDASys.Operations.InitReach
public import CORALean.ContDynamics.NonlinDASys.Definitions.LinPointCertifies
public import CORALean.ContDynamics.NonlinDASys.Theorems.LinReachOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.SplitUnion

@[expose] public section

/-!
# `initReach` holds every run whose start set's linearization certifies it

A run of the DAE on `[0, Δt]` starting in one of the start sets is in the time-point set at
`Δt`, and in the time-interval and joint sets throughout, of one entry `initReach` returns,
provided every start set holding `x(0)` comes with a linearization that certifies the run
(`LinPoint.Certifies`, the hypotheses of `linReach_outer`). Whatever `select` splits, the two
halves cover the set they came from (`Zonotope.split_union`), so the run's start lies in one
of them, and the induction on the fuel ends in a `linReach` of a set holding it. Outer.

## Inputs
* `sys` – system
* `Δt` – step size
* `R₀` – initial zonotope
* `U` – input zonotope
* `x` – differential trajectory
* `y` – algebraic trajectory
* `u` – input signal
* `z` – output signal
* `lin` – linearization of a start set
* `select` – choice of the generator to split along
* `q` – Taylor order minus two
* `fuel` – splitting depth
* `Rstart` – start sets

## Hypotheses
* `traj` – DAE trajectory
* `hΔt` – step positive
* `hcert` – every start set holding the start has a certifying linearization
* `hstart` – the start lies in a start set

## Conclusion
* the run lies in the sets of one returned entry
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n p m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run starting in a set of `Rstart`, certified by the linearization of every set holding its
start, lies in the sets of one entry of `initReach` over the step. -/
theorem NonlinDASys.IsTrajectory.initReach_outer {sys : NonlinDASys n p m} {Δt : ℝ}
    {R₀ : Zonotope (Vec ℝ n)} {U : Zonotope (Vec ℝ m)} {x : ℝ → Vec ℝ n} {y : ℝ → Vec ℝ p}
    {u : ℝ → Vec ℝ m} {z : ℝ → Vec ℝ sys.q}
    (traj : sys.IsTrajectory (S := 𝒵) (Set.Icc 0 Δt) R₀ U x y u z)
    (hΔt : 0 < Δt) {lin : Zonotope (Vec ℝ n) → NonlinDASys.LinPoint n p m}
    {select : (Z : Zonotope (Vec ℝ n)) → Option (Fin Z.h)} {q : ℕ}
    (hcert : ∀ Z : Zonotope (Vec ℝ n), x 0 ∈ Z.construct → (lin Z).Certifies sys U Δt q x y u)
    (fuel : ℕ) {Rstart : List (Zonotope (Vec ℝ n))}
    (hstart : ∃ Z ∈ Rstart, x 0 ∈ Z.construct) : -- --- CONCL ---
    ∃ R ∈ sys.initReach lin select U Δt (q + 2) fuel Rstart,
      x Δt ∈ R.fst.construct ∧
        ∀ t ∈ Set.Icc 0 Δt,
          x t ∈ R.snd.1.construct ∧ (x t, y t) ∈ R.snd.2.construct := by -- --- PROOF ---
  induction fuel generalizing Rstart with
  | zero =>
    obtain ⟨Z, hZ, hx0⟩ := hstart
    obtain ⟨F, Rz, hF, hR, hL, hLa, hus, h0, hε⟩ := hcert Z hx0
    -- no fuel left: the entry is `linReach` of `Z`
    refine ⟨_, List.mem_map.mpr ⟨Z, hZ, rfl⟩, ?_⟩
    exact NonlinDASys.IsTrajectory.linReach_outer (Rinit := Z)
      ⟨hx0, traj.input, traj.meas, traj.integrable, traj.cont, traj.flow, traj.constraint,
        traj.output⟩ hΔt hF hR hL hLa hus h0 hε
  | succ k ih =>
    obtain ⟨Z, hZ, hx0⟩ := hstart
    rw [NonlinDASys.initReach]
    cases hs : select Z with
    -- no split: `linReach` of `Z`, as at no fuel
    | none =>
      obtain ⟨F, Rz, hF, hR, hL, hLa, hus, h0, hε⟩ := hcert Z hx0
      refine ⟨_, List.mem_flatMap.mpr ⟨Z, hZ, by simp only [hs]; exact List.mem_singleton_self _⟩,
        ?_⟩
      exact NonlinDASys.IsTrajectory.linReach_outer (Rinit := Z)
        ⟨hx0, traj.input, traj.meas, traj.integrable, traj.cont, traj.flow, traj.constraint,
          traj.output⟩ hΔt hF hR hL hLa hus h0 hε
    -- a split: the start lies in one half, and the halves are run again
    | some j =>
      have hhalf : x 0 ∈ (Z.split j).fst.construct ∪ (Z.split j).snd.construct := by
        rw [Zonotope.split_union]; exact hx0
      obtain ⟨R, hR, hRx⟩ := ih (Rstart := [(Z.split j).fst, (Z.split j).snd]) (by
        rcases hhalf with h | h
        · exact ⟨_, List.mem_cons_self .., h⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), h⟩)
      refine ⟨R, List.mem_flatMap.mpr ⟨Z, hZ, ?_⟩, hRx⟩
      simp only [hs]
      exact hR

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
