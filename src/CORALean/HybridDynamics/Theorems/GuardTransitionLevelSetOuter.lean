module

public import CORALean.ContSet.LevelSet.Real.Definitions.RangeBound
public import CORALean.HybridDynamics.Operations.GuardTransitionLevelSet
public import CORALean.HybridDynamics.Theorems.GuardIntersectLevelSetOuter

@[expose] public section

/-!
# The transition through a nonlinear guard encloses every jump

[1, Sec. 3.2]: if `bound` range-bounds `g` on each reachable set ([1, Def. 5]), `box` encloses
it, `contract` is a contractor for `g = 0` ([1, Def. 6]), `intersect` encloses the guard in a
box (`I ∩ {g = 0}`), `reset` encloses the image of a set under `r` and `unify` the union of a
list, then every state `x` of a reachable set `R(τⱼ)` on the guard has `r(x)` in the result.
A state on the guard passes Step 1, since `0 = g(x) ∈ [l, u]`; the contractor keeps it in its
box and in the united box of its run (`guardIntersectLevelSet_outer`); the rest is the chain of
the operators' guarantees. The grouping into runs of `μ` affects precision, not soundness.

## Inputs
* `R` – reach set type
* `T` – enclosure type
* `den` – denotation of a reach set
* `denT` – denotation of an enclosure
* `g` – guard function
* `r` – reset map
* `bound` – range bound of the guard function
* `box` – box enclosure
* `contract` – box contractor
* `μ` – chunk size
* `intersect` – guard intersection of a box
* `reset` – enclosure reset
* `unify` – union of enclosures
* `Rs` – reach sets
* `Rj` – reach set
* `x` – state

## Hypotheses
* `hbound` – bound holds on each reach set
* `hbox` – box encloses each reach set
* `hcontract` – contractor is valid
* `hintersect` – intersection encloses the guard
* `hreset` – reset encloses the image
* `hunify` – union encloses its members
* `hRj` – reach set is among the given ones
* `hx` – state lies in the reach set
* `hg` – guard function vanishes at the state

## Conclusion
* the reset image lies in the unified enclosure

## References

* [1] N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear
      Guard Sets". In Proc. of the 23rd ACM International Conference on Hybrid Systems:
      Computation and Control (HSCC), 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 3.2]: `r(x) ∈ unify(…)` for every `x ∈ R(τⱼ)` with `g(x) = 0`. -/
theorem Location.guardTransitionLevelSet_outer {R T : Type} {den : R → Set (Vec ℝ n)}
    {denT : T → Set (Vec ℝ n)} {g : Vec ℝ n → ℝ} {r : Vec ℝ n → Vec ℝ n}
    {bound : R → Real.Interval ℝ}
    {box : R → Real.Interval (Vec ℝ n)}
    {contract : Real.Interval (Vec ℝ n) → Real.Interval (Vec ℝ n)} (μ : ℕ)
    {intersect : Real.Interval (Vec ℝ n) → T} {reset : T → T} {unify : List T → T}
    (hbound : ∀ Rj, Real.IsRangeBound g (den Rj) (bound Rj).inf (bound Rj).sup)
    (hbox : ∀ Rj, den Rj ⊆ (box Rj).construct) (hcontract : Real.IsContractor g contract)
    (hintersect : ∀ I : Real.Interval (Vec ℝ n),
      I.construct ∩ {x | g x = 0} ⊆ denT (intersect I))
    (hreset : ∀ F, r '' denT F ⊆ denT (reset F))
    (hunify : ∀ L, ∀ F ∈ L, denT F ⊆ denT (unify L))
    {Rs : List R} {Rj : R} (hRj : Rj ∈ Rs) {x : Vec ℝ n} (hx : x ∈ den Rj)
    (hg : g x = 0) : -- --- CONCL ---
    r x ∈ denT (Location.guardTransitionLevelSet bound box contract μ intersect reset
      unify Rs) := by -- --- PROOF ---
  -- Step 1 keeps `R(τⱼ)`: `0 = g(x)` lies in its bound
  have hhit : Rj ∈ Rs.filter fun Rj => (bound Rj).inf ≤ 0 ∧ 0 ≤ (bound Rj).sup := by
    have h := hbound Rj x hx
    rw [hg] at h
    exact List.mem_filter.mpr ⟨hRj, by simpa using h⟩
  -- Step 2-3: its box is in some run, whose united contracted box holds `x`
  obtain ⟨c, hc, hxc⟩ := exists_mem_chunks μ _ (List.mem_map_of_mem (f := box) hhit)
  have hxI : x ∈ (Location.guardIntersectLevelSet contract c.1 c.2).construct ∩ {x | g x = 0} :=
    Location.guardIntersectLevelSet_outer hcontract
      ⟨box Rj, by rcases hxc with h | h <;> simp [h], hbox Rj hx⟩ hg
  -- Steps 4-6: the operators' guarantees, chained
  refine hunify _ (reset (intersect (Location.guardIntersectLevelSet contract c.1 c.2))) ?_
    (hreset _ ⟨x, hintersect _ hxI, rfl⟩)
  exact List.mem_map_of_mem (List.mem_map_of_mem (List.mem_map_of_mem hc))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
