module

public import CORALean.ContSet.Zonotope.Float.Theorems.ConstructPoint
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMemIff
public import CORALean.Specification.STL.Operations.DepReachInitFloat
public import CORALean.ContSet.Zonotope.Real.Theorems.CenterMemConstruct
public import CORALean.Specification.STL.Theorems.DepBoxFloatOuter

@[expose] public section

/-!
# The initial state over floats encloses the real one

Lines 2-3 of [1, Alg. 1]: `H(t₀)`, `P_c(t₀)` and `D₀` are held as the sets are. The points of `C₀`
are the products `M x + M' ũ` for `M` in `F`, `x` in `X₀` and `M'` in `G`: `mtimesIntervalMat_outer`
holds each product, `plus_outer` the sum, and the float box holds every point of the sum
(`depBoxFloat_outer` at the point zonotope of each point). The real `C₀` is not compared itself: its
conservative `mtimesIntervalMat` has a symmetric box that the rounded one need not cover.

## Inputs
* `X₀r` – real initial set
* `X₀f` – float initial set
* `csR` – real constants
* `csF` – float constants

## Hypotheses
* `hX` – the real initial set lies inside the float one
* `hcs` – the float constants enclose the real ones

## Conclusion
* the float initial state encloses the real one, with the exact products as `C₀`
## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The float `interval(Z)` holds every point of `Z`. -/
theorem STL.aux_subset_depBoxFloat (Z : Float.Zonotope (Vec 𝕋 n)) :
    Z.construct ⊆ (STL.depBoxFloat Z).construct := fun x hx =>
  STL.depBoxFloat_outer (Zr := Real.Zonotope.ofPoint x)
    (fun y hy => (Real.Zonotope.mem_ofPoint_iff x y).1 hy ▸ hx)
    (Real.Zonotope.center_mem_construct (STL.depBox (Real.Zonotope.ofPoint x)))


-- =======================================  MAIN THEOREM  ======================================= --

/-- The float state at `t₀` encloses the real one, with the exact products as the set `C₀`. -/
theorem STL.depReachInitFloat_outer {X₀r : Real.Zonotope (Vec ℝ n)} {X₀f : Float.Zonotope (Vec 𝕋 n)}
    {csR : STL.DepReachConsts n} {csF : STL.DepReachConstsFloat 𝕋 n}
    (hX : X₀r.construct ⊆ X₀f.construct) (hcs : csF.Encloses csR) : -- --- CONCL ---
    (STL.depReachInitFloat X₀f csF).Encloses (STL.depReachInit X₀r csR)
      {y | ∃ M ∈ csR.F.construct, ∃ x ∈ X₀r.construct, ∃ M' ∈ csR.G.construct,
        y = M *ᵥ x + M' *ᵥ csR.ũ} := by -- --- PROOF ---
  obtain ⟨hu, -, -, hF, hG, -⟩ := hcs
  have hzero : toRealVec (fun _ : Fin n => (zero : 𝕋)) = 0 := funext fun i => toReal_zero
  refine ⟨hX, ?_, ?_, ?_⟩
  · intro x hx
    have hx : x = 0 := (Real.Zonotope.mem_ofPoint_iff _ x).1 hx
    show x ∈ (Float.Zonotope.point (fun _ : Fin n => (zero : 𝕋))).construct
    rw [Float.Zonotope.construct_point, Set.mem_singleton_iff, hx, hzero]
  · intro x hx
    have hx : x = 0 := (Real.Zonotope.mem_ofPoint_iff _ x).1 hx
    show x ∈ (Float.Zonotope.point (fun _ : Fin n => (zero : 𝕋))).construct
    rw [Float.Zonotope.construct_point, Set.mem_singleton_iff, hx, hzero]
  · rintro _ ⟨M, hM, x, hx, M', hM', rfl⟩
    refine STL.aux_subset_depBoxFloat _ (Float.Zonotope.plus_outer _ _
      (Set.add_mem_add ?_ ?_))
    · exact Float.Zonotope.mtimesIntervalMat_outer _ _
        (Set.mem_iUnion₂.2 ⟨M, hF hM, ⟨x, hX hx, rfl⟩⟩)
    · exact Float.Zonotope.mtimesIntervalMat_outer _ _
        (Set.mem_iUnion₂.2 ⟨M', hG hM', ⟨_, hu, rfl⟩⟩)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
