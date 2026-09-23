import CORALean.ContDynamics.LinearSysDT.ReachErrorFloat
import CORALean.ContDynamics.LinearSysDT.ReachSet
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachFloatZeroMemError
import CORALean.ContSet.Zonotope.Float.Theorems.MtimesSubsetAddBox
import CORALean.ContSet.Zonotope.Float.Theorems.PlusSubsetAddBox
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceSubsetAddBox
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact

/-!
# A float run reaches no further than the exact set plus its own error

The float counterpart of `reach_subset_reachSet_add_error`. The induction is
the same shape, run against three growth bounds instead of one:
`mtimes_subset_add_box`, `plus_subset_add_box` and `reduce_subset_add_box`
each peel a box off a float operation, in the order `reach`'s own step applies
them, and what is left after peeling all three is exactly the previous step's
construct carried through `A`, plus `U`'s — which the induction hypothesis and
`reachSet`'s own recursion close.

`reachFloat_zero_mem_error` supplies what `mtimes_subset_add_box` and
`plus_subset_add_box` ask beyond `reduce_subset_add_box`: that the operands'
error boxes bracket `0`, carried from `hR₀` and `hU` by induction.

At `k = 0` the run is `R₀` itself and `reachErrorFloat 0` matches it exactly.
Each box's own `construct` is computed in `𝕋` now, so it reaches
`reachErrorFloat`'s real accumulator through one more `⊆` step, the two
`aux_` lemmas below.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float
open Matrix Pointwise ContSet InflatedContSet FloatOps SoundFloatArithmetic

variable {n : ℕ} {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A float box's own `construct` sits inside its nominal reading as a
zonotope, by `Interval.zonotope_contains`. What `plusBox` and `mtimesBox`
need to feed `reachErrorFloat`'s real accumulator. -/
theorem aux_interval_construct_subset_nominal_zonotope {n : ℕ} (I : Interval 𝕋 n) :
    I.construct ⊆ I.nominal.zonotope.construct :=
  Real.Interval.zonotope_contains I.nominal

/-- `y` in the degenerate `0` box's construct is `0`. -/
theorem aux_mem_zeroInterval_eq_zero {n : ℕ} {y : Vec ℝ n}
    (hy : y ∈ (⟨fun _ => (zero : 𝕋), fun _ => (zero : 𝕋)⟩ : Interval 𝕋 n).construct) :
    y = 0 := by -- --- PROOF ---
  funext i
  have h1 : toReal (zero : 𝕋) ≤ y i := (hy i).1
  have h2 : y i ≤ toReal (zero : 𝕋) := (hy i).2
  rw [toReal_zero] at h1 h2
  exact le_antisymm h2 h1

/-- `reduceGirardBox`'s own error box is the degenerate `0` one in either
branch, so what its `construct` adds beyond its nominal reading is `0`. -/
theorem aux_reduceGirardBox_construct_subset_nominal (Z : Zonotope 𝕋 n) (o : ℕ) :
    (Zonotope.reduceGirardBox Z o).construct
      ⊆ (nominal (Zonotope.reduceGirardBox Z o)).construct := by -- --- PROOF ---
  rintro _ ⟨y₁, hy₁, y₂, hy₂, rfl⟩
  have hy₂0 : y₂ = 0 := by
    unfold Zonotope.reduceGirardBox at hy₂
    split_ifs at hy₂ with hlt
    · exact aux_mem_zeroInterval_eq_zero hy₂
    · exact aux_mem_zeroInterval_eq_zero hy₂
  subst hy₂0
  show y₁ + (0 : Vec ℝ n) ∈ (nominal (Zonotope.reduceGirardBox Z o)).construct
  rw [add_zero]
  exact hy₁


-- =======================================  MAIN THEOREM  ======================================= --

/-- What a float run computes stays inside the exact reachable set — read from
the nominal parts of `R₀` and `U` — widened by the error that run accumulated,
provided both `R₀` and `U` bracket `0` in their own error boxes. -/
theorem LinearSysDT.reach_float_subset_reachSet_add_error (sys : LinearSysDT 𝕋 n) {o : ℕ}
    (ho : 0 < o) {R₀ U : Zonotope 𝕋 n} (hR₀ : (0 : Vec ℝ n) ∈ R₀.E.construct)
    (hU : (0 : Vec ℝ n) ∈ U.E.construct) (k : ℕ) :
    (sys.reach (S := Zonotope 𝕋) o ho R₀ U k).construct ⊆
      sys.reachSet (S := fun n => Real.Zonotope (Vec ℝ n)) (nominal R₀) (nominal U) k
        + (sys.reachErrorFloat o ho R₀ U k).construct := by -- --- PROOF ---
  induction k with
  | zero =>
    intro x hx
    obtain ⟨n₀, hn₀, e₀, he₀, rfl⟩ := hx
    exact ⟨n₀, hn₀, e₀, Real.Interval.zonotope_contains _ he₀, rfl⟩
  | succ k ih =>
    set Rk := sys.reach (S := Zonotope 𝕋) o ho R₀ U k with hRkdef
    set M := Zonotope.mtimes sys.A Rk with hMdef
    set W := M.plus U with hWdef
    -- `reach`'s step, past the `Plus`/`Mtimes`/`Reduce` instances' own `materialise`
    have hstep : sys.reach (S := Zonotope 𝕋) o ho R₀ U (k + 1) = W.reduceGirard o := by
      show Reduce.reduce (Plus.plus (Mtimes.mtimes sys.A Rk) U) o = _
      simp only [Mtimes.mtimes, Plus.plus, Reduce.reduce, Zonotope.materialise_eq,
        Zonotope.reduce, hMdef, hWdef]
    -- what `plus_subset_add_box` and `mtimes_subset_add_box` ask beyond `reduce_subset_add_box`
    have hRk0 : (0 : Vec ℝ n) ∈ Rk.E.construct :=
      sys.reachFloat_zero_mem_error ho hR₀ hU k
    have hM0 : (0 : Vec ℝ n) ∈ M.E.construct := Zonotope.zero_mem_mtimes_error hRk0
    intro x hx
    rw [hstep] at hx
    -- peel the three boxes off, in the order `reach`'s step applies the operations
    obtain ⟨w, hw, g₁, hg₁, rfl⟩ := Zonotope.reduce_subset_add_box W o hx
    obtain ⟨mu, hmu, g₂, hg₂, rfl⟩ := Zonotope.plus_subset_add_box M U hM0 hU hw
    obtain ⟨m, hm, u, hu, rfl⟩ := hmu
    obtain ⟨am, ham, g₃, hg₃, rfl⟩ := Zonotope.mtimes_subset_add_box sys.A Rk hRk0 hm
    -- what is left is `Rk`'s own point, carried through `A`, plus `U`'s point
    obtain ⟨z, hz, rfl⟩ := ham
    -- the induction hypothesis splits that point into the exact set and `Rk`'s error
    obtain ⟨s, hs, e, he, rfl⟩ := ih hz
    -- and `U`'s float point splits into its nominal part and its own error box
    obtain ⟨nu, hnu, eu, heu, rfl⟩ := hu
    -- `mtimes` is exact at `Real`, so the carried error rides through `A` for free
    have hemem : toRealMat sys.A *ᵥ e ∈ (Real.Zonotope.mtimes (toRealMat sys.A)
        (sys.reachErrorFloat o ho R₀ U k)).construct :=
      (Real.Zonotope.mtimes_exact (toRealMat sys.A) (sys.reachErrorFloat o ho R₀ U k)) ▸
        ⟨e, he, rfl⟩
    -- the exact part reassembles into `reachSet`'s own step
    have hA : toRealMat sys.A *ᵥ s + nu
        ∈ sys.reachSet (S := fun n => Real.Zonotope (Vec ℝ n)) (nominal R₀) (nominal U) (k + 1) :=
      ⟨_, ⟨s, hs, rfl⟩, nu, hnu, rfl⟩
    -- `plus` is exact at `Real`, so membership in a sum of constructs lifts to `.plus`
    have plusMem : ∀ (A B : Real.Zonotope (Vec ℝ n)) {a b : Vec ℝ n},
        a ∈ A.construct → b ∈ B.construct → a + b ∈ (A.plus B).construct :=
      fun A B _ _ ha hb => (Real.Zonotope.plus_exact A B) ▸ Set.add_mem_add ha hb
    -- the four boxes and the carried error, each read into a real zonotope, assemble
    have hEmem : toRealMat sys.A *ᵥ e + (g₃ + (g₂ + (g₁ + eu)))
        ∈ (sys.reachErrorFloat o ho R₀ U (k + 1)).construct :=
      plusMem _ _ hemem (plusMem _ _ (aux_interval_construct_subset_nominal_zonotope _ hg₃)
        (plusMem _ _ (aux_interval_construct_subset_nominal_zonotope _ hg₂)
          (plusMem _ _ (aux_reduceGirardBox_construct_subset_nominal W o hg₁)
            (Real.Interval.zonotope_contains _ heu))))
    refine ⟨_, hA, toRealMat sys.A *ᵥ e + (g₃ + (g₂ + (g₁ + eu))), hEmem, ?_⟩
    -- what remains is bookkeeping: `A` distributes and the terms regroup
    simp only [Matrix.mulVec_add]
    abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
