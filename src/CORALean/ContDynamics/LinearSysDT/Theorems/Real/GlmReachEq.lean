module

public import CORALean.ContDynamics.LinearSysDT.Definitions.ReachSetExact
public import CORALean.ContDynamics.LinearSysDT.Operations.GlmReach
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMemIff
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact

@[expose] public section

/-!
# `glmReach` returns the exact reachable sets

[1, Alg. 1]'s output line: the `i`-th set returned is `Ω_{i+1}` of the recurrence
`Ω_{i+1} = ΦΩᵢ ⊕ U`, [1, Eq. 1], which is `LinearSysDT.reachSetExact`. The invariant is the
paper's derivation from [1, Eq. 2]: `Xᵢ ⊕ Sᵢ = Ωᵢ` and `Sᵢ ⊕ Vᵢ = ΦSᵢ ⊕ U`, the second
being `S_{i+1} = Φ^iU ⊕ … ⊕ U` read one step at a time. Linear maps distribute over
Minkowski sums of arbitrary sets, so neither convexity nor boundedness of `U` is used.

## References

* [1] A. Girard, C. Le Guernic and O. Maler. "Efficient Computation of Reachable Sets of
      Linear Time-Invariant Systems with Inputs". In Hybrid Systems: Computation and
      Control (HSCC), LNCS 3927, Springer, 2006, pp. 257-271.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Pointwise Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `k` passes of a loop that steps its state by `f` and appends `g` of the new state. -/
theorem LinearSysDT.aux_glmReach_foldl {α β : Type} (f : α → α) (g : α → β) (a : α)
    (l : List β) (k : ℕ) :
    (List.range k).foldl (fun (s : α × List β) (_ : ℕ) => (f s.1, s.2 ++ [g (f s.1)])) (a, l)
      = (f^[k] a, l ++ (List.range k).map fun i => g (f^[i + 1] a)) := by -- --- PROOF ---
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp [Function.iterate_succ_apply']

/-- The loop invariant: `Xᵢ ⊕ Sᵢ = Ωᵢ` and `Sᵢ ⊕ Vᵢ = ΦSᵢ ⊕ U`. -/
theorem LinearSysDT.aux_glmReach_inv (sys : LinearSysDT 𝕋 n) (Ω₀ U : Zonotope (Vec ℝ n))
    (k : ℕ) : -- --- STMT ---
    let f := fun (s : Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n)) =>
      (s.1.mtimes (toRealMat sys.A), s.2.1.plus s.2.2, s.2.2.mtimes (toRealMat sys.A))
    let s := f^[k] (Ω₀, Zonotope.ofPoint 0, U)
    s.1.construct + s.2.1.construct = sys.reachSetExact (S := 𝒵) Ω₀ U k ∧
      s.2.1.construct + s.2.2.construct
        = mulVecLin (toRealMat sys.A) '' s.2.1.construct + U.construct := by -- --- PROOF ---
  intro f s
  set L := mulVecLin (toRealMat sys.A)
  -- a zonotope's image under `Φ` is its `mtimes`
  have hmt : ∀ Z : Zonotope (Vec ℝ n), (Z.mtimes (toRealMat sys.A)).construct = L '' Z.construct :=
    fun Z => (Zonotope.mtimes_exact _ Z).symm
  have h0 : (Zonotope.ofPoint (0 : Vec ℝ n)).construct = {0} :=
    Set.ext fun x => Zonotope.mem_ofPoint_iff 0 x
  induction k with
  | zero =>
    -- `X₀ ⊕ {0} = Ω₀` and `{0} ⊕ U = Φ{0} ⊕ U`
    simp only [s, Function.iterate_zero, id, h0, Set.image_singleton, map_zero]
    refine ⟨?_, trivial⟩
    rw [Set.singleton_zero, add_zero]
    rfl
  | succ k ih =>
    obtain ⟨ih₁, ih₂⟩ := ih
    simp only [s, Function.iterate_succ_apply', f, hmt, ← Zonotope.plus_exact] at ih₁ ih₂ ⊢
    set t := f^[k] (Ω₀, Zonotope.ofPoint 0, U)
    constructor
    · -- `ΦXᵢ ⊕ (Sᵢ ⊕ Vᵢ) = ΦXᵢ ⊕ ΦSᵢ ⊕ U = Φ(Xᵢ ⊕ Sᵢ) ⊕ U`
      show _ = L '' sys.reachSetExact (S := 𝒵) Ω₀ U k + ContSet.construct U
      rw [ih₂, ← ih₁, Set.image_add, add_assoc]
      rfl
    · -- `(Sᵢ ⊕ Vᵢ) ⊕ ΦVᵢ = ΦSᵢ ⊕ U ⊕ ΦVᵢ = Φ(Sᵢ ⊕ Vᵢ) ⊕ U`
      rw [Set.image_add, ih₂, add_right_comm]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1]: the sets returned are `Ω₁, …, Ω_N` of `Ω_{i+1} = ΦΩᵢ ⊕ U`. -/
theorem LinearSysDT.glmReach_eq (sys : LinearSysDT 𝕋 n) (Ω₀ U : Zonotope (Vec ℝ n)) (N : ℕ) :
    (sys.glmReach Ω₀ U N).map Zonotope.construct
      = (List.range N).map fun i => sys.reachSetExact (S := 𝒵) Ω₀ U (i + 1) := by -- --- PROOF ---
  -- unroll the loop, then read each set off the invariant
  have h := LinearSysDT.aux_glmReach_foldl
    (fun (s : Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n)) =>
      (s.1.mtimes (toRealMat sys.A), s.2.1.plus s.2.2, s.2.2.mtimes (toRealMat sys.A)))
    (fun s => s.1.plus s.2.1) (Ω₀, Zonotope.ofPoint 0, U) [] N
  rw [LinearSysDT.glmReach, congrArg Prod.snd h, List.nil_append, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  rw [Function.comp_apply, ← Zonotope.plus_exact]
  exact (LinearSysDT.aux_glmReach_inv sys Ω₀ U (i + 1)).1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
