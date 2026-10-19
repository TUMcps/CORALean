module

public import CORALean.ContDynamics.LinearSysDT.Operations.ObserveStep
public import CORALean.ContSet.ContSet.Theorems.IntersectStripSeqOuter

@[expose] public section

/-!
# One observer step encloses the states the measurement allows

[1, Alg. 1]: if `X̂` holds every state `X` might be in, the step's result holds every
`A x + u + ω` with `x ∈ X`, `ω ∈ W`, that lies in the measurement strips. The prediction
is outer by `mtimes_outer` and `plus_outer` ([1, Eq. 2]; exact at `Real.Zonotope`), the update
by `intersectStripSeq_outer`, [1, Eq. 3], or `intersectStrip_outer` all at once, for every gain.
One statement for every representation and scalar: at a float type the matrices, inputs and
strips are the reals the floats store.

[2, Eq. 4]: the correction keeps `S_p ∩ Ŝ`.

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 49(11):3418-3424, 2013.
* [2] M. Althoff. "Guaranteed State Estimation in CORA 2021". In Proc. of the 8th
      International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH21),
      EPiC Series in Computing, vol. 80, pp. 161-175, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       13-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise ContSet Scalar Plus Mtimes IntersectStrip

variable {𝕋 : Type} [Scalar 𝕋] {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] [OfScalarPoint 𝕋 S]
variable [IntersectStrip 𝕋 S] {n p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.observeStep_outer (sys : LinearSysDT 𝕋 n) (σ : Vec 𝕋 sys.q)
    (W : S n) (options : LinearSysDT.ObserveStripOptions 𝕋 (S n) n sys.q) (u : Vec 𝕋 sys.m)
    (y : Vec 𝕋 sys.q) (Xhat : S n) {X : Set (Vec ℝ n)} (hX : X ⊆ construct Xhat) : -- --- CONCL ---
    ((fun x => toRealMat sys.A *ᵥ x + toRealMat sys.B *ᵥ toRealVec u + toRealVec sys.c) '' X +
        construct W) ∩
        {x | ∀ i, |(toRealMat sys.C *ᵥ x - toRealVec y) i| ≤ toReal (σ i)} ⊆
      construct (sys.observeStep σ W options u y Xhat) := by -- --- PROOF ---
  -- the prediction holds every predicted state
  have hpred : (fun x => toRealMat sys.A *ᵥ x + toRealMat sys.B *ᵥ toRealVec u + toRealVec sys.c) ''
      X + construct W ⊆
      construct (plus (plus (plus (mtimes sys.A Xhat) (mtimes sys.B (OfScalarPoint.ofVec u)))
        (OfScalarPoint.ofVec sys.c)) W) := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, w, hw, rfl⟩
    have hA : toRealMat sys.A *ᵥ x ∈ construct (mtimes sys.A Xhat) :=
      mtimes_outer sys.A Xhat (Set.mem_biUnion (Set.mem_singleton _) ⟨x, hX hx, rfl⟩)
    have hB : toRealMat sys.B *ᵥ toRealVec u ∈
        construct (mtimes sys.B (OfScalarPoint.ofVec (S := S) u)) :=
      mtimes_outer sys.B _ (Set.mem_biUnion (Set.mem_singleton _)
        ⟨_, OfScalarPoint.mem_ofVec u, rfl⟩)
    exact plus_outer _ _ ⟨_, plus_outer _ _ ⟨_, plus_outer _ _ ⟨_, hA, _, hB, rfl⟩, _,
      OfScalarPoint.mem_ofVec sys.c, rfl⟩, w, hw, rfl⟩
  intro x hx
  unfold LinearSysDT.observeStep
  split
  · exact intersectStripSeq_outer _ _ _ _ _ ⟨hpred hx.1, hx.2⟩
  · exact intersectStrip_outer _ _ _ _ _ ⟨hpred hx.1, hx.2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
