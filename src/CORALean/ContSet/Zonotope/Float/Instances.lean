module

public import CORALean.ContSet.ContSet.Definitions.CompactSet
public import CORALean.ContSet.ContSet.Definitions.ConvexSet
public import CORALean.ContSet.Interval.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Operations.Materialise
public import CORALean.ContSet.Zonotope.Float.Theorems.Basic
public import CORALean.ContSet.Zonotope.Float.Theorems.ConstructPoint
public import CORALean.ContSet.Zonotope.Float.Theorems.Convex
public import CORALean.ContSet.Zonotope.Float.Theorems.IntersectStripOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.IsClosed
public import CORALean.ContSet.Zonotope.Float.Theorems.LinCombOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.MemPointMat
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesMatZonotopeOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.RecenterSubMem
public import CORALean.ContSet.Zonotope.Float.Theorems.RecenterZeroMem
public import CORALean.ContSet.Zonotope.Float.Theorems.ReduceOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.ReindexExact
public import CORALean.Global.Float.NoNaN

@[expose] public section

/-!
# What `Zonotope` instantiates

`ContSet` is supplied by `InflatedContSet`, so an algorithm written against the three operation
classes runs here with no float counterpart to write. A zonotope's four fields are function types,
so the one an operation returns is a closure over the one it was given: a loop that iterates
operations rebuilds its whole history on every entry read. `Zonotope.materialise` stores them, and
`materialise_eq` says it is the identity, so each proof below is the operation's own guarantee after
one rewrite. It goes here rather than in `Operations/`: an algorithm reaches a representation
through the operation fields below and nothing else, so this knows a set is about to be handed back
to a loop.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       18-August-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- The zonotope family over vectors.
The scalar is an argument: a notation cannot capture the section
variable `𝕋`, so `(S := 𝒵[𝕋])`. -/
scoped notation "𝒵[" t "]" => fun n => Zonotope (Vec t n)

/-- The matrix-zonotope family.
The scalar is an argument: a notation cannot capture the section
variable `𝕋`, so `(S := 𝕄𝒵[𝕋])`. -/
scoped notation "𝕄𝒵[" t "]" => fun m n => Zonotope (Mat t m n)


-- ========================================  INSTANCES  ========================================= --

/-- Not the nominal zonotope's own convexity read across: the set is that one
plus the error box, and `Convex.add` is what carries the property over the sum. -/
instance {n : ℕ} : ConvexSet (Zonotope (Vec 𝕋 n)) (Vec ℝ n) := ⟨Zonotope.convex_construct⟩

/-- Compactness, not the closed-and-bounded pair, for the exact layer's reason;
it survives the box because a sum of two compact sets is compact. -/
instance {n : ℕ} : CompactSet (Zonotope (Vec 𝕋 n)) (Vec ℝ n) := ⟨Zonotope.isCompact_construct⟩

instance {n : ℕ} : Plus (Zonotope (Vec 𝕋 n)) (Vec ℝ n) where
  plus Z₁ Z₂ := (Z₁.plus Z₂).materialise
  plus_outer Z₁ Z₂ := by
    rw [Zonotope.materialise_eq]
    exact Zonotope.plus_outer Z₁ Z₂

instance {n : ℕ} : LinComb (Zonotope (Vec 𝕋 n)) (Vec ℝ n) where
  linComb Z₁ Z₂ := (Z₁.linComb Z₂).materialise
  linComb_outer Z₁ Z₂ := by
    rw [Zonotope.materialise_eq]
    exact Zonotope.linComb_outer Z₁ Z₂

instance {n : ℕ} : Reduce (Zonotope (Vec 𝕋 n)) (Vec ℝ n) where
  reduce Z o := (Z.reduce o).materialise
  reduce_outer Z o := by
    rw [Zonotope.materialise_eq]
    exact Zonotope.reduce_outer Z o

/-- `center` is the stored center read as reals: a field projection, and
exactly the point `recenter` takes out, so nothing rounds. -/
instance {n : ℕ} : Recenter (Zonotope (Vec 𝕋 n)) (Vec ℝ n) where
  center Z := toRealVec Z.c
  recenter := Zonotope.recenter
  zero_mem_recenter := Zonotope.zero_mem_recenter
  sub_center_mem_recenter := Zonotope.sub_center_mem_recenter

/-- The point zonotope: no generators and the origin error box, exactly the stored point. -/
instance : OfScalarPoint 𝕋 𝒵[𝕋] where
  ofVec v := Zonotope.point v
  mem_ofVec v := by
    have h := Zonotope.construct_point v
    show toRealVec v ∈ (Zonotope.point v).construct
    rw [h]
    exact Set.mem_singleton _

omit [SoundFloatArithmetic 𝕋] in
/-- The stored identity block as a point matrix zonotope. -/
instance : OfIdentity 𝕄𝒵[𝕋] where
  identity n := Zonotope.pointMat (diagonalBlock fun _ : Fin n => (FloatOps.one : 𝕋))

open FloatOps SoundFloatArithmetic in
/-- The stored identity block reads back as the real `1`. -/
instance : IdentityMem 𝕄𝒵[𝕋] where
  one_mem_identity n := by
    have h : toRealMat (diagonalBlock fun _ : Fin n => (one : 𝕋)) = (1 : Mat ℝ n n) := by
      funext i j
      rw [toRealMat, toReal_diagonalBlock]
      simp [toRealVec, toReal_one, Matrix.one_apply, Matrix.diagonal_apply]
    rw [← h]
    exact Zonotope.mem_pointMat (diagonalBlock fun _ : Fin n => (one : 𝕋))

/-- The stored center. -/
instance : ScalarCenter 𝕋 𝒵[𝕋] where
  centerVec Z := Z.c

/-- Exact, alone among the fields here: a relabelling moves stored floats and
computes nothing, so the error box is carried across rather than grown. -/
instance : Reindex 𝒵[𝕋] where
  reindex e Z := (Zonotope.reindex e Z).materialise
  reindex_exact e Z := by
    rw [Zonotope.materialise_eq]
    exact Zonotope.reindex_exact e Z

instance : Mtimes (Mat 𝕋) 𝒵[𝕋] where
  mtimes M Z := (Zonotope.mtimes M Z).materialise
  mtimes_outer M Z := by
    simp only [ContSet.construct_mat, Set.biUnion_singleton, Zonotope.materialise_eq]
    exact Zonotope.mtimes_outer M Z

/-- The rounded update, with `I - Λ C` an interval matrix; the guarantee reads the strips at the
reals they store. -/
instance : IntersectStrip 𝕋 𝒵[𝕋] where
  intersectStrip C φ y Λ Z := (Zonotope.intersectStrip C φ y Λ Z).materialise
  intersectStrip_outer C φ y Λ Z := by
    rw [Zonotope.materialise_eq]
    exact Zonotope.intersectStrip_outer C φ y Λ Z

/-- The same operation at a float interval matrix, which the float
`expIntervalEnclosure` chain builds towards, exactly as `Real`'s `Mtimes ℐ 𝒵`
does at the exact layer. -/
instance : Mtimes ℐ[𝕋] 𝒵[𝕋] where
  mtimes IM Z := (Zonotope.mtimesIntervalMat IM Z).materialise
  mtimes_outer IM Z := by
    rw [Zonotope.materialise_eq]
    exact Zonotope.mtimesIntervalMat_outer IM Z

/-- The same operation at a float matrix zonotope, what a `LinParamSys` or `LinParamSysDT`
over `Zonotope (Mat 𝕋 m n)` multiplies a reachable set by, as `Real`'s `Mtimes 𝕄𝒵 𝒵` does. -/
instance : Mtimes 𝕄𝒵[𝕋] 𝒵[𝕋] where
  mtimes M Z := (Zonotope.mtimesMatZonotope M Z).materialise
  mtimes_outer M Z := by
    rw [Zonotope.materialise_eq]
    exact Zonotope.mtimesMatZonotope_outer M Z

/-- Center, generators and error box, for `ifNoNaN`. -/
instance {n : ℕ} : Floats 𝕋 (Zonotope (Vec 𝕋 n)) :=
  ⟨fun Z => Floats.floats Z.c ++ Floats.floats Z.G ++ Floats.floats Z.I_error⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
