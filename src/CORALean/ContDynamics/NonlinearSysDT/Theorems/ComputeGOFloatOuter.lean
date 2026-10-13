import CORALean.ContDynamics.NonlinearSysDT.Operations.ComputeGO
import CORALean.ContDynamics.NonlinearSysDT.Operations.ComputeGOFloat
import CORALean.ContSet.Interval.Float.Theorems.DescProdOuter
import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
import CORALean.ContSet.Interval.Float.Theorems.MemPoint

/-!
# The float GO parameters enclose the real ones

For float models `fm` of the field and `om` of the output equation that enclose them with their
Jacobians, everything `computeGO` returns from the real value of a float start under the real
value of a float reference input lies in what `computeGOFloat` returns: the reference run `x`,
`y` and the parameters `A{k}`, `B{k,j}`, `F{k,j}`, `C{k}`, `D{k,j}`, `E{k,j}`. An outer statement;
with `computeGO_state` and `computeGO_output` it encloses the deviation of every run, the
linearization errors `L_j` aside.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearSysDT.computeGOFloat_outer (sys : NonlinearSysDT n m)
    (out : Vec ℝ n → Vec ℝ m → Vec ℝ r) {fm : NonlinearSysDT.FloatJacModel 𝕋 n m n}
    (hf : fm.Encloses sys.f) {om : NonlinearSysDT.FloatJacModel 𝕋 n m r} (ho : om.Encloses out)
    (x0 : Vec 𝕋 n) (u_ref : ℕ → Vec 𝕋 m) (k j : ℕ) :
    let G := sys.computeGO out (toRealVec x0) (fun i => toRealVec (u_ref i))
    let F := NonlinearSysDT.computeGOFloat fm om x0 u_ref
    G.x k ∈ (F.x k).construct ∧ G.y k ∈ (F.y k).construct ∧ G.A k ∈ (F.A k).construct ∧
      G.B k j ∈ (F.B k j).construct ∧ G.F k j ∈ (F.F k j).construct ∧
      G.C k ∈ (F.C k).construct ∧ G.D k j ∈ (F.D k j).construct ∧
      G.E k j ∈ (F.E k j).construct := by -- --- PROOF ---
  intro G F
  -- a stored zero matrix reads as the zero matrix
  have hz : ∀ {a b : ℕ}, (0 : Mat ℝ a b) ∈
      (Interval.point (show Mat 𝕋 a b from fun _ _ => zero)).construct := fun {a b} => by
    have h : toRealMat (show Mat 𝕋 a b from fun _ _ => zero) = 0 := by
      funext i l
      simp [toRealMat, toReal_zero]
    rw [← h]
    exact Interval.mem_point _
  -- the stored selection matrices read as `stackFst` and `stackSnd`
  have hIx : stackFst n r ∈ (Interval.point (show Mat 𝕋 n (n + r) from fun i l =>
      if l.val = i.val then (one : 𝕋) else zero)).construct := by
    have h : toRealMat (show Mat 𝕋 n (n + r) from fun i l =>
        if l.val = i.val then (one : 𝕋) else zero) = stackFst n r := by
      funext i l
      simp only [toRealMat, stackFst, Matrix.of_apply]
      split_ifs <;> simp [toReal_one, toReal_zero]
    rw [← h]
    exact Interval.mem_point _
  have hIy : stackSnd n r ∈ (Interval.point (show Mat 𝕋 r (n + r) from fun i l =>
      if l.val = n + i.val then (one : 𝕋) else zero)).construct := by
    have h : toRealMat (show Mat 𝕋 r (n + r) from fun i l =>
        if l.val = n + i.val then (one : 𝕋) else zero) = stackSnd n r := by
      funext i l
      simp only [toRealMat, stackSnd, Matrix.of_apply]
      split_ifs <;> simp [toReal_one, toReal_zero]
    rw [← h]
    exact Interval.mem_point _
  -- the reference run lies in the boxes, the reference input in its point boxes
  have hu : ∀ i, toRealVec (u_ref i) ∈ (Interval.point (u_ref i)).construct :=
    fun i => Interval.mem_point (u_ref i)
  have hx : ∀ i, sys.refState (toRealVec x0) (fun i => toRealVec (u_ref i)) i ∈
      (NonlinearSysDT.simulateBoxFloat ⟨fm.f⟩ x0 u_ref i).construct := fun i => by
    induction i with
    | zero => exact Interval.mem_point x0
    | succ i ih => exact hf.f_mem _ _ _ ih _ (hu i)
  -- the Jacobians at the reference run lie in the models' interval matrices
  have hA : ∀ i, jacobianMat (fun x => sys.f x (toRealVec (u_ref i)))
      (sys.refState (toRealVec x0) (fun i => toRealVec (u_ref i)) i) ∈
      (fm.jacX (NonlinearSysDT.simulateBoxFloat ⟨fm.f⟩ x0 u_ref i)
        (Interval.point (u_ref i))).construct :=
    fun i => hf.jacX_mem _ _ _ (hx i) _ (hu i)
  have hB : ∀ i, jacobianMat (fun u => sys.f
      (sys.refState (toRealVec x0) (fun i => toRealVec (u_ref i)) i) u) (toRealVec (u_ref i)) ∈
      (fm.jacU (NonlinearSysDT.simulateBoxFloat ⟨fm.f⟩ x0 u_ref i)
        (Interval.point (u_ref i))).construct :=
    fun i => hf.jacU_mem _ _ _ (hx i) _ (hu i)
  -- and those of the output equation in its model's
  have hC : ∀ i, jacobianMat (fun x => out x (toRealVec (u_ref i)))
      (sys.refState (toRealVec x0) (fun i => toRealVec (u_ref i)) i) ∈
      (om.jacX (NonlinearSysDT.simulateBoxFloat ⟨fm.f⟩ x0 u_ref i)
        (Interval.point (u_ref i))).construct :=
    fun i => ho.jacX_mem _ _ _ (hx i) _ (hu i)
  have hD : ∀ i, jacobianMat (fun u => out
      (sys.refState (toRealVec x0) (fun i => toRealVec (u_ref i)) i) u) (toRealVec (u_ref i)) ∈
      (om.jacU (NonlinearSysDT.simulateBoxFloat ⟨fm.f⟩ x0 u_ref i)
        (Interval.point (u_ref i))).construct :=
    fun i => ho.jacU_mem _ _ _ (hx i) _ (hu i)
  -- so do their products, and every parameter is a product of these
  have hP := Interval.descProd_outer _ hA
  simp only [G, F, NonlinearSysDT.computeGO, NonlinearSysDT.computeGOFloat]
  refine ⟨hx k, ho.f_mem _ _ _ (hx k) _ (hu k), Interval.matMul_outer _ _ (hA k) (hP _ _),
    ?_, ?_, Interval.matMul_outer _ _ (hC k) (hP _ _), ?_, ?_⟩
  · -- `B{k,j}`: the product times `B_lin j` up to the diagonal, zero beyond
    split_ifs
    · exact Interval.matMul_outer _ _ (hP _ _) (hB j)
    · exact hz
  · -- `F{k,j}`: the product times the selection of `L_x`
    split_ifs
    · exact Interval.matMul_outer _ _ (hP _ _) hIx
    · exact hz
  · -- `D{k,j}`: `C_lin k` times the product times `B_lin j` below, `D_lin k` on the diagonal
    split_ifs
    · exact Interval.matMul_outer _ _ (Interval.matMul_outer _ _ (hC k) (hP _ _)) (hB j)
    · subst_vars
      exact hD _
    · exact hz
  · -- `E{k,j}`: the same with the selections of `L_x` and `L_y`
    split_ifs
    · exact Interval.matMul_outer _ _ (Interval.matMul_outer _ _ (hC k) (hP _ _)) hIx
    · exact hIy
    · exact hz

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
