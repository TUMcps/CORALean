import CORALean.Global.Entrywise

/-!
# The entrywise product, bundled as a bilinear map

`Entrywise` says which ambient types have coordinates; this is the product read
in them. Bundled as `α →ₗ[ℝ] α →ₗ[ℝ] α` rather than left as a function, because
every use is as an argument: `PolyZonotope.bilin` propagates *any* bilinear map
through two sets sharing their factors, and the entrywise product is the one
that gives a polynomial abstraction its order-`n` term.

Stated over the class and not over `Vec`, so that `Mat ℝ n m` gets it too. That
matters: `Mat`'s own `*` is matrix multiplication, so a matrix polynomial
zonotope has no entrywise product to inherit and would otherwise need one
written by hand — which is exactly what a graph convolutional network needs for
`P_ij = Ã_ij ⬝ s_i ⬝ s_j`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]

/-- The product taken coordinate by coordinate. -/
def Entrywise.hadamard (a b : α) : α :=
  Entrywise.ofEntry fun i => Entrywise.entry a i * Entrywise.entry b i

@[simp] theorem Entrywise.entry_hadamard (a b : α) (i : ι) :
    Entrywise.entry (Entrywise.hadamard a b) i
      = Entrywise.entry a i * Entrywise.entry b i :=
  Entrywise.entry_ofEntry _ i

/-- The product in its second argument, which is the inner half of the bundle. -/
def Entrywise.hadamardRight (a : α) : α →ₗ[ℝ] α where
  toFun b := Entrywise.hadamard a b
  map_add' b c := Entrywise.ext fun i => by
    simp only [Entrywise.entry_hadamard, Entrywise.entry_add]
    ring
  map_smul' c b := Entrywise.ext fun i => by
    simp only [Entrywise.entry_hadamard, Entrywise.entry_smul, RingHom.id_apply]
    ring

@[simp] theorem Entrywise.hadamardRight_apply (a b : α) :
    Entrywise.hadamardRight a b = Entrywise.hadamard a b := rfl


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The entrywise product, bilinear because a coordinate of it is a product of
two coordinates and multiplication in `ℝ` is. -/
def Entrywise.hadamardLin : α →ₗ[ℝ] α →ₗ[ℝ] α where
  toFun := Entrywise.hadamardRight
  map_add' a b := LinearMap.ext fun c => Entrywise.ext fun i => by
    simp only [LinearMap.add_apply, Entrywise.hadamardRight_apply, Entrywise.entry_hadamard,
      Entrywise.entry_add]
    ring
  map_smul' r a := LinearMap.ext fun c => Entrywise.ext fun i => by
    simp only [RingHom.id_apply, LinearMap.smul_apply, Entrywise.hadamardRight_apply,
      Entrywise.entry_hadamard, Entrywise.entry_smul]
    ring

@[simp] theorem Entrywise.hadamardLin_apply (a b : α) :
    (Entrywise.hadamardLin a) b = Entrywise.hadamard a b := rfl

/-- At `Vec`, where a coordinate is an application, it is the `Pi` product the
library already writes as `*`. -/
theorem Entrywise.hadamardLin_vec {n : ℕ} (a b : Vec ℝ n) :
    (Entrywise.hadamardLin a) b = a * b := rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
