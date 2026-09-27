import MatrixSpencer.KSObjectiveChart
import MatrixSpencer.SuperoperatorCoordinates
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Full Hermitian coordinates with Frobenius geometry

The first chart is explicit vectorization into the real subspace of complex
Euclidean coordinates representing Hermitian matrices. It is bijective onto
all physical Hermitian matrices and has exactly the real trace pairing.
An orthonormal basis then gives a finite real Euclidean coordinate chart.
Continuity into the physical operator norm follows from finite dimension;
the physical matrix norm is not replaced by a Frobenius norm.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace MatrixSpencer.KSFullHermitianChart

variable (n : Type*) [Fintype n] [DecidableEq n]

local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance : InnerProductSpace ℝ (EuclideanSpace ℂ (n × n)) :=
  PiLp.innerProductSpace (fun _ : n × n => ℂ)

/-- The full real Hermitian subspace in explicit complex Frobenius coordinates. -/
def hermitianCoordinates : Submodule ℝ (EuclideanSpace ℂ (n × n)) where
  carrier := {x | (matrixUnvector (WithLp.ofLp x)).IsHermitian}
  zero_mem' := Matrix.isHermitian_zero
  add_mem' hx hy := hx.add hy
  smul_mem' r x hx := by
    change (r • matrixUnvector (WithLp.ofLp x)).IsHermitian
    change (r • matrixUnvector (WithLp.ofLp x))ᴴ = _
    simp only [Matrix.conjTranspose_smul, star_trivial, hx.eq]

abbrev Frobenius := ↥(hermitianCoordinates n)

/-- Vectorization and unvectorization give an actual linear bijection, before
choosing any orthonormal basis. -/
def physicalLinearEquiv : Frobenius n ≃ₗ[ℝ] selfAdjoint (Matrix n n ℂ) where
  toFun x := ⟨matrixUnvector (WithLp.ofLp x.val), x.property⟩
  invFun X := ⟨WithLp.toLp 2 (matrixVector (X : Matrix n n ℂ)), X.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The physical codomain retains the operator-norm topology. -/
def physicalEquiv : Frobenius n ≃L[ℝ] selfAdjoint (Matrix n n ℂ) :=
  (physicalLinearEquiv n).toContinuousLinearEquiv

@[simp] theorem physicalEquiv_apply (x : Frobenius n) :
    (physicalEquiv n x : Matrix n n ℂ) = matrixUnvector (WithLp.ofLp x.val) := rfl

theorem physicalEquiv_surjective : Function.Surjective (physicalEquiv n) :=
  (physicalEquiv n).surjective

/-- Squared Frobenius length is exactly the real trace of the physical square. -/
theorem physicalEquiv_trace_square (x : Frobenius n) :
    realTrace ((physicalEquiv n x : Matrix n n ℂ) *
      (physicalEquiv n x : Matrix n n ℂ)) = ‖x‖ ^ 2 := by
  let X : Matrix n n ℂ := physicalEquiv n x
  have hX : X.IsHermitian := (physicalEquiv n x).property
  change realTrace (X * X) = ‖x‖ ^ 2
  have ht : realTrace (X * X) = realTrace (Xᴴ * X) := by rw [hX.eq]
  rw [ht, ← entryEnergy_eq_realTrace_adjoint_mul, ← matrixVector_energy]
  rw [Submodule.coe_norm, EuclideanSpace.norm_sq_eq]
  simp only [Complex.normSq_eq_norm_sq]
  rfl

/-- The full bilinear trace identity, obtained from the squared-norm identity. -/
theorem physicalEquiv_trace_pairing (x y : Frobenius n) :
    realTrace ((physicalEquiv n x : Matrix n n ℂ) *
      (physicalEquiv n y : Matrix n n ℂ)) = inner ℝ x y := by
  have hxy := physicalEquiv_trace_square n (x + y)
  have hx := physicalEquiv_trace_square n x
  have hy := physicalEquiv_trace_square n y
  have he : (physicalEquiv n (x + y) : Matrix n n ℂ) =
      (physicalEquiv n x : Matrix n n ℂ) + (physicalEquiv n y : Matrix n n ℂ) := rfl
  rw [he, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, realTrace_add,
    realTrace_add, realTrace_add, realTrace_mul_comm (physicalEquiv n y : Matrix n n ℂ)
      (physicalEquiv n x : Matrix n n ℂ), norm_add_sq_real] at hxy
  linarith

abbrev Index := Fin (Module.finrank ℝ (Frobenius n))
abbrev Coordinates := EuclideanSpace ℝ (Index n)

/-- An orthonormal real basis of the full Frobenius Hermitian space. The
analytic basis choice is separate from numerical coordinate reports. -/
def basis : OrthonormalBasis (Index n) ℝ (Frobenius n) :=
  stdOrthonormalBasis ℝ (Frobenius n)

/-- Onto real Euclidean coordinates for every physical Hermitian matrix. -/
def chartEquiv : Coordinates n ≃L[ℝ] selfAdjoint (Matrix n n ℂ) :=
  (basis n).repr.symm.toContinuousLinearEquiv.trans (physicalEquiv n)

def chart : Coordinates n →L[ℝ] selfAdjoint (Matrix n n ℂ) :=
  (chartEquiv n).toContinuousLinearMap

theorem chart_surjective : Function.Surjective (chart n) :=
  (chartEquiv n).surjective

theorem chart_injective : Function.Injective (chart n) :=
  (chartEquiv n).injective

theorem chart_trace_square (x : Coordinates n) :
    realTrace ((chart n x : Matrix n n ℂ) * (chart n x : Matrix n n ℂ)) = ‖x‖ ^ 2 := by
  change realTrace ((physicalEquiv n ((basis n).repr.symm x) : Matrix n n ℂ) *
    (physicalEquiv n ((basis n).repr.symm x) : Matrix n n ℂ)) = _
  rw [physicalEquiv_trace_square, (basis n).repr.symm.norm_map]

theorem chart_trace_pairing (x y : Coordinates n) :
    realTrace ((chart n x : Matrix n n ℂ) * (chart n y : Matrix n n ℂ)) = inner ℝ x y := by
  change realTrace ((physicalEquiv n ((basis n).repr.symm x) : Matrix n n ℂ) *
    (physicalEquiv n ((basis n).repr.symm y) : Matrix n n ℂ)) = _
  rw [physicalEquiv_trace_pairing, (basis n).repr.symm.inner_map_map]

open KSObjectiveChart

/-- Every physical Hermitian density satisfying the floor has coordinates in
the feasible set. This rules out optimization over only a proper subspace. -/
theorem densityFloor_onto (a : ℝ) (S : selfAdjoint (Matrix n n ℂ)) :
    (a • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ) ∧ realTrace (S : Matrix n n ℂ) = 1) ↔
      ∃ x ∈ densityFloor (chart n) a, chart n x = S := by
  constructor
  · intro hS
    obtain ⟨x, hx⟩ := chart_surjective n S
    exact ⟨x, by simpa only [densityFloor, Set.mem_setOf_eq, hx] using hS, hx⟩
  · rintro ⟨x, hx, rfl⟩
    exact hx

/-- Physical and coordinate maximization over the density floor are exactly
equivalent, including boundary maximizers. -/
theorem isMaxOn_densityFloor_iff (a : ℝ)
    (f : selfAdjoint (Matrix n n ℂ) → ℝ) (xstar : Coordinates n) :
    IsMaxOn (fun x => f (chart n x)) (densityFloor (chart n) a) xstar ↔
      ∀ S : selfAdjoint (Matrix n n ℂ),
        a • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ) →
        realTrace (S : Matrix n n ℂ) = 1 → f S ≤ f (chart n xstar) := by
  constructor
  · intro hmax S hfloor htr
    obtain ⟨x, hx, hxeq⟩ := (densityFloor_onto n a S).mp ⟨hfloor, htr⟩
    have hh : f (chart n x) ≤ f (chart n xstar) := hmax hx
    simpa only [hxeq] using hh
  · intro hmax x hx
    exact hmax (chart n x) hx.1 hx.2

theorem densityFloor_nonempty [Nonempty n] {a : ℝ}
    (ha : a ≤ (Fintype.card n : ℝ)⁻¹) : (densityFloor (chart n) a).Nonempty := by
  let S : selfAdjoint (Matrix n n ℂ) := ⟨maximallyMixed, maximallyMixed_posDef.isHermitian⟩
  have hfloor : a • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ) :=
    smul_le_smul_of_nonneg_right ha zero_le_one
  obtain ⟨x, hx, _⟩ := (densityFloor_onto n a S).mp
    ⟨hfloor, maximallyMixed_mem_densitySet.2⟩
  exact ⟨x, hx⟩

/-- A maximizer of the original full density objective is a maximizer in
coordinates. Its floor membership is a separate quantitative faithfulness fact. -/
theorem original_maximizer_isMaxOn {ι : Type*} [Fintype ι]
    (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ) {a : ℝ} (ha : 0 < a)
    (S : selfAdjoint (Matrix n n ℂ))
    (hmax : ∀ T ∈ densitySet, densityObjective H B θ T ≤ densityObjective H B θ S) :
    IsMaxOn (objective H B θ (chart n)) (densityFloor (chart n) a)
      ((chartEquiv n).symm S) := by
  intro x hx
  have hS : chart n ((chartEquiv n).symm S) = S := (chartEquiv n).apply_symm_apply S
  change densityObjective H B θ (chart n x : Matrix n n ℂ) ≤
    densityObjective H B θ (chart n ((chartEquiv n).symm S) : Matrix n n ℂ)
  rw [hS]
  exact hmax _ ⟨(densityFloor_posDef (chart n) ha hx).posSemidef, hx.2⟩

end MatrixSpencer.KSFullHermitianChart
