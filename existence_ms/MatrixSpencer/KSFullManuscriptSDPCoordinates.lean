import MatrixSpencer.KSFullManuscriptTraceCoordinates

/-!
# Actual finite-entry coordinates for the full density SDP

The four coordinate groups store trace-zero density displacement, Hermitian
regularizer displacement, and the real and imaginary fidelity block. The
centers are specified matrices; the application uses the explicit strictly
feasible point (O11). The chart covers every trace-one Hermitian density,
every Hermitian regularizer block, and every complex fidelity block.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSFullManuscriptSDPCoordinates

variable {n : Type*} [Fintype n] [LinearOrder n]

abbrev Index (a : n) := (KSFullManuscriptTraceCoordinates.Index a ⊕ (n × n)) ⊕ ((n × n) ⊕ (n × n))

def densityLinear (a : n) : (Index a → ℝ) →ₗ[ℝ] selfAdjoint (Matrix n n ℂ) where
  toFun x := KSFullManuscriptTraceCoordinates.linear a (fun p => x (.inl (.inl p)))
  map_add' _ _ := (KSFullManuscriptTraceCoordinates.linear a).map_add _ _
  map_smul' r _ := (KSFullManuscriptTraceCoordinates.linear a).map_smul r _

def regularizerLinear (a : n) : (Index a → ℝ) →ₗ[ℝ] selfAdjoint (Matrix n n ℂ) where
  toFun x := KSFullManuscriptHermitianCoordinates.linear (fun p => x (.inl (.inr p)))
  map_add' _ _ := KSFullManuscriptHermitianCoordinates.linear.map_add _ _
  map_smul' r _ := KSFullManuscriptHermitianCoordinates.linear.map_smul r _

def fidelityLinear (a : n) : (Index a → ℝ) →ₗ[ℝ] Matrix n n ℂ where
  toFun x := fun i j => (x (.inr (.inl (i,j))) : ℂ) + (x (.inr (.inr (i,j))) : ℂ) * Complex.I
  map_add' x y := by ext i j; simp only [Pi.add_apply, Matrix.add_apply, Complex.ofReal_add]; ring
  map_smul' r x := by
    ext i j
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Matrix.smul_apply, Complex.real_smul, RingHom.id_apply]
    ring

def density (a : n) (S₀ : selfAdjoint (Matrix n n ℂ)) (x : Index a → ℝ) : selfAdjoint (Matrix n n ℂ) :=
  S₀ + densityLinear a x

def regularizer (a : n) (Y₀ : selfAdjoint (Matrix n n ℂ)) (x : Index a → ℝ) : selfAdjoint (Matrix n n ℂ) :=
  Y₀ + regularizerLinear a x

def encode (a : n) (S₀ Y₀ S Y : selfAdjoint (Matrix n n ℂ)) (Z : Matrix n n ℂ) : Index a → ℝ :=
  Sum.elim
    (Sum.elim (fun p => KSFullManuscriptHermitianCoordinates.encode (S - S₀ : selfAdjoint (Matrix n n ℂ)) p.val)
      (KSFullManuscriptHermitianCoordinates.encode (Y - Y₀ : selfAdjoint (Matrix n n ℂ))))
    (Sum.elim (fun p => (Z p.1 p.2).re) (fun p => (Z p.1 p.2).im))

theorem density_trace (a : n) (S₀ : selfAdjoint (Matrix n n ℂ)) (x : Index a → ℝ) :
    realTrace (density a S₀ x : Matrix n n ℂ) = realTrace (S₀ : Matrix n n ℂ) := by
  change realTrace ((S₀ : Matrix n n ℂ) + (densityLinear a x : Matrix n n ℂ)) = _
  rw [realTrace_add]
  have hh := KSFullManuscriptTraceCoordinates.linear_trace a (fun p => x (.inl (.inl p)))
  change realTrace (densityLinear a x : Matrix n n ℂ) = 0 at hh
  rw [hh, add_zero]

theorem density_encode (a : n) (S₀ Y₀ S Y : selfAdjoint (Matrix n n ℂ)) (Z : Matrix n n ℂ)
    (htr : realTrace (S : Matrix n n ℂ) = realTrace (S₀ : Matrix n n ℂ)) :
    density a S₀ (encode a S₀ Y₀ S Y Z) = S := by
  have ht : realTrace ((S - S₀ : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) = 0 := by
    change realTrace ((S : Matrix n n ℂ) - (S₀ : Matrix n n ℂ)) = 0
    rw [realTrace_sub, htr, sub_self]
  have hh := KSFullManuscriptTraceCoordinates.linear_onto_trace_zero a (S - S₀) ht
  change S₀ + KSFullManuscriptTraceCoordinates.linear a
    (fun p => KSFullManuscriptHermitianCoordinates.encode (S - S₀ : selfAdjoint (Matrix n n ℂ)) p.val) = S
  rw [hh]
  abel

theorem regularizer_encode (a : n) (S₀ Y₀ S Y : selfAdjoint (Matrix n n ℂ)) (Z : Matrix n n ℂ) :
    regularizer a Y₀ (encode a S₀ Y₀ S Y Z) = Y := by
  have hh := (KSFullManuscriptHermitianCoordinates.equiv (n := n)).apply_symm_apply (Y - Y₀)
  change Y₀ + KSFullManuscriptHermitianCoordinates.equiv
    ((KSFullManuscriptHermitianCoordinates.equiv (n := n)).symm (Y - Y₀)) = Y
  rw [hh]
  abel

omit [Fintype n] in
theorem fidelity_encode (a : n) (S₀ Y₀ S Y : selfAdjoint (Matrix n n ℂ)) (Z : Matrix n n ℂ) :
    fidelityLinear a (encode a S₀ Y₀ S Y Z) = Z := by
  ext i j
  exact Complex.re_add_im (Z i j)

/-- All original matrix variables are represented, not merely a proper
subspace of the trace-one affine hyperplane. -/
theorem onto (a : n) (S₀ Y₀ S Y : selfAdjoint (Matrix n n ℂ)) (Z : Matrix n n ℂ)
    (htr : realTrace (S : Matrix n n ℂ) = realTrace (S₀ : Matrix n n ℂ)) :
    ∃ x : Index a → ℝ, density a S₀ x = S ∧ regularizer a Y₀ x = Y ∧ fidelityLinear a x = Z :=
  ⟨encode a S₀ Y₀ S Y Z, density_encode a S₀ Y₀ S Y Z htr,
    regularizer_encode a S₀ Y₀ S Y Z, fidelity_encode a S₀ Y₀ S Y Z⟩

end MatrixSpencer.KSFullManuscriptSDPCoordinates
