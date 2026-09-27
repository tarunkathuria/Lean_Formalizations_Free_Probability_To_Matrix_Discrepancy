import MatrixSpencer.KSFullManuscriptSDPCoordinates
import MatrixSpencer.KSFullManuscriptAffineObjective

/-! Explicit real coordinates for the dyadic Tsallis SDP. The trace-one
density chart is reused; each of the m auxiliary matrices has its own
Hermitian entry chart, and the fidelity variable is unrestricted complex.
No eigendecomposition or matrix root is used to construct these coordinates. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.DyadicSDPCoordinates
variable {n : Type*} [Fintype n] [LinearOrder n]
set_option maxHeartbeats 600000

abbrev Index (m : ℕ) (a : n) :=
  (KSFullManuscriptTraceCoordinates.Index a ⊕ (Fin m × (n × n))) ⊕ ((n × n) ⊕ (n × n))

def densityLinear (m : ℕ) (a : n) : (Index m a → ℝ) →ₗ[ℝ] selfAdjoint (Matrix n n ℂ) where
  toFun x := KSFullManuscriptTraceCoordinates.linear a (fun p => x (.inl (.inl p)))
  map_add' _ _ := (KSFullManuscriptTraceCoordinates.linear a).map_add _ _
  map_smul' r _ := (KSFullManuscriptTraceCoordinates.linear a).map_smul r _

def auxiliaryLinear (m : ℕ) (a : n) (j : Fin m) :
    (Index m a → ℝ) →ₗ[ℝ] selfAdjoint (Matrix n n ℂ) where
  toFun x := KSFullManuscriptHermitianCoordinates.linear (fun p => x (.inl (.inr (j,p))))
  map_add' _ _ := KSFullManuscriptHermitianCoordinates.linear.map_add _ _
  map_smul' r _ := KSFullManuscriptHermitianCoordinates.linear.map_smul r _

def fidelityLinear (m : ℕ) (a : n) : (Index m a → ℝ) →ₗ[ℝ] Matrix n n ℂ where
  toFun x := fun i j => (x (.inr (.inl (i,j))) : ℂ) + (x (.inr (.inr (i,j))) : ℂ) * Complex.I
  map_add' x y := by ext i j; simp only [Pi.add_apply, Matrix.add_apply, Complex.ofReal_add]; ring
  map_smul' r x := by
    ext i j
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Matrix.smul_apply,
      Complex.real_smul, RingHom.id_apply]
    ring

def density (m : ℕ) (a : n) (S₀ : selfAdjoint (Matrix n n ℂ)) (x : Index m a → ℝ) :=
  S₀ + densityLinear m a x

def chain (m : ℕ) (a : n) (x : Index m a → ℝ) : Fin (m+1) → Matrix n n ℂ :=
  Fin.cases 1 (fun j => auxiliaryLinear m a j x)

def chainLinear (m : ℕ) (a : n) (j : Fin (m+1)) : (Index m a → ℝ) →ₗ[ℝ] Matrix n n ℂ :=
  Fin.cases 0 (fun k => (hermitianInclusion (n:=n)).toLinearMap.comp (auxiliaryLinear m a k)) j

@[simp] theorem chain_zero (m : ℕ) (a : n) (x : Index m a → ℝ) : chain m a x 0 = 1 := rfl
@[simp] theorem chain_succ (m : ℕ) (a : n) (x : Index m a → ℝ) (j : Fin m) :
    chain m a x j.succ = auxiliaryLinear m a j x := rfl

theorem chain_affine (m : ℕ) (a : n) (x y : Index m a → ℝ) (j : Fin (m+1)) :
    chain m a (x+y) j = chain m a x j + chainLinear m a j y := by
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [chain,chainLinear]
  · change ((auxiliaryLinear m a k (x+y) : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) = _
    rw [map_add]
    rfl

theorem chain_hermitian (m : ℕ) (a : n) (x : Index m a → ℝ) (j : Fin (m+1)) :
    (chain m a x j).IsHermitian := by
  refine Fin.cases Matrix.isHermitian_one (fun k => ?_) j
  exact (auxiliaryLinear m a k x).property

theorem chainLinear_hermitian (m : ℕ) (a : n) (x : Index m a → ℝ) (j : Fin (m+1)) :
    (chainLinear m a j x).IsHermitian := by
  refine Fin.cases Matrix.isHermitian_zero (fun k => ?_) j
  exact (auxiliaryLinear m a k x).property

def encode (m : ℕ) (a : n) (S₀ S : selfAdjoint (Matrix n n ℂ))
    (Y : Fin m → selfAdjoint (Matrix n n ℂ)) (Z : Matrix n n ℂ) : Index m a → ℝ :=
  Sum.elim (Sum.elim
    (fun p => KSFullManuscriptHermitianCoordinates.encode (S-S₀ : selfAdjoint (Matrix n n ℂ)) p.val)
    (fun p => KSFullManuscriptHermitianCoordinates.encode (Y p.1) p.2))
    (Sum.elim (fun p => (Z p.1 p.2).re) (fun p => (Z p.1 p.2).im))

theorem density_trace (m : ℕ) (a : n) (S₀ : selfAdjoint (Matrix n n ℂ)) (x : Index m a → ℝ) :
    realTrace (density m a S₀ x : Matrix n n ℂ)=realTrace (S₀ : Matrix n n ℂ) := by
  change realTrace ((S₀ : Matrix n n ℂ)+(densityLinear m a x : Matrix n n ℂ))=_
  rw [realTrace_add]
  have h:=KSFullManuscriptTraceCoordinates.linear_trace a (fun p => x (.inl (.inl p)))
  change realTrace (densityLinear m a x : Matrix n n ℂ)=0 at h
  rw [h,add_zero]

theorem density_encode (m : ℕ) (a : n) (S₀ S : selfAdjoint (Matrix n n ℂ))
    (Y : Fin m → selfAdjoint (Matrix n n ℂ)) (Z : Matrix n n ℂ)
    (htr : realTrace (S : Matrix n n ℂ)=realTrace (S₀ : Matrix n n ℂ)) :
    density m a S₀ (encode m a S₀ S Y Z)=S := by
  have ht : realTrace ((S-S₀ : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ)=0 := by
    change realTrace ((S : Matrix n n ℂ)-(S₀ : Matrix n n ℂ))=0
    rw [realTrace_sub,htr,sub_self]
  have h:=KSFullManuscriptTraceCoordinates.linear_onto_trace_zero a (S-S₀) ht
  change S₀+KSFullManuscriptTraceCoordinates.linear a
    (fun p => KSFullManuscriptHermitianCoordinates.encode (S-S₀ : selfAdjoint (Matrix n n ℂ)) p.val)=S
  rw [h]
  abel

theorem auxiliary_encode (m : ℕ) (a : n) (S₀ S : selfAdjoint (Matrix n n ℂ))
    (Y : Fin m → selfAdjoint (Matrix n n ℂ)) (Z : Matrix n n ℂ) (j : Fin m) :
    auxiliaryLinear m a j (encode m a S₀ S Y Z)=Y j := by
  exact (KSFullManuscriptHermitianCoordinates.equiv (n:=n)).apply_symm_apply (Y j)

theorem fidelity_encode (m : ℕ) (a : n) (S₀ S : selfAdjoint (Matrix n n ℂ))
    (Y : Fin m → selfAdjoint (Matrix n n ℂ)) (Z : Matrix n n ℂ) :
    fidelityLinear m a (encode m a S₀ S Y Z)=Z := by
  ext i j
  exact Complex.re_add_im (Z i j)

abbrev dimension (m : ℕ) (a : n) := Fintype.card (Index m a)
abbrev Space (m : ℕ) (a : n) := EuclideanSpace ℝ (Fin (dimension m a))
def entries (m : ℕ) (a : n) (x : Space m a) : Index m a → ℝ := fun p => x (Fintype.equivFin (Index m a) p)
def coordinates (m : ℕ) (a : n) (x : Index m a → ℝ) : Space m a :=
  WithLp.toLp 2 (fun i => x ((Fintype.equivFin (Index m a)).symm i))
theorem entries_coordinates (m : ℕ) (a : n) (x : Index m a → ℝ) : entries m a (coordinates m a x)=x := by
  funext p
  simp [entries,coordinates]
def unit (m : ℕ) (a : n) (i : Fin (dimension m a)) : Space m a := WithLp.toLp 2 (Pi.single i 1)
theorem sum_units (m : ℕ) (a : n) (x : Space m a) : ∑i,x i • unit m a i=x := by
  simpa only [unit,PiLp.basisFun_repr,PiLp.basisFun_apply] using
    (PiLp.basisFun 2 ℝ (Fin (dimension m a))).sum_repr x

theorem dimension_eq (m : ℕ) (a : n) : dimension m a=(m+3)*Fintype.card n^2-1 := by
  have hn : 1≤Fintype.card n := by letI : Nonempty n:=⟨a⟩; exact Fintype.card_pos
  have hc : Fintype.card (KSFullManuscriptTraceCoordinates.Index a)=Fintype.card n*Fintype.card n-1 := by
    simpa only [Fintype.card_prod,Fintype.card_unique] using Fintype.card_subtype_compl (fun p:n×n => p=(a,a))
  simp only [dimension,Index,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,hc]
  have hp : 1≤Fintype.card n*Fintype.card n := Nat.mul_pos hn hn
  have he : (m+3)*Fintype.card n^2=m*(Fintype.card n*Fintype.card n)+3*(Fintype.card n*Fintype.card n) := by ring
  rw [he]
  omega

end MatrixSpencer.DyadicSDPCoordinates
