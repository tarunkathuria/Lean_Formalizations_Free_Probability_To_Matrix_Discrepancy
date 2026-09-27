import MatrixSpencer.KSCompactTraceRoots
import MatrixSpencer.KSComplexSpinDomain

/-!
# Exact agreement of the holomorphic trace with the KS fidelity

The constructed trace integral agrees with the CFC square-root trace on
positive definite matrices. Cyclic characteristic polynomials identify the
trace of a nonsymmetric positive product with actual fidelity. The canonical
fixed-support compression then handles singular physical Kraus sources,
including empty support, and gives the exact real KS polynomial-source identity.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSHolomorphicFidelity
open KSScalarHolomorphicRoot KSCompactResolvent
variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

theorem trace_sqrt_eq_sum_eigenvalues {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    Matrix.trace (CFC.sqrt A) = ∑ i, (Real.sqrt (hA.isHermitian.eigenvalues i) : ℂ) := by
  rw [CFC.sqrt_eq_real_sqrt A hA.nonneg, cfcₙ_eq_cfc (hf0 := Real.sqrt_zero),
    hA.isHermitian.cfc_eq, Matrix.IsHermitian.cfc]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp

theorem roots_principalRoot_sum_eq_trace_sqrt {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (A.charpoly.roots.map principalRoot).sum = Matrix.trace (CFC.sqrt A) := by
  rw [trace_sqrt_eq_sum_eigenvalues hA, hA.isHermitian.roots_charpoly_eq_eigenvalues,
    Multiset.map_map]
  change (∑ i, principalRoot (hA.isHermitian.eigenvalues i : ℂ)) = _
  apply Finset.sum_congr rfl
  intro i _
  exact principalRoot_ofReal (hA.eigenvalues_nonneg i)

theorem trace_sqrt_eq_ofReal {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    Matrix.trace (CFC.sqrt A) = (realTrace (CFC.sqrt A) : ℂ) := by
  rw [realTrace, trace_sqrt_eq_sum_eigenvalues hA]
  simp

open KSAccretiveProductDomain KSCompactTraceRoots

omit [DecidableEq n] in
theorem strictAccretive_of_posDef {A : Matrix n n ℂ} (hA : A.PosDef) : StrictAccretive A :=
  fun _ hv => hA.re_dotProduct_pos hv

theorem domain_of_posDef {A : Matrix n n ℂ} (hA : A.PosDef) : Domain A := by
  have hh := product_spectrum_subset_slitPlane (strictAccretive_of_posDef hA)
    (strictAccretive_of_posDef (Matrix.PosDef.one (n := n) (R := ℂ)))
  simpa using hh

theorem domain_product_of_posDef {S M : Matrix n n ℂ} (hS : S.PosDef) (hM : M.PosDef) :
    Domain (S*M) :=
  product_spectrum_subset_slitPlane (strictAccretive_of_posDef hS) (strictAccretive_of_posDef hM)

/-- On positive definite matrices, the constructed analytic extension is the actual CFC trace. -/
theorem traceRoot_posDef {A : Matrix n n ℂ} (hA : A.PosDef) :
    traceRoot A = (realTrace (CFC.sqrt A) : ℂ) := by
  rw [traceRoot_eq_sum_roots (domain_of_posDef hA),
    roots_principalRoot_sum_eq_trace_sqrt hA.posSemidef, trace_sqrt_eq_ofReal hA.posSemidef]

/-- The principal trace of the nonsymmetric product equals actual matrix fidelity. -/
theorem traceRoot_product_eq_fidelity {S M : Matrix n n ℂ}
    (hS : S.PosDef) (hM : M.PosDef) :
    traceRoot (S*M) = (fidelity S M : ℂ) := by
  have hQ : (CFC.sqrt S * M * CFC.sqrt S).PosDef := by
    simpa only [hS.posDef_sqrt.isHermitian.eq] using
      hM.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.mpr hS.posDef_sqrt.isUnit)
  have he : (CFC.sqrt S * M * CFC.sqrt S).charpoly = (S*M).charpoly := by
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
      CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg]
  rw [traceRoot_eq_sum_roots (domain_product_of_posDef hS hM), ← he,
    ← traceRoot_eq_sum_roots (domain_of_posDef hQ), traceRoot_posDef hQ]
  rfl

/-- Fixed-support compression handles singular physical sources without a source gap. -/
theorem traceRoot_compressed_eq_fidelity (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    {S : Matrix n n ℂ} {M : Matrix m m ℂ} (hS : S.PosDef) (hM : M.PosDef) :
    traceRoot ((Vᴴ*S*V)*M) = (fidelity S (V*M*Vᴴ) : ℂ) := by
  rw [traceRoot_product_eq_fidelity (posDef_isometry_compression V hV hS) hM,
    fidelity_isometry_compression V hV hS.posSemidef hM.posSemidef]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The exact covariance-supported fidelity, including singular physical sources. -/
theorem traceRoot_covariance_eq_fidelity (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosDef)
    {S : Matrix n n ℂ} (hS : S.PosDef) :
    traceRoot (krausCompressedDensity A S * covarianceCompressedSource A C S) =
      (fidelity S (covarianceSource A C S) : ℂ) := by
  have hp := covariance_compressed_pair_posDef A hA hC hS
  rw [traceRoot_product_eq_fidelity hp.1 hp.2,
    fidelity_covariance_support_compression A hA hC hS]

/-- At a real live-face parameter the actual complex polynomial source recovers
exactly the fidelity term in the actual KS owner objective. -/
theorem traceRoot_spin_source_eq_fidelity (v : ι → n → ℂ) (x h : ι → ℝ) (t : ℝ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef)
    (hc : ∀ i, 0 < 64 * (1 - (x i + t*h i)^2)) :
    traceRoot (KSComplexSpinDomain.compressedDensity v S *
      KSComplexSpinDomain.compressedSource v x h ((t : ℂ), S)) =
      (fidelity S (covarianceSource (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
        (KSSpinSource.coefficientCovariance (fun i => 64 * (1 - (x i + t*h i)^2))) S) : ℂ) := by
  unfold KSComplexSpinDomain.compressedSource
  rw [KSComplexSpinSource.source_real]
  exact traceRoot_covariance_eq_fidelity _
    (KSSpinSource.family_isHermitian _ (fun i => (KSRankOne.atom_posSemidef (v i)).isHermitian))
    (KSSpinCompression.coefficientCovariance_posDef hc) hS

end MatrixSpencer.KSHolomorphicFidelity
