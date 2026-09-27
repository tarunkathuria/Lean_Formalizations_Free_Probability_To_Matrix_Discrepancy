import FaithfulMS.SpectralArithmetic
import MatrixSpencer.KrausReducedFamily

/-! Computing the actual source support from its eigenvalues.
The projection used by the direct-density transport is reconstructed from
the eigendecomposition of the source matrix; no basis of an abstract range
is supplied to the algorithm.
-/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace FaithfulMS.SpectralArithmetic
open MatrixSpencer
local instance {n : Type*} [Fintype n] [DecidableEq n] : CStarAlgebra (Matrix n n ℂ) := {}

def supportScalar (x : ℝ) : ℝ := if x = 0 then 0 else 1

theorem finite_spectrum_continuous {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ A) := by
  rw [hA.spectrum_real_eq_range_eigenvalues]
  exact (Set.finite_range _).continuousOn f

theorem support_fixes_source {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    cfc supportScalar A * A = A := by
  have hid : cfc (fun x : ℝ => x) A = A := cfc_id' ℝ A hA
  calc
    _ = cfc supportScalar A * cfc (fun x : ℝ => x) A := by rw [hid]
    _ = cfc (fun x : ℝ => supportScalar x * x) A :=
      (cfc_mul _ _ _ (finite_spectrum_continuous A hA _) continuous_id.continuousOn).symm
    _ = cfc (fun x : ℝ => x) A := by
      congr 1
      funext x
      by_cases hx : x=0 <;> simp [supportScalar,hx]
    _ = A := cfc_id' ℝ A hA

theorem support_source_factorization {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    A * cfc (fun x : ℝ => x⁻¹) A = cfc supportScalar A := by
  have hid : cfc (fun x : ℝ => x) A = A := cfc_id' ℝ A hA
  calc
    _ = cfc (fun x : ℝ => x) A * cfc (fun x : ℝ => x⁻¹) A := by rw [hid]
    _ = cfc (fun x : ℝ => x*x⁻¹) A :=
      (cfc_mul _ _ _ continuous_id.continuousOn (finite_spectrum_continuous A hA _)).symm
    _ = _ := by
      congr 1
      funext x
      by_cases hx : x=0 <;> simp [supportScalar,hx]

/-- Any faithful compression of a PSD matrix has precisely this computed
spectral support projection. The conclusion does not depend on the frame. -/
theorem support_of_isometry {n k : Type*} [Fintype n] [DecidableEq n]
    [Fintype k] [DecidableEq k]
    (V : Matrix n k ℂ) (hV : Vᴴ*V=1)
    (X : Matrix k k ℂ) (hX : X.PosDef) :
    cfc supportScalar (V*X*Vᴴ) = V*Vᴴ := by
  let A := V*X*Vᴴ
  let P := V*Vᴴ
  let Q := cfc supportScalar A
  have hA : A.IsHermitian := (hX.posSemidef.mul_mul_conjTranspose_same V).isHermitian
  have hP : P.IsHermitian := (Matrix.posSemidef_self_mul_conjTranspose V).isHermitian
  have hQ : Q.IsHermitian := cfc_predicate supportScalar A
  have hPA : P*A=A := by
    dsimp only [P,A]
    simp only [Matrix.mul_assoc,←Matrix.mul_assoc Vᴴ V,hV,Matrix.one_mul]
  have hPQ : P*Q=Q := by
    rw [show Q = A*cfc (fun x : ℝ => x⁻¹) A from (support_source_factorization A hA).symm]
    rw [←mul_assoc,hPA]
  have hQP : Q*P=Q := by
    have h := congrArg Matrix.conjTranspose hPQ
    simpa only [Matrix.conjTranspose_mul,hP.eq,hQ.eq] using h
  have hAX : A*(V*X⁻¹*Vᴴ)=P := by
    have hXX : X*X⁻¹=1 := Matrix.mul_nonsing_inv X (X.isUnit_iff_isUnit_det.mp hX.isUnit)
    calc
      _ = V * X * (Vᴴ*V) * X⁻¹ * Vᴴ := by simp only [A,Matrix.mul_assoc]
      _ = P := by
        rw [hV,Matrix.mul_one]
        rw [Matrix.mul_assoc V X, hXX, Matrix.mul_one]
  have hQAP : Q*P=P := by
    rw [←hAX,←mul_assoc,support_fixes_source A hA]
  exact hQP.symm.trans hQAP

theorem source_support_projection {ι n : Type*} [Fintype ι] [Fintype n]
    [DecidableEq n] (B : ι → Matrix n n ℂ)
    {S : Matrix n n ℂ} (hS : S.PosDef) :
    cfc supportScalar (krausChannel B S) = krausSupportProjection B := by
  rw [←krausCompressedSource_reconstruct_posDef B hS]
  exact support_of_isometry (krausSupportEmbedding B) (krausSupportEmbedding_isometry B)
    (krausCompressedSource B S) (krausCompressedSource_posDef B hS)

def spectralSupport {d : ℕ} (A : Mat d) (hA : A.IsHermitian) :
    MatrixSpencer.RealRAM.JacobiIteration.Counted (Mat d) :=
  let r := assembly (hA.eigenvectorUnitary : Mat d) (fun i => supportScalar (hA.eigenvalues i))
  ⟨r.value,1+5*d+r.cost⟩

theorem spectralSupport_value {d : ℕ} (A : Mat d) (hA : A.IsHermitian) :
    (spectralSupport A hA).value = cfc supportScalar A := by
  rw [hA.cfc_eq]
  exact assembly_value _ _

theorem spectralSupport_cost {d : ℕ} (A : Mat d) (hA : A.IsHermitian) :
    (spectralSupport A hA).cost ≤ 40*(d+1)^3 := by
  have h := assembly_cost (hA.eigenvectorUnitary : Mat d)
    (fun i => supportScalar (hA.eigenvalues i))
  dsimp only [spectralSupport]
  nlinarith

/-- On a positive source the guarded reciprocal-root code is the ordinary
inverse of the positive square root. -/
theorem spectralInverseRoot_posDef_value {d : ℕ} (A : Mat d) (hA : A.PosDef) :
    (spectralInverseRoot A hA.isHermitian).value = (CFC.sqrt A)⁻¹ := by
  rw [spectralInverseRoot_value]
  have hf : inverseRootScalar = (fun x : ℝ => (Real.sqrt x)⁻¹) := by
    funext x
    by_cases hx : x=0 <;> simp [inverseRootScalar,hx]
  rw [hf, Matrix.nonsing_inv_eq_ringInverse, CFC.sqrt_eq_real_sqrt A hA.posSemidef.nonneg,
    cfcₙ_eq_cfc (hf0 := Real.sqrt_zero)]
  apply cfc_inv Real.sqrt A (ha := hA.isHermitian)
  intro x hx
  rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i,rfl⟩ := hx
  exact (Real.sqrt_pos.mpr (hA.eigenvalues_pos i)).ne'

end FaithfulMS.SpectralArithmetic
