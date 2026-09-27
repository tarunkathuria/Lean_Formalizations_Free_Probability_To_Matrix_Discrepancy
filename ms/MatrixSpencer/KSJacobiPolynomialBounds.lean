import MatrixSpencer.KSStencilMatrixBounds
import MatrixSpencer.KSManuscriptInputPolynomialParameters
import MatrixSpencer.RealRAMCeiling
import MatrixSpencer.RealRAMJacobiIteration

/-!
# Natural polynomial budgets for the actual finite KS Jacobi loops

The caps below are fixed polynomials in the original label count and physical
dimension. Report magnitude hypotheses describe only the queried ball; the
separate value-accuracy/magnitude layer supplies them for each actual solver.
No spectral gap or unknown Hessian norm is used in these loop bounds.
-/

open Matrix
noncomputable section
namespace MatrixSpencer.KSJacobiPolynomialBounds
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
open KSEighthManuscriptPreprocess KSManuscriptInputPolynomialParameters
open KSManuscriptPolynomialTaylorBounds
variable {N d m : ℕ}

def base (N d : ℕ) : ℕ := 100000*(N+d+1)
def taylor (N d : ℕ) : ℕ := base N d ^ 275
def fullQuery (N d : ℕ) : ℕ := 32*N^2+800*N^3*taylor N d
def fullEntry (N d : ℕ) : ℕ := 4*(base N d+1)*fullQuery N d
def fullKappa (N : ℕ) : ℕ := 100*N^2
def eighthQuery (N d : ℕ) : ℕ := 1024+1000000*taylor N d*N^5
def eighthEntry (N d : ℕ) : ℕ := (base N d+1)*eighthQuery N d
def eighthScaledEntry (N d : ℕ) : ℕ := 10000*N^3*eighthEntry N d
def eighthBeta (N d : ℕ) : ℕ := 1000000*N^4*(taylor N d+1)
def jacobi (N V K : ℕ) : ℕ := (N^2+1)*N^2*V^2*K^2+1
def fullJacobi (N d : ℕ) : ℕ := jacobi N (fullEntry N d) (fullKappa N)
def eighthJacobi (N d : ℕ) : ℕ := jacobi N (eighthScaledEntry N d) (eighthBeta N d)

@[simp] theorem cast_base (N d : ℕ) : (base N d : ℝ) = sizeBase N d := by
  simp [base, sizeBase]
@[simp] theorem cast_taylor (N d : ℕ) : (taylor N d : ℝ) = taylorCap N d := by
  simp only [taylor, Nat.cast_pow, cast_base, taylorCap]

theorem iterationCount_le (A : Matrix (Fin m) (Fin m) ℝ) (hm : m ≤ N)
    {V K : ℕ} (hA : ∀ i j, |A i j| ≤ (V : ℝ)) {τ : ℝ}
    (hτ : 0 ≤ τ) (hK : τ⁻¹ ≤ (K : ℝ)) :
    KSJacobiIteration.iterationCount A τ ≤ jacobi N V K := by
  have hs : 1/τ^2 ≤ (K : ℝ)^2 := by
    rw [one_div, ← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.mpr hτ) hK 2
  have h := KSStencilMagnitudeBounds.iterationCount_le_of_entries A
    (Nat.cast_nonneg V) hA hs
  apply (Nat.cast_le (α := ℝ)).mp
  calc
    (KSJacobiIteration.iterationCount A τ : ℝ) ≤
        ((m : ℝ)^2+1)*(m : ℝ)^2*(V : ℝ)^2*(K : ℝ)^2+1 := h
    _ ≤ ((N : ℝ)^2+1)*(N : ℝ)^2*(V : ℝ)^2*(K : ℝ)^2+1 := by
      have hc : (m : ℝ) ≤ N := Nat.cast_le.mpr hm
      gcongr
    _ = (jacobi N V K : ℝ) := by simp [jacobi]

/-- The real ceiling input itself is bounded, so the natural budget can be
computed by the already verified bounded comparison loop. -/
theorem ceiling_input_le (A : Matrix (Fin m) (Fin m) ℝ) (hm : m ≤ N)
    {V K : ℕ} (hA : ∀ i j, |A i j| ≤ (V : ℝ)) {τ : ℝ}
    (hτ : 0 ≤ τ) (hK : τ⁻¹ ≤ (K : ℝ)) :
    KSJacobiIteration.denominator m*KSJacobiStep.offDiagonalEnergy A/τ^2 ≤
      (jacobi N V K : ℝ) := by
  exact (Nat.le_ceil _).trans (Nat.cast_le.mpr (iterationCount_le A hm hA hτ hK))

theorem diagonalize_cost_le (A : Matrix (Fin m) (Fin m) ℝ) (hm : m ≤ N)
    {V K : ℕ} (hA : ∀ i j, |A i j| ≤ (V : ℝ)) {τ : ℝ}
    (hτ : 0 ≤ τ) (hK : τ⁻¹ ≤ (K : ℝ)) :
    (RealRAM.JacobiIteration.diagonalize A (KSJacobiIteration.iterationCount A τ)).cost ≤
      510*(jacobi N V K+1)*(N+1)^3 := by
  apply (RealRAM.JacobiIteration.diagonalize_cost A _).trans
  have hc := iterationCount_le A hm hA hτ hK
  gcongr

theorem full_matrix_entries (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1)
    (report : KSNumericalHessian.Space m → ℝ)
    (hreport : ∀ z, ‖z‖ ≤ Real.sqrt (epsilon v)/2 → |report z| ≤ sizeBase N d+1)
    (w : Fin m → ℝ) (hw : ∀ i, |w i| ≤ 1) (i j : Fin m) :
    |KSFullManuscriptHessian.weighted w
      (KSFullManuscriptHessian.matrixReport report 0
        (KSFullManuscriptParameters.queryStep N (Real.sqrt (epsilon v))
          (KSFullManuscriptAlgorithm.taylorBudget v (epsilon v)))) i j| ≤
        (fullEntry N d : ℝ) := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hbase := sizeBase_pos N d
  have hN := labels_pos v hd hp
  have hδ := Real.sqrt_pos.mpr (epsilon_pos v hd hp)
  have hM := KSFullManuscriptAlgorithm.taylorBudget_pos v hN (epsilon_pos v hd hp)
  have ht := KSFullManuscriptParameters.queryStep_pos hN hδ hM
  have htR := KSFullManuscriptQueries.queryStep_le_quarter N
    (M := KSFullManuscriptAlgorithm.taylorBudget v (epsilon v)) hδ.le
  have hentry := KSStencilMatrixBounds.full_matrixReport_abs report ht.le
    (by linarith : 2*KSFullManuscriptParameters.queryStep N (Real.sqrt (epsilon v))
      (KSFullManuscriptAlgorithm.taylorBudget v (epsilon v)) ≤ Real.sqrt (epsilon v)/2)
    (by positivity : 0 ≤ sizeBase N d+1) hreport
  have he := KSStencilMatrixBounds.weighted_abs w hw _ (by positivity) hentry i j
  have hq := full_query_inv_sq_le v hd hp
  calc
    _ ≤ 4*(sizeBase N d+1)/
        KSFullManuscriptParameters.queryStep N (Real.sqrt (epsilon v))
          (KSFullManuscriptAlgorithm.taylorBudget v (epsilon v))^2 := he
    _ = 4*(sizeBase N d+1)*
        (KSFullManuscriptParameters.queryStep N (Real.sqrt (epsilon v))
          (KSFullManuscriptAlgorithm.taylorBudget v (epsilon v))^2)⁻¹ := by ring
    _ ≤ 4*(sizeBase N d+1)*(32*(N : ℝ)^2+800*(N : ℝ)^3*taylorCap N d) := by
      gcongr
    _ = (fullEntry N d : ℝ) := by simp only [fullEntry, fullQuery, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_pow, cast_taylor, cast_base, Nat.cast_one]

theorem full_iterationCount_le (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) (hm : m ≤ N)
    (report : KSNumericalHessian.Space m → ℝ)
    (hreport : ∀ z, ‖z‖ ≤ Real.sqrt (epsilon v)/2 → |report z| ≤ sizeBase N d+1)
    (w : Fin m → ℝ) (hw : ∀ i, |w i| ≤ 1) :
    KSJacobiIteration.iterationCount
      (KSFullManuscriptHessian.weighted w
        (KSFullManuscriptHessian.matrixReport report 0
          (KSFullManuscriptParameters.queryStep N (Real.sqrt (epsilon v))
            (KSFullManuscriptAlgorithm.taylorBudget v (epsilon v)))))
      (KSFullManuscriptParameters.curvatureTolerance N (Real.sqrt (epsilon v))) ≤ fullJacobi N d := by
  have hk := full_curvature_inv_le v hd hp
  have hk0 := KSFullManuscriptParameters.curvatureTolerance_pos
    (labels_pos v hd hp) (Real.sqrt_pos.mpr (epsilon_pos v hd hp))
  apply iterationCount_le _ hm (full_matrix_entries v hd hp report hreport w hw) hk0.le
  simpa [fullKappa] using hk

theorem eighth_matrix_entries (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) (x : Fin N → ℝ)
    (hx : 0 < KSEighthLiveEnumeration.count x)
    (report : KSEighthFacePotential.Space x → ℝ)
    (hreport : ∀ z, ‖z‖ ≤ 1/16 → |report z| ≤ sizeBase N d+1)
    (i j : Fin (KSEighthLiveEnumeration.count x)) :
    |((1/2 : ℝ) • KSMatrixEntryAccuracy.symmetrize
      (KSNumericalHessian.matrixReport report 0
        (KSEighthHessianQueries.queryMesh v (ksRegularizerScale (epsilon v) (Fin d))
          (KSEighthManuscriptParameters.precision N (Real.sqrt (epsilon v))) x))) i j| ≤
      (eighthEntry N d : ℝ) := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hbase := sizeBase_pos N d
  have hN := labels_pos v hd hp
  have hδ := Real.sqrt_pos.mpr (epsilon_pos v hd hp)
  have hθ := ksRegularizerScale_pos (n := Fin d) (epsilon_pos v hd hp)
  have hη := KSEighthManuscriptParameters.precision_pos hN hδ
  have hM := KSEighthManuscriptParameters.fourthCap_pos v hθ hd
  have ht := KSEighthHessianQueries.queryMesh_pos v hθ hη hd x hx
  have htR := KSEighthHessianQueries.queryMesh_le v
    (ksRegularizerScale (epsilon v) (Fin d))
    (KSEighthManuscriptParameters.precision N (Real.sqrt (epsilon v))) x
  have hentry := KSStencilMatrixBounds.eighth_matrixReport_abs report ht.le
    (by linarith : 2*KSEighthHessianQueries.queryMesh v
      (ksRegularizerScale (epsilon v) (Fin d))
      (KSEighthManuscriptParameters.precision N (Real.sqrt (epsilon v))) x ≤ 1/16) hreport
  have hsym := KSStencilMatrixBounds.symmetrize_abs _ hentry
  have he := KSStencilMatrixBounds.half_smul_abs _ (by positivity) hsym i j
  have hq := KSManuscriptPolynomialParameters.eighth_query_inv_sq_le v hN hδ
    (KSManuscriptScaleBounds.inverse_delta_le v hd hp) hM
    (eighth_fourthCap_le_taylorCap v hd hp) x hx
  calc
    _ ≤ (sizeBase N d+1)/
        KSEighthHessianQueries.queryMesh v (ksRegularizerScale (epsilon v) (Fin d))
          (KSEighthManuscriptParameters.precision N (Real.sqrt (epsilon v))) x^2 := he
    _ = (sizeBase N d+1)*
        (KSEighthHessianQueries.queryMesh v (ksRegularizerScale (epsilon v) (Fin d))
          (KSEighthManuscriptParameters.precision N (Real.sqrt (epsilon v))) x^2)⁻¹ := by ring
    _ ≤ (sizeBase N d+1)*(1024+1000000*taylorCap N d*(N : ℝ)^5) := by gcongr
    _ = (eighthEntry N d : ℝ) := by simp only [eighthEntry, eighthQuery, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_pow, cast_taylor, cast_base, Nat.cast_one]

theorem eighth_iterationCount_le (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) (x : Fin N → ℝ)
    (hx : 0 < KSEighthLiveEnumeration.count x)
    (report : KSEighthFacePotential.Space x → ℝ)
    (hreport : ∀ z, ‖z‖ ≤ 1/16 → |report z| ≤ sizeBase N d+1) :
    KSJacobiIteration.iterationCount
      ((-(KSEighthManuscriptParameters.kappa N (Real.sqrt (epsilon v)))⁻¹) •
        ((1/2 : ℝ) • KSMatrixEntryAccuracy.symmetrize
          (KSNumericalHessian.matrixReport report 0
            (KSEighthHessianQueries.queryMesh v (ksRegularizerScale (epsilon v) (Fin d))
              (KSEighthManuscriptParameters.precision N (Real.sqrt (epsilon v))) x))))
      (KSEighthManuscriptParameters.beta v (Real.sqrt (epsilon v))
        (ksRegularizerScale (epsilon v) (Fin d))) ≤ eighthJacobi N d := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hN := labels_pos v hd hp
  have hδ := Real.sqrt_pos.mpr (epsilon_pos v hd hp)
  have hθ := ksRegularizerScale_pos (n := Fin d) (epsilon_pos v hd hp)
  have hM := KSEighthManuscriptParameters.fourthCap_pos v hθ hd
  have hδinv := KSManuscriptScaleBounds.inverse_delta_le v hd hp
  have hk := KSManuscriptPolynomialParameters.eighth_kappa_inv_le hδinv
  have hk0 := (KSEighthManuscriptParameters.kappa_pos hN hδ).le
  have hb0 := (KSEighthManuscriptParameters.beta_pos v hN hδ hθ hd).le
  have hb := KSManuscriptPolynomialParameters.eighth_beta_inv_le v hδ hδinv hM.le
    (eighth_fourthCap_le_taylorCap v hd hp)
  have he := eighth_matrix_entries v hd hp x hx report hreport
  have hs := KSStencilMatrixBounds.reciprocal_scaled_abs _ (Nat.cast_nonneg (eighthEntry N d)) he hk0 hk
  apply iterationCount_le _ (KSEighthManuscriptMovement.count_le x) (V := eighthScaledEntry N d)
    (K := eighthBeta N d) _ hb0 _
  · intro i j
    simpa only [eighthScaledEntry, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using hs i j
  · simpa only [eighthBeta, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_one, cast_taylor] using hb

end MatrixSpencer.KSJacobiPolynomialBounds
