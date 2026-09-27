import SeamlessKS.RuntimeBudgets
import SeamlessKS.NumericQueries
import SeamlessKS.StateBounds

/-! Magnitude bounds for the actual reports and finite Hessian matrices.
They use only the original Parseval vectors and accuracy of the SDP solver. -/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace SeamlessKS.RuntimeMagnitude
open MatrixSpencer SeamlessKS.State SeamlessKS.StatePotential SeamlessKS.Parameters
open SeamlessKS.Walk SeamlessKS.LivePotential
open MatrixSpencer.KSLiveEnumeration (count)
open MatrixSpencer.KSFullManuscriptLiveCoordinates (face)
variable {N d : ℕ} [Nonempty (Fin d)]

omit [Nonempty (Fin d)] in
theorem hessianAccuracy_le_one (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : ∑ i,KSRankOne.atom (v i)=1) : hessianAccuracy v≤1 := by
  have hN : (1:ℝ)≤N := by exact_mod_cast Input.labels_pos v hd hp
  have hb : beta v≤1 := by
    unfold beta
    apply (div_le_iff₀ (by positivity : (0:ℝ)<100*(N:ℝ))).mpr
    have hh := Input.delta_le_one v hp
    linarith
  have ht : queryStep v≤1 := by
    have hr := rho_le_one v hd hp
    have hq : queryStep v≤rho N/16 := min_le_left _ _
    linarith
  have ht2 := pow_le_pow_left₀ (queryStep_pos v hd hp).le ht 2
  norm_num only [one_pow] at ht2
  have hmul := mul_le_mul hb ht2 (sq_nonneg _) (by norm_num : (0:ℝ)≤1)
  unfold hessianAccuracy
  apply (div_le_iff₀ (by positivity : (0:ℝ)<128*(N:ℝ))).mpr
  linarith

theorem query_potential_abs (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : ∑ i,KSRankOne.atom (v i)=1) (s : WalkState N) (y : Fin N → ℝ)
    (hy : y∈ksCube 1) :
    |KSDebitPotential.potential (signedSum v y) (debit v s.toCubeState) v
      (SourceTransport.smoothWeights (zeta N) y) (Input.theta v)|≤36 := by
  have hc0 (i : Fin N) : 0≤Source.weight 64 (zeta N) (y i) :=
    Source.weight_nonneg (by norm_num) (abs_le.mpr ⟨hy.1 i,hy.2 i⟩)
  have hc128 (i : Fin N) : Source.weight 64 (zeta N) (y i)≤128 :=
    by
      simpa only [show (2:ℝ)*64=128 by norm_num] using Source.weight_upper (u:=64) (by norm_num)
        (zeta_pos (Input.labels_pos v hd hp)).le (y i)
  have hb := debit_bounds v hp s.toCubeState
  have hθ := Input.theta_pos v hd hp
  have hu := StateBounds.ownerPotential_le_thirtysix v hp.le
    (SourceTransport.smoothWeights (zeta N) y) hc0 hc128
    (KSDebitCenter.center (signedSum v y) (debit v s.toCubeState))
    (KSDebitCenter.center_isHermitian (signedSum_isHermitian v y) hb.1.isHermitian)
    (StateBounds.actual_center_norm_le_two v hd hp y
      (fun i => abs_le.mpr ⟨hy.1 i,hy.2 i⟩) hb.1 hb.2)
    hθ (StateBounds.original_regularizer_budget v hd hp)
  have hl := KSDebitPotential.norm_le_potential_add (signedSum_isHermitian v y)
    hb.2 v hc0 hθ
  have hr := rho_le_one v hd hp
  apply abs_le.mpr
  constructor
  · change -(36:ℝ)≤KSDebitPotential.potential (signedSum v y) (debit v s.toCubeState) v
      (fun i => Source.weight 64 (zeta N) (y i)) (Input.theta v)
    have hh := norm_nonneg (signedSum v y)
    linarith
  · exact hu

theorem faceReport_abs (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) (s : WalkState N)
    (z : EuclideanSpace ℝ (Fin (count s.coeff))) (hz : ‖z‖<rho N) :
    |faceReport O v s z|≤37 := by
  have he := NumericQueries.faceReport_accuracy O v hd hp s z hz
  have hy := KSFullManuscriptLiveCoordinates.face_mem_cube s.cube z
    (fun i hi => (s.margin i hi).le) hz
  have hf := query_potential_abs v hd hp s (face s.coeff z) hy
  have hν := hessianAccuracy_le_one v hd hp
  have ha := abs_add_le
    (faceReport O v s z-faceValue v (Input.theta v) (zeta N) s.toCubeState z)
    (faceValue v (Input.theta v) (zeta N) s.toCubeState z)
  rw [sub_add_cancel] at ha
  change |faceValue v (Input.theta v) (zeta N) s.toCubeState z|≤36 at hf
  linarith

theorem matrix_entries (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) (s : WalkState N)
    (i j : Fin (count s.coeff)) :
    |KSFullManuscriptHessian.weighted (liveWeights s)
      (KSFullManuscriptHessian.matrixReport (faceReport O v s) 0 (queryStep v)) i j|≤
      (RuntimeBudgets.entryCap N d : ℝ) := by
  have hρ := rho_pos (Input.labels_pos v hd hp)
  have ht := queryStep_pos v hd hp
  have htr : queryStep v≤rho N/16 := min_le_left _ _
  have he := KSStencilMatrixBounds.full_matrixReport_abs (faceReport O v s) ht.le
    (show 2*queryStep v≤rho N/2 by linarith) (by norm_num : (0:ℝ)≤37)
    (fun z hz => faceReport_abs O v hd hp s z (by linarith))
  have hw := NormalizedHessian.sourceWeight_sq_le_two
    (zeta_pos (Input.labels_pos v hd hp)).le (livePositions s.coeff)
    (fun k => (livePositions_interior s.coeff k).le)
  have hh := NormalizedHessian.weighted_entry_error (liveWeights s) hw
    (A:=KSFullManuscriptHessian.matrixReport (faceReport O v s) 0 (queryStep v))
    (B:=0) (by positivity : (0:ℝ)≤4*37/queryStep v^2)
    (fun k l => by simpa using he k l) i j
  simp only [KSFullManuscriptHessian.weighted,Matrix.zero_apply,mul_zero,zero_mul,
    zero_div,sub_zero] at hh
  change |KSFullManuscriptHessian.weighted (liveWeights s)
    (KSFullManuscriptHessian.matrixReport (faceReport O v s) 0 (queryStep v)) i j|≤_ at hh
  apply hh.trans
  have hq := mul_le_mul_of_nonneg_left (queryStep_inverse_square_le v hd hp)
    (by norm_num : (0:ℝ)≤148)
  simp only [RuntimeBudgets.entryCap,Nat.cast_mul,Nat.cast_ofNat,
    RuntimeBudgets.cast_queryInverseSquareCap,div_eq_mul_inv]
  nlinarith

end SeamlessKS.RuntimeMagnitude
