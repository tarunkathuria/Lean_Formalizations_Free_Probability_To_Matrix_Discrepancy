import MatrixSpencer.KSManuscriptPolynomialTaylorBounds
import MatrixSpencer.KSFullManuscriptQueries
import MatrixSpencer.KSEighthHessianQueries

/-!
# Polynomial magnitudes of the actual KS value reports

These bounds use the real trace-one density objective on the whole relevant
cube, including retained eighth-cube owners and the actual full-cube debit.
They do not assume a value oracle or a source eigenvalue bound.
-/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSManuscriptReportMagnitudeBounds
open KSManuscriptPolynomialTaylorBounds KSManuscriptInputBudgetBounds
open KSOwnerInputBounds KSPotentialModels
set_option maxHeartbeats 1600000

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}

theorem owner_abs_le_input [Nonempty n] (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {θ R κ : ℝ}
    (hθ : 0≤θ) (hR : ‖H‖≤R)
    (hκ : (∑i,(covarianceKraus A C i)ᴴ*covarianceKraus A C i)≤κ•(1:Matrix n n ℂ)) :
    |ownerPotential H A C θ|≤R+2*Real.sqrt κ+2*θ*Real.sqrt (Fintype.card n:ℝ) := by
  rw [ownerPotential_eq_densityPotential H A hA hC]
  obtain ⟨S,hS,he⟩ := exists_densityPotential_eq H (covarianceKraus A C) θ
  rw [he]
  apply abs_le.mpr
  constructor
  · have hn := realTrace_mul_density_le_norm hH.neg hS
    simp only [Matrix.neg_mul,realTrace_neg,norm_neg] at hn
    have hf := fidelity_nonneg S (krausChannel (covarianceKraus A C) S)
    have hs := realTrace_nonneg (CFC.sqrt_nonneg S).posSemidef
    have hs' := mul_nonneg hθ hs
    have hr' := mul_nonneg hθ (Real.sqrt_nonneg (Fintype.card n:ℝ))
    unfold densityObjective
    linarith [Real.sqrt_nonneg κ]
  · exact KSOptimizerFloor.objective_le_input_bound H hH _ hθ hR hκ hS

theorem abs_report_le {report value V ν : ℝ} (h : |report-value|≤ν) (hv : |value|≤V) :
    |report|≤V+ν := by
  have ha := abs_add_le (report-value) value
  rw [sub_add_cancel] at ha
  linarith

variable {N d : ℕ}

private theorem sqrt_spin_le (v : Fin N → Fin d → ℂ)
    (hp : (∑i,KSRankOne.atom (v i))=1) :
    Real.sqrt (KSDebitUniformFloor.spinBudget v)≤1+1152*(N:ℝ) := by
  have hn := Nat.cast_nonneg (α := ℝ) N
  exact (Real.sqrt_le_iff).mpr ⟨by positivity,by nlinarith [spinBudget_le v hp]⟩

/-- Every full-cube state, with its actual stored debit, has uniformly
polynomial potential magnitude at the original-input tuning. -/
theorem full_statePotential_abs (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) {x : Fin N → ℝ} (hx : x∈ksCube 1) :
    |KSDebitPreparation.statePotential v
      (Real.sqrt (KSEighthManuscriptPreprocess.epsilon v))
      (Real.sqrt (KSEighthManuscriptPreprocess.epsilon v)/(N:ℝ))
      (ksRegularizerScale (KSEighthManuscriptPreprocess.epsilon v) (Fin d)) x|≤sizeBase N d := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  let δ := Real.sqrt (KSEighthManuscriptPreprocess.epsilon v)
  let η := δ/(N:ℝ)
  let θ := ksRegularizerScale (KSEighthManuscriptPreprocess.epsilon v) (Fin d)
  have hδ : 0≤δ := Real.sqrt_nonneg _
  have hη : 0≤η := by unfold η; positivity
  have hθ : 0<θ := ksRegularizerScale_pos (KSEighthManuscriptPreprocess.epsilon_pos v hd hp)
  have hdebit := KSDebitBudget.debit_posSemidef _ (fun i => KSRankOne.atom_posSemidef (v i)) hδ hη x
  have hH := KSDebitCenter.center_isHermitian_of_posSemidef
    (center_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)) x) hdebit
  have hR := KSDebitUniformFloor.fixed_center_norm v hδ hη hdebit
    (KSDebitUniformFloor.debit_le_scalar v hδ hη x) hx
  have hc := naturalOwners_nonneg (by norm_num : (0:ℝ)≤64) le_rfl hx
  have hC := KSSpinSource.coefficientCovariance_posSemidef hc
  have hk := KSDebitUniformFloor.spin_kraus_budget v _ hc
    (fun i => by unfold naturalOwners; nlinarith [sq_nonneg (x i)])
  have hb := owner_abs_le_input _ hH _
    (KSSpinSource.family_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i))) hC hθ.le hR hk
  have he := ksRegularizerScale_budget (n := Fin d) (KSEighthManuscriptPreprocess.epsilon v)
  have hδ1 : δ≤1 := by
    simpa only [δ,Real.sqrt_one] using Real.sqrt_le_sqrt (KSEighthManuscriptPreprocess.epsilon_le_one v hd hp)
  have hRc := actual_centerRadius_le v hd hp
  have hs := sqrt_spin_le v hp
  change |KSDebitPreparation.statePotential v δ η θ x|≤sizeBase N d
  change |KSDebitPreparation.statePotential v δ η θ x|≤_ at hb
  change 2*θ*Real.sqrt (Fintype.card (Fin d ⊕ Fin d):ℝ)=2*δ at he
  unfold sizeBase
  have hn := Nat.cast_nonneg (α := ℝ) N
  have hd0 := Nat.cast_nonneg (α := ℝ) d
  linarith

theorem full_stateReport_abs (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) {x : Fin N → ℝ} (hx : x∈ksCube 1)
    {ν : ℝ} (hν : 0<ν) :
    |KSFullManuscriptDebitValue.stateReport v
      (Real.sqrt (KSEighthManuscriptPreprocess.epsilon v))
      (Real.sqrt (KSEighthManuscriptPreprocess.epsilon v)/(N:ℝ))
      (ksRegularizerScale (KSEighthManuscriptPreprocess.epsilon v) (Fin d)) hd ν x|≤sizeBase N d+ν := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hθ := ksRegularizerScale_pos (n := Fin d) (KSEighthManuscriptPreprocess.epsilon_pos v hd hp)
  exact abs_report_le (KSFullManuscriptDebitValue.stateReport_accuracy v _ _ hθ.le hν hd hx)
    (full_statePotential_abs v hd hp hx)

private theorem independent_krausBudget_le (v : Fin N → Fin d → ℂ)
    (hp : (∑i,KSRankOne.atom (v i))=1) (c : Fin N → ℝ)
    (hc : ∀i,0≤c i) (hc64 : ∀i,c i≤64) :
    krausBudget (KSIndependentSource.family (fun i => KSRankOne.atom (v i)))
      (KSIndependentSource.coefficientCovariance c)≤1+512*(N:ℝ) := by
  unfold krausBudget KSIndependentSource.coefficientCovariance
  simp only [Matrix.diagonal_apply,abs_ite,abs_zero,ite_mul,zero_mul,
    Finset.sum_ite_eq,Finset.mem_univ,if_true]
  apply add_le_add_left
  calc _ ≤ ∑_j : Fin N × Bool, (256:ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        have hb : matrixBound (KSIndependentSource.family (fun i => KSRankOne.atom (v i)) j)≤2 :=
          independent_bound_le_two v hp j
        have hb0 := (matrixBound_pos (KSIndependentSource.family (fun i => KSRankOne.atom (v i)) j)).le
        rw [abs_of_nonneg (hc j.1)]
        calc _ ≤ 64*2*2 := by gcongr; exact hc64 j.1
          _ = (256:ℝ) := by norm_num
    _ = _ := by simp; ring

/-- Retaining any mask of owners of size at most 64 preserves the polynomial
potential bound throughout the whole cube, including every stencil point. -/
theorem eighth_commonPotential_abs (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) {x : Fin N → ℝ} (hx : x∈ksCube 1)
    (c : Fin N → ℝ) (hc : ∀i,0≤c i) (hc64 : ∀i,c i≤64) :
    |commonPotential (fun i => KSRankOne.atom (v i))
      (ksRegularizerScale (KSEighthManuscriptPreprocess.epsilon v) (Fin d)) x c|≤sizeBase N d := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  let θ := ksRegularizerScale (KSEighthManuscriptPreprocess.epsilon v) (Fin d)
  have hθ : 0<θ := ksRegularizerScale_pos (KSEighthManuscriptPreprocess.epsilon_pos v hd hp)
  have hH := signedLift_isHermitian (center_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)) x)
  have hR : ‖signedLift (center (fun i => KSRankOne.atom (v i)) x)‖≤KSDebitUniformFloor.atomBudget v := by
    rw [signedLift_norm (center_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)) x)]
    exact KSDebitUniformFloor.signed_sum_norm_le_atomBudget v x (fun i => abs_le.mpr ⟨hx.1 i,hx.2 i⟩)
  have hA := KSIndependentSource.family_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i))
  have hC := KSIndependentSource.coefficientCovariance_posSemidef hc
  have hk := (covarianceKraus_budget _ hA hC).trans
    (smul_le_smul_of_nonneg_right (independent_krausBudget_le v hp c hc hc64) zero_le_one)
  have hb := owner_abs_le_input _ hH _ hA hC hθ.le hR hk
  have he := ksRegularizerScale_budget (n := Fin d) (KSEighthManuscriptPreprocess.epsilon v)
  have hδ1 : Real.sqrt (KSEighthManuscriptPreprocess.epsilon v)≤1 := by
    simpa using Real.sqrt_le_sqrt (KSEighthManuscriptPreprocess.epsilon_le_one v hd hp)
  have hn := Nat.cast_nonneg (α := ℝ) N
  have hd0 := Nat.cast_nonneg (α := ℝ) d
  have hs : Real.sqrt (1+512*(N:ℝ))≤1+512*(N:ℝ) :=
    (Real.sqrt_le_iff).mpr ⟨by positivity,by nlinarith⟩
  have hR' := atomBudget_le v hp
  unfold commonPotential
  rw [KSCommonSource.potential_eq_independent _ _ (fun i => KSRankOne.atom_isHermitian (v i)) hc hθ]
  unfold sizeBase
  change 2*θ*Real.sqrt (Fintype.card (Fin d ⊕ Fin d):ℝ)=_ at he
  linarith

theorem eighth_ownerReport_abs (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) {x : Fin N → ℝ} (hx : x∈ksCube 1)
    (c : Fin N → ℝ) (hc : ∀i,0≤c i) (hc64 : ∀i,c i≤64) {ν : ℝ} (hν : 0<ν) :
    |KSEighthNumericalValue.ownerReport v
      (ksRegularizerScale (KSEighthManuscriptPreprocess.epsilon v) (Fin d)) hd c ν x|≤sizeBase N d+ν := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hθ := ksRegularizerScale_pos (n := Fin d) (KSEighthManuscriptPreprocess.epsilon_pos v hd hp)
  exact abs_report_le (KSEighthNumericalValue.ownerReport_accuracy v hθ hν hd c hc x)
    (eighth_commonPotential_abs v hd hp hx c hc hc64)

theorem eighth_retainedReport_abs (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) {x : Fin N → ℝ} (hx : x∈ksCube 1)
    (L : Finset (Fin N)) {ν : ℝ} (hν : 0<ν) :
    |KSEighthNumericalValue.retainedReport v
      (ksRegularizerScale (KSEighthManuscriptPreprocess.epsilon v) (Fin d)) hd L ν x|≤sizeBase N d+ν := by
  apply eighth_ownerReport_abs v hd hp hx _
    (maskedOwners_nonneg (by norm_num) le_rfl hx L) _ hν
  intro i
  unfold maskedOwners naturalOwners
  split_ifs <;> nlinarith [sq_nonneg (x i)]

private theorem full_valueTolerance_le_one {N : ℕ} (hN : 0<N) {δ M : ℝ}
    (hδ : 0<δ) (hδ1 : δ≤1) (hM : 0<M) :
    KSFullManuscriptParameters.valueTolerance N δ M≤1 := by
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hk0 := (KSFullManuscriptParameters.curvatureTolerance_pos hN hδ).le
  have hk : KSFullManuscriptParameters.curvatureTolerance N δ≤1 := by
    unfold KSFullManuscriptParameters.curvatureTolerance
    apply (div_le_one (by linarith : (0:ℝ)<100*N)).mpr
    linarith
  have ht0 := (KSFullManuscriptParameters.queryStep_pos hN hδ hM).le
  have ht := KSFullManuscriptQueries.queryStep_le_quarter N (M := M) hδ.le
  have ht2 : (KSFullManuscriptParameters.queryStep N δ M)^2≤1 := by nlinarith
  have hm := mul_le_mul hk ht2 (sq_nonneg (KSFullManuscriptParameters.queryStep N δ M)) (by norm_num : (0:ℝ)≤1)
  unfold KSFullManuscriptParameters.valueTolerance
  apply (div_le_one (by linarith : (0:ℝ)<16*N)).mpr
  nlinarith

/-- This covers all full-cube diagonal and mixed stencil queries at once.
Any positive mesh budget is allowed; the actual one is already proved positive. -/
theorem full_faceReport_abs (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) {x : Fin N → ℝ} (hx : x∈ksCube 1)
    (hmargin : ∀i,|x i|<1 → Real.sqrt (KSEighthManuscriptPreprocess.epsilon v)≤1-|x i|)
    {M : ℝ} (hM : 0<M) (z : KSNumericalHessian.Space (KSLiveEnumeration.count x))
    (hz : ‖z‖≤Real.sqrt (KSEighthManuscriptPreprocess.epsilon v)/2) :
    |KSFullManuscriptQueries.faceReport v
      (Real.sqrt (KSEighthManuscriptPreprocess.epsilon v))
      (Real.sqrt (KSEighthManuscriptPreprocess.epsilon v)/(N:ℝ))
      (ksRegularizerScale (KSEighthManuscriptPreprocess.epsilon v) (Fin d)) hd M x z|≤sizeBase N d+1 := by
  have hn := (KSEighthManuscriptPreprocess.count_pos v hd hp).trans_le (KSEighthManuscriptPreprocess.count_le v)
  have hδ := Real.sqrt_pos.mpr (KSEighthManuscriptPreprocess.epsilon_pos v hd hp)
  have hδ1 : Real.sqrt (KSEighthManuscriptPreprocess.epsilon v)≤1 := by
    simpa using Real.sqrt_le_sqrt (KSEighthManuscriptPreprocess.epsilon_le_one v hd hp)
  have hy := KSFullManuscriptLiveCoordinates.face_mem_cube hx z hmargin (by linarith)
  have hν := KSFullManuscriptParameters.valueTolerance_pos hn hδ hM
  exact (full_stateReport_abs v hd hp hy hν).trans
    (add_le_add_left (full_valueTolerance_le_one hn hδ hδ1 hM) _)

private theorem eighth_queryTolerance_le_one (v : Fin N → Fin d → ℂ)
    {θ κ : ℝ} (hθ : 0<θ) (hκ : 0<κ) (hκ1 : κ≤1) (hd : 0<d)
    (x : Fin N → ℝ) (hk : 0<KSEighthLiveEnumeration.count x) :
    KSEighthHessianQueries.queryTolerance v θ κ x≤1 := by
  have hkn : (1:ℝ)≤KSEighthLiveEnumeration.count x := by exact_mod_cast hk
  have ht0 := (KSEighthHessianQueries.queryMesh_pos v hθ hκ hd x hk).le
  have ht := KSEighthHessianQueries.queryMesh_le v θ κ x
  have ht2 : (KSEighthHessianQueries.queryMesh v θ κ x)^2≤1 := by nlinarith
  have hm := mul_le_mul hκ1 ht2 (sq_nonneg (KSEighthHessianQueries.queryMesh v θ κ x)) (by norm_num : (0:ℝ)≤1)
  unfold KSEighthHessianQueries.queryTolerance KSNumericalHessian.valueTolerance
  apply (div_le_one (by linarith : (0:ℝ)<4*KSEighthLiveEnumeration.count x)).mpr
  change κ*(KSEighthHessianQueries.queryMesh v θ κ x)^2≤_
  nlinarith

/-- Every retained eighth-cube face query has a polynomial report magnitude,
uniformly over its live mask and independent of source conditioning. -/
theorem eighth_faceReport_abs (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) {x : Fin N → ℝ} (hx : x∈ksCube (1/8))
    (hk : 0<KSEighthLiveEnumeration.count x) {κ : ℝ} (hκ : 0<κ) (hκ1 : κ≤1)
    (z : KSEighthFacePotential.Space x) (hz : ‖z‖≤1/16) :
    |KSEighthHessianQueries.faceReport v
      (ksRegularizerScale (KSEighthManuscriptPreprocess.epsilon v) (Fin d)) κ hd x z|≤sizeBase N d+1 := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hθ := ksRegularizerScale_pos (n := Fin d) (KSEighthManuscriptPreprocess.epsilon_pos v hd hp)
  have hyq := KSEighthHessianQueries.query_ball_cube hx z hz
  have hy : KSEighthLiveCoordinates.face x z∈ksCube 1 := by
    constructor <;> intro i
    · linarith [hyq.1 i]
    · linarith [hyq.2 i]
  have hν := KSEighthHessianQueries.queryTolerance_pos v hθ hκ hd x hk
  exact (eighth_retainedReport_abs v hd hp hy _ hν).trans
    (add_le_add_left (eighth_queryTolerance_le_one v hθ hκ hκ1 hd x hk) _)

end MatrixSpencer.KSManuscriptReportMagnitudeBounds
