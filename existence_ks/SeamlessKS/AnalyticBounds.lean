import SeamlessKS.WalkDrift
import SeamlessKS.NumericalRegularityEnvelope

/-! Closing the numerical-regularity interface from the original Parseval
input. Every queried or moved point retains a definite live-coordinate margin;
the generic actual-curve estimate therefore applies to the current face. -/
open Matrix Set
open scoped BigOperators Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace SeamlessKS.AnalyticBounds
open MatrixSpencer SeamlessKS.State SeamlessKS.StatePotential SeamlessKS.LivePotential
open SeamlessKS.Parameters SeamlessKS.Walk
open MatrixSpencer.KSLiveEnumeration (count liveEquiv)
open MatrixSpencer.KSFullManuscriptLiveCoordinates (face)
open MatrixSpencer.KSNumericalHessian (coordinate)
variable {N d : ℕ}
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}
set_option maxHeartbeats 1200000

theorem live_subparseval (v : Fin N → Fin d → ℂ)
    (hp : ∑ i,KSRankOne.atom (v i)=1) (x : Fin N → ℝ) :
    (∑ i,KSRankOne.atom (liveVectors v x i))≤1 := by
  classical
  have he := (liveEquiv x).sum_comp (fun i => KSRankOne.atom (v i))
  change (∑ i,KSRankOne.atom (v (liveEquiv x i)))≤1
  rw [he,←hp]
  have hc := Fintype.sum_subtype_add_sum_subtype (fun i => |x i|<1)
    (fun i => KSRankOne.atom (v i))
  have hn : (0 : Matrix (Fin d) (Fin d) ℂ) ≤
      ∑ i : {j : Fin N // ¬ |x j|<1}, KSRankOne.atom (v i) :=
    Finset.sum_nonneg (fun i _ => (KSRankOne.atom_posSemidef (v i)).nonneg)
  rw [←hc]
  exact le_add_of_nonneg_right hn

theorem line_margin (s : WalkState N) (hρ : 0<rho N)
    (w : EuclideanSpace ℝ (Fin (count s.coeff))) (hw : ∀ i, |w i|≤2)
    (t : ℝ) (ht : |t|≤rho N/16) (i : Fin (count s.coeff)) :
    |livePositions s.coeff i+t*w i|≤1-rho N/2 := by
  have hm := s.margin (liveEquiv s.coeff i) (liveEquiv s.coeff i).property
  change rho N<1-|livePositions s.coeff i| at hm
  have hd := mul_le_mul ht (hw i) (abs_nonneg _) (by positivity : 0≤rho N/16)
  rw [←abs_mul] at hd
  have ha := abs_add_le (livePositions s.coeff i) (t*w i)
  linarith

theorem line_cube (s : WalkState N) (hρ : 0<rho N)
    (w : EuclideanSpace ℝ (Fin (count s.coeff))) (hw : ∀ i, |w i|≤2)
    (t : ℝ) (ht : |t|≤rho N/16) : face s.coeff (t • w)∈ksCube 1 := by
  have hb (j : Fin N) : |face s.coeff (t • w) j|≤1 := by
    by_cases hj : |s.coeff j|<1
    · let i := (liveEquiv s.coeff).symm ⟨j,hj⟩
      have he : (liveEquiv s.coeff i).val=j := congrArg Subtype.val
        ((liveEquiv s.coeff).apply_symm_apply ⟨j,hj⟩)
      rw [←he,LivePotential.face_live]
      simp only [PiLp.smul_apply,smul_eq_mul]
      have hh := line_margin s hρ w hw t ht i
      linarith
    · rw [KSFullManuscriptLiveCoordinates.face_dead s.coeff _ j hj]
      exact coeff_abs_le s.toCubeState j
  exact ⟨fun j => (abs_le.mp (hb j)).1,fun j => (abs_le.mp (hb j)).2⟩

theorem curve_center (v : Fin N → Fin d → ℂ) (s : WalkState N)
    (w : EuclideanSpace ℝ (Fin (count s.coeff))) (t : ℝ) :
    KSDebitLocalState.curveCenter (center v s.toCubeState) (liveVectors v s.coeff)
      (fun i => w i) t =
    KSDebitCenter.center (StatePotential.signedSum v (face s.coeff (t • w)))
      (debit v s.toCubeState) := by
  rw [center_face]
  unfold KSDebitLocalState.curveCenter
  rw [Finset.smul_sum]
  simp only [PiLp.smul_apply,smul_eq_mul,MulAction.mul_smul,KSSpinLocalState.atoms]

theorem curve_center_norm (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : ∑ i,KSRankOne.atom (v i)=1) (s : WalkState N)
    (w : EuclideanSpace ℝ (Fin (count s.coeff))) (hw : ∀ i, |w i|≤2)
    (t : ℝ) (ht : |t|≤rho N/16) :
    ‖KSDebitLocalState.curveCenter (center v s.toCubeState) (liveVectors v s.coeff)
      (fun i => w i) t‖≤2 := by
  rw [curve_center]
  have hc := line_cube s (rho_pos (Input.labels_pos v hd hp)) w hw t ht
  exact StateBounds.actual_center_norm_le_two v hd hp _
    (fun i => abs_le.mpr ⟨hc.1 i,hc.2 i⟩)
    (debit_bounds v hp s.toCubeState).1 (debit_bounds v hp s.toCubeState).2

theorem radius_eq (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : ∑ i,KSRankOne.atom (v i)=1) :
    NumericalRegularity.radius (NumericalRegularityEnvelope.densityFloor (Input.theta v))
      (rho N/2) (zeta N)=complexRadius v := by
  have hr := rho_pos (Input.labels_pos v hd hp)
  have hzhalf : zeta N≤rho N/2 := by unfold zeta outwardStep; linarith
  have hzfull : zeta N≤rho N := by linarith
  unfold NumericalRegularity.radius complexRadius NumericalRegularityEnvelope.densityFloor densityFloor
  simp only [min_assoc,min_eq_right hzhalf,min_eq_right hzfull]

theorem derivativeCap_le (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : ∑ i,KSRankOne.atom (v i)=1) :
    NumericalRegularityEnvelope.derivativeCap (n := Fin d) (rho N/2) (zeta N) (Input.theta v)≤
      derivativeBudget v := by
  have hX : NumericalRegularityParseval.jointCap (n := Fin d)
      (NumericalRegularityEnvelope.densityFloor (Input.theta v)) (rho N/2) (zeta N)=
      jointDerivativeBound v := by
    unfold NumericalRegularityParseval.jointCap jointDerivativeBound objectiveBound
    rw [radius_eq v hd hp]
    simp only [Fintype.card_sum,Fintype.card_fin,Nat.cast_add]
    congr 2
    ring
  unfold NumericalRegularityEnvelope.derivativeCap
  dsimp only
  rw [hX]
  unfold derivativeBudget coercivity
  linarith

theorem face_line_eq (v : Fin N → Fin d → ℂ) (s : WalkState N)
    (w : EuclideanSpace ℝ (Fin (count s.coeff))) :
    (fun t : ℝ => faceValue v (Input.theta v) (zeta N) s.toCubeState (t • w))=
      SmoothPotential.curvePotential (center v s.toCubeState) (liveVectors v s.coeff)
        (Input.theta v) (zeta N) (livePositions s.coeff) (fun i => w i) := by
  funext t
  rw [faceValue_eq_restricted,restrictedValue_curve]

theorem face_line_bounds [Nonempty (Fin d)] (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : ∑ i,KSRankOne.atom (v i)=1) (s : WalkState N)
    (w : EuclideanSpace ℝ (Fin (count s.coeff))) (hw : ∀ i, |w i|≤2)
    (r : ℝ) (hr : r≤rho N/16) :
    ContDiffOn ℝ 4 (fun t : ℝ => faceValue v (Input.theta v) (zeta N) s.toCubeState (t • w))
      (Icc (-r) r) ∧
    ∀ t ∈ Icc (-r) r,
      |iteratedDeriv 4
        (fun q : ℝ => faceValue v (Input.theta v) (zeta N) s.toCubeState (q • w)) t|≤derivativeBudget v := by
  have hN := Input.labels_pos v hd hp
  have hρ := rho_pos hN
  have hζ := zeta_pos hN
  have hθ := Input.theta_pos v hd hp
  have hζone : zeta N≤1 := by
    have hh := rho_le_one v hd hp
    unfold zeta outwardStep
    linarith
  have hM := KSDebitCenter.center_isHermitian_of_posSemidef
    (StatePotential.signedSum_isHermitian v s.coeff) (debit_bounds v hp s.toCubeState).1
  have htbound (t : ℝ) (ht : t∈Icc (-r) r) : |t|≤rho N/16 :=
    (abs_le.mpr ht).trans hr
  rw [face_line_eq]
  constructor
  · intro t ht
    apply ContDiffAt.contDiffWithinAt
    apply (NumericalRegularityEnvelope.contDiffAt_curvePotential hζ hθ
      (center v s.toCubeState) hM (liveVectors v s.coeff) (livePositions s.coeff)
      (fun i => w i) t (fun i => ?_)).of_le
      (WithTop.coe_le_coe.mpr (show (4 : ℕ∞)≤⊤ from le_top))
    have hh := line_margin s hρ w hw t (htbound t ht) i
    linarith
  · intro t ht
    exact (NumericalRegularityEnvelope.curve_fourth_le hζ hζone (by positivity) hθ
      (StateBounds.original_regularizer_budget v hd hp) (center v s.toCubeState) hM
      (liveVectors v s.coeff) (live_subparseval v hp s.coeff) (livePositions s.coeff)
      (fun i => w i) t (line_margin s hρ w hw t (htbound t ht)) hw
      (curve_center_norm v hd hp s w hw t (htbound t ht))).trans (derivativeCap_le v hd hp)

theorem analyticBounds [Nonempty (Fin d)] (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : ∑ i,KSRankOne.atom (v i)=1) (s : WalkState N) : WalkDrift.AnalyticBounds v s := by
  have hM := (derivativeBudget_pos v hd hp).le
  have hcoord (i : Fin (count s.coeff)) (j : Fin (count s.coeff)) : |coordinate i j|≤1 := by
    have hh := PiLp.norm_apply_le (coordinate i) j
    simpa only [Real.norm_eq_abs,NumericQueries.coordinate_norm] using hh
  have hb (w : EuclideanSpace ℝ (Fin (count s.coeff))) (hw : ∀ i, |w i|≤2) :=
    face_line_bounds v hd hp s w hw (queryStep v) (min_le_left _ _)
  constructor
  · constructor
    · intro i
      simpa only [zero_add] using hb (coordinate i) (fun j => (hcoord i j).trans (by norm_num))
    · intro i j hij
      have hp := hb (coordinate i+coordinate j) (fun k => by
        change |coordinate i k+coordinate j k|≤2
        exact (abs_add_le _ _).trans (by linarith [hcoord i k,hcoord j k]))
      have hm := hb (coordinate i-coordinate j) (fun k => by
        change |coordinate i k-coordinate j k|≤2
        exact (abs_sub _ _).trans (by linarith [hcoord i k,hcoord j k]))
      refine ⟨?_,?_,?_,?_⟩
      · simpa only [zero_add] using hp.1
      · simpa only [zero_add] using hm.1
      · intro t ht
        simpa only [zero_add] using (hp.2 t ht).trans (by linarith : derivativeBudget v≤4*derivativeBudget v)
      · intro t ht
        simpa only [zero_add] using (hm.2 t ht).trans (by linarith : derivativeBudget v≤4*derivativeBudget v)
  · intro w hw
    apply face_line_bounds v hd hp s _ _ (movementStep v) (min_le_left _ _)
    intro i
    rw [NormalizedHessian.diagonalMap_apply,abs_mul]
    have hwi : |w i|≤1 := by simpa only [Real.norm_eq_abs,hw] using PiLp.norm_apply_le w i
    have hs := NormalizedHessian.sourceWeight_sq_le_two (zeta_pos (Input.labels_pos v hd hp)).le
      (livePositions s.coeff) (fun j => (livePositions_interior s.coeff j).le) i
    have hsw : |liveWeights s i|≤2 := by
      have he : liveWeights s i=NormalizedHessian.sourceWeight (zeta N) (livePositions s.coeff) i := rfl
      rw [he]
      nlinarith [sq_abs (NormalizedHessian.sourceWeight (zeta N) (livePositions s.coeff) i),
        abs_nonneg (NormalizedHessian.sourceWeight (zeta N) (livePositions s.coeff) i)]
    exact (mul_le_mul_of_nonneg_left hwi (abs_nonneg _)).trans (by simpa using hsw)

/-- The concrete walk's potential-plus-reserve drift, with all numerical regularity
derived from the original Parseval family. -/
theorem step_drift [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬Walk.terminal s) :
    (account v (Input.theta v) (zeta N) (Walk.step O v hd hp s false).toCubeState+
      account v (Input.theta v) (zeta N) (Walk.step O v hd hp s true).toCubeState)/2≤
    account v (Input.theta v) (zeta N) s.toCubeState+beta v*movementStep v^2 :=
  WalkDrift.step_drift O v hd hp s hs (analyticBounds v hd hp s)

end SeamlessKS.AnalyticBounds
