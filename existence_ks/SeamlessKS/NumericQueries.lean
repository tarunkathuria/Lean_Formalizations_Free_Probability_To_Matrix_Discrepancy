import SeamlessKS.LivePotential
import SeamlessKS.Walk

/-! Every Hessian stencil value is the actual SDP report at a point of the
current cube face. Its error is proved from the general affine SDP solver. -/
open Matrix Set
open scoped BigOperators Topology Matrix.Norms.L2Operator
noncomputable section
namespace SeamlessKS.NumericQueries
open MatrixSpencer SeamlessKS.State SeamlessKS.StatePotential SeamlessKS.LivePotential
open SeamlessKS.Parameters SeamlessKS.Walk
open MatrixSpencer.KSLiveEnumeration (count liveEquiv)
open MatrixSpencer.KSFullManuscriptLiveCoordinates (face)
open MatrixSpencer.KSNumericalHessian (coordinate)
variable {N d : ℕ}

theorem liveCount_le (x : Fin N → ℝ) : count x≤N := by
  have hh := Fintype.card_le_of_injective
    (fun i : Fin (count x) => (liveEquiv x i).val)
    (by intro i j hij; exact (liveEquiv x).injective (Subtype.ext hij))
  simpa only [Fintype.card_fin] using hh

theorem faceReport_accuracy [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (z : EuclideanSpace ℝ (Fin (count s.coeff))) (hz : ‖z‖<rho N) :
    |faceReport O v s z-faceValue v (Input.theta v) (zeta N) s.toCubeState z|≤
      hessianAccuracy v := by
  exact Value.report_accuracy O v 0 (Input.theta_pos v hd hp)
    (hessianAccuracy_pos v hd hp) (face s.coeff z)
    (KSFullManuscriptLiveCoordinates.face_mem_cube s.cube z
      (fun i hi => (s.margin i hi).le) hz)

theorem coordinate_norm {m : ℕ} (i : Fin m) : ‖coordinate i‖=1 := by
  simp [coordinate]

theorem stencil_norm {m : ℕ} {ρ t : ℝ} (hρ : 0<ρ) (ht : 0≤t) (htr : t≤ρ/16)
    (w : EuclideanSpace ℝ (Fin m)) (hw : ‖w‖≤2) : ‖t • w‖<ρ := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht]
  have hh := mul_le_mul htr hw (norm_nonneg _) (by positivity : 0≤ρ/16)
  nlinarith

theorem queryAccuracy [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) :
    KSFullManuscriptHessian.QueryAccuracy
      (faceValue v (Input.theta v) (zeta N) s.toCubeState) (faceReport O v s) 0
      (queryStep v) (hessianAccuracy v) := by
  have hN := Input.labels_pos v hd hp
  have hr := rho_pos hN
  have ht := queryStep_pos v hd hp
  have htr : queryStep v≤rho N/16 := min_le_left _ _
  have ha (z : EuclideanSpace ℝ (Fin (count s.coeff))) (hz : ‖z‖<rho N) :=
    faceReport_accuracy O v hd hp s z hz
  have hq (w : EuclideanSpace ℝ (Fin (count s.coeff))) (hw : ‖w‖≤2) :
      ‖queryStep v • w‖<rho N := stencil_norm hr ht.le htr w hw
  have he (i : Fin (count s.coeff)) : ‖coordinate i‖≤2 := by rw [coordinate_norm]; norm_num
  have hplus (i j : Fin (count s.coeff)) : ‖coordinate i+coordinate j‖≤2 :=
    (norm_add_le _ _).trans (by rw [coordinate_norm,coordinate_norm]; norm_num)
  have hminus (i j : Fin (count s.coeff)) : ‖coordinate i-coordinate j‖≤2 :=
    (norm_sub_le _ _).trans (by rw [coordinate_norm,coordinate_norm]; norm_num)
  refine ⟨ha 0 (by simpa using hr),?_,?_⟩
  · intro i
    constructor
    · simpa only [zero_add] using ha _ (hq _ (he i))
    · simpa only [zero_sub,neg_smul] using ha (-queryStep v • coordinate i)
        (by rw [neg_smul,norm_neg]; exact hq _ (he i))
  · intro i j hij
    refine ⟨?_,?_,?_,?_⟩
    · simpa only [zero_add] using ha _ (hq _ (hplus i j))
    · simpa only [zero_add] using ha _ (hq _ (hminus i j))
    · simpa only [zero_sub,neg_smul] using ha (-queryStep v • (coordinate i-coordinate j))
        (by rw [neg_smul,norm_neg]; exact hq _ (hminus i j))
    · simpa only [zero_sub,neg_smul] using ha (-queryStep v • (coordinate i+coordinate j))
        (by rw [neg_smul,norm_neg]; exact hq _ (hplus i j))

end SeamlessKS.NumericQueries
