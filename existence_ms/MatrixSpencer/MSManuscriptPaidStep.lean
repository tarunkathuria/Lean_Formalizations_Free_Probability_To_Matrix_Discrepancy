import MatrixSpencer.CovariancePreparation
import MatrixSpencer.KSFirstDifference


open Matrix Set
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.MSManuscriptPaidStep
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def energy (w : ι → ℝ) : ℝ := ∑ i, w i ^ 2

def unitRank (w : ι → ℝ) : Matrix ι ι ℝ := (energy w)⁻¹ • realRankOne w

def cut (C : Matrix ι ι ℝ) (α : ℝ) (w : ι → ℝ) : Matrix ι ι ℝ := C-α • unitRank w

omit [DecidableEq ι] in
theorem energy_nonneg (w : ι → ℝ) : 0 ≤ energy w := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

omit [DecidableEq ι] in
theorem energy_eq_norm_sq (w : ι → ℝ) : energy w = ‖(WithLp.toLp 2 w : EuclideanSpace ℝ ι)‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [energy, Real.norm_eq_abs, sq_abs]

omit [DecidableEq ι] in
theorem energy_pos {w : ι → ℝ} (hw : w ≠ 0) : 0 < energy w := by
  rw [energy_eq_norm_sq]
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro h
  apply hw
  exact congrArg WithLp.ofLp h

omit [DecidableEq ι] in
theorem unitRank_posSemidef (w : ι → ℝ) : (unitRank w).PosSemidef :=
  (realRankOne_posSemidef w).smul (inv_nonneg.mpr (energy_nonneg w))

omit [DecidableEq ι] in
theorem realTrace_rank (w : ι → ℝ) : realTrace (realRankOne w) = energy w := by
  simpa only [energy_eq_norm_sq] using realTrace_rankOne_eq_norm_sq (WithLp.toLp 2 w : EuclideanSpace ℝ ι)

omit [DecidableEq ι] in
theorem unitRank_trace {w : ι → ℝ} (hw : w ≠ 0) : realTrace (unitRank w) = 1 := by
  rw [unitRank, realTrace_smul, realTrace_rank, inv_mul_cancel₀ (energy_pos hw).ne']

omit [DecidableEq ι] in
theorem cut_trace (C : Matrix ι ι ℝ) (α : ℝ) {w : ι → ℝ} (hw : w ≠ 0) :
    realTrace (cut C α w) = realTrace C-α := by
  rw [cut, realTrace_sub, realTrace_smul, unitRank_trace hw, mul_one]

theorem unitRank_le_projection {P : Matrix ι ι ℝ} (hP : P.IsHermitian) (hPP : P*P=P)
    {w : ι → ℝ} (hw : w ≠ 0) (hPw : P*ᵥw=w) : unitRank w ≤ P := by
  have h := (Matrix.le_iff.mp (realRankOne_le_energy w)).mul_mul_conjTranspose_same P
  rw [hP.eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hPP, realRankOne_congruence hP, hPw] at h
  have he : w ⬝ᵥ w = energy w := by simp only [dotProduct, energy, pow_two]
  rw [he] at h
  have hh := h.smul (inv_nonneg.mpr (energy_nonneg w))
  apply Matrix.le_iff.mpr
  convert hh using 1
  simp only [smul_sub, smul_smul, inv_mul_cancel₀ (energy_pos hw).ne', one_smul, unitRank]

omit [DecidableEq ι] in
theorem cut_le (C : Matrix ι ι ℝ) {α : ℝ} (hα : 0 ≤ α) (w : ι → ℝ) : cut C α w ≤ C :=
  sub_le_self C ((unitRank_posSemidef w).smul hα).nonneg

omit [DecidableEq ι] in
theorem cut_floor {P C : Matrix ι ι ℝ} {δ α : ℝ} {w : ι → ℝ}
    (hfloor : δ • P ≤ C) (hα : 0 ≤ α) (hwP : unitRank w ≤ P) :
    (δ-α) • P ≤ cut C α w := by
  apply Matrix.le_iff.mpr
  have hp := (Matrix.le_iff.mp hfloor).add ((Matrix.le_iff.mp hwP).smul hα)
  convert hp using 1
  unfold cut
  module

theorem cut_preserves_support {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    {δ α : ℝ} {w : ι → ℝ} (hdom : δ • unitRank w ≤ C)
    (hα : 0 ≤ α) (hsmall : α ≤ δ/2) :
    (cut C α w).PosSemidef ∧
      LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) (cut C α w)).toLinearMap =
      LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) C).toLinearMap :=
  shaving_posSemidef_and_range hC (unitRank_posSemidef w) hdom hα hsmall

omit [DecidableEq ι] in
/-- The supported unit-vector specialization used by the Jacobi top routine. -/
theorem unitRank_of_norm_one (u : EuclideanSpace ℝ ι) (hu : ‖u‖ = 1) :
    unitRank (WithLp.ofLp u) = realRankOne (WithLp.ofLp u) := by
  unfold unitRank
  rw [energy_eq_norm_sq]
  simp [hu]

/-- A prepared support floor makes the literal cut feasible and preserves it by half. -/
theorem cut_valid {P C : Matrix ι ι ℝ} (hP : P.PosSemidef) (hPP : P*P=P)
    (hC : C.PosSemidef) {δ α : ℝ} (hδ : 0 < δ) (hα : 0 ≤ α) (hsmall : α ≤ δ/2)
    (hfloor : δ • P ≤ C) {w : ι → ℝ} (hw : w ≠ 0) (hPw : P*ᵥw=w) :
    (cut C α w).PosSemidef ∧ cut C α w ≤ C ∧ (δ/2) • P ≤ cut C α w ∧
      LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) (cut C α w)).toLinearMap =
      LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) C).toLinearMap := by
  have hu := unitRank_le_projection hP.isHermitian hPP hw hPw
  have hdom : δ • unitRank w ≤ C := by
    apply le_trans _ hfloor
    apply Matrix.le_iff.mpr
    simpa only [smul_sub] using (Matrix.le_iff.mp hu).smul hδ.le
  have hv := cut_preserves_support hC hdom hα hsmall
  refine ⟨hv.1, cut_le C hα w, ?_, hv.2⟩
  apply le_trans _ (cut_floor hfloor hα hu)
  apply Matrix.le_iff.mpr
  have hp := hP.smul (show 0 ≤ δ-α-δ/2 by linarith)
  convert hp using 1
  module

/-- Actual Lagrange Taylor theorem, with only a one-sided second derivative cap. -/
theorem paid_drop (f : ℝ → ℝ) {α price M q : ℝ} (hα : 0 < α)
    (hf : ContDiffOn ℝ 2 f (Icc 0 α)) (hd : HasDerivAt f (-q) 0)
    (hsecond : ∀ u ∈ Ioo 0 α, iteratedDeriv 2 f u ≤ M)
    (hq : 7*price/8 ≤ q) (hstep : M*α ≤ price/2) :
    5*price*α/8 ≤ f 0-f α := by
  obtain ⟨u, hu, hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hα hf
  have hdw : derivWithin f (Icc 0 α) 0 = -q :=
    hd.hasDerivWithinAt.derivWithin ((uniqueDiffOn_Icc hα) 0 (left_mem_Icc.mpr hα.le))
  have hpoly : taylorWithinEval f 1 (Icc 0 α) 0 α = f 0-α*q := by
    rw [show (1:ℕ)=0+1 from rfl, taylorWithinEval_succ, taylor_within_zero_eval,
      iteratedDerivWithin_one, hdw]
    norm_num
    ring
  rw [hpoly] at hrem
  norm_num at hrem
  have hs := mul_le_mul_of_nonneg_right (hsecond u hu) (sq_nonneg α)
  have hqα := mul_le_mul_of_nonneg_right hq hα.le
  have hMα := mul_le_mul_of_nonneg_right hstep hα.le
  nlinarith

end MatrixSpencer.MSManuscriptPaidStep
