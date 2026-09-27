import MatrixSpencer.PositiveCovarianceSampler
import MatrixSpencer.FiniteProcessMoments
import MatrixSpencer.KSCubePreparation



open scoped BigOperators MatrixOrder

noncomputable section
namespace MatrixSpencer.KSSymmetricProgress

section InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem symmetric_norm_sq (x v : E) (h : ℝ) :
    (‖x + h • v‖ ^ 2 + ‖x - h • v‖ ^ 2) / 2 =
      ‖x‖ ^ 2 + h ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_add_sq_real, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem weighted_centered_norm_sq {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (v : Ω → E) (x : E) (h : ℝ)
    (hw : (∑ s, w s) = 1) (hv : (∑ s, w s • v s) = 0) :
    (∑ s, w s * ‖x + h • v s‖ ^ 2) =
      ‖x‖ ^ 2 + h ^ 2 * ∑ s, w s * ‖v s‖ ^ 2 := by
  have hcenter : (∑ s, w s • (h • v s)) = 0 := by
    simp_rw [smul_comm (w _) h]
    rw [← Finset.smul_sum, hv, smul_zero]
  rw [FiniteProcessMoments.weighted_norm_sq_add w (fun s => h • v s) x hw hcenter]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- The explicit uniform sampler that chooses an index and then either sign. -/
theorem uniform_symmetric_norm_sq {Ω : Type*} [Fintype Ω]
    (hcard : 0 < Fintype.card Ω) (v : Ω → E) (x : E) (h : ℝ) :
    (∑ s, (‖x + h • v s‖ ^ 2 + ‖x - h • v s‖ ^ 2)) /
        (2 * (Fintype.card Ω : ℝ)) =
      ‖x‖ ^ 2 + h ^ 2 * (∑ s, ‖v s‖ ^ 2) / (Fintype.card Ω : ℝ) := by
  have hp (s : Ω) : ‖x + h • v s‖ ^ 2 + ‖x - h • v s‖ ^ 2 =
      2 * ‖x‖ ^ 2 + 2 * h ^ 2 * ‖v s‖ ^ 2 := by
    linarith [symmetric_norm_sq x (v s) h]
  simp_rw [hp, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast hcard.ne'
  field_simp

end InnerProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Any finite implementation of the same centered covariance, including a
uniform signed LDL factor sampler, has this identical movement expectation. -/
theorem finite_covariance_mean_norm_sq {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (v : Ω → EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ ι) (h : ℝ) (Q : Matrix ι ι ℝ)
    (hw : (∑ s, w s) = 1) (hv : (∑ s, w s • v s) = 0)
    (hcov : (∑ s, w s • realRankOne (WithLp.ofLp (v s))) = Q) :
    (∑ s, w s * ‖x + h • v s‖ ^ 2) = ‖x‖ ^ 2 + h ^ 2 * realTrace Q := by
  rw [weighted_centered_norm_sq w v x h hw hv]
  have ht := congrArg realTrace hcov
  simp only [realTrace_sum, realTrace_smul, realTrace_rankOne_eq_norm_sq] at ht
  rw [ht]

/-- Exact one-step mean progress for the existing, explicitly defined sampler. -/
theorem covarianceSample_mean_norm_sq {Q : Matrix ι ι ℝ}
    (hQ : Q.PosSemidef) (htrace : 0 < realTrace Q)
    (x : EuclideanSpace ℝ ι) (h : ℝ) :
    (∑ s, covarianceSampleWeight hQ s *
      ‖x + h • covarianceSampleIncrement hQ s‖ ^ 2) =
      ‖x‖ ^ 2 + h ^ 2 * realTrace Q := by
  rw [weighted_centered_norm_sq _ _ _ _ (covarianceSampleWeight_sum hQ htrace)
    (covarianceSample_mean_zero hQ)]
  simp only [covarianceSample_norm_sq, ← Finset.sum_mul,
    covarianceSampleWeight_sum hQ htrace, one_mul]

/-- Removing zero-mass outcomes preserves the same progress identity. -/
theorem positive_covarianceSample_mean_norm_sq {Q : Matrix ι ι ℝ}
    (hQ : Q.PosSemidef) (htrace : 0 < realTrace Q)
    (x : EuclideanSpace ℝ ι) (h : ℝ) :
    (∑ s : PositiveCovarianceOutcome hQ, covarianceSampleWeight hQ s *
      ‖x + h • covarianceSampleIncrement hQ s‖ ^ 2) =
      ‖x‖ ^ 2 + h ^ 2 * realTrace Q := by
  rw [weighted_centered_norm_sq _ _ _ _ (positive_covarianceSample_weight_sum hQ htrace)
    (positive_covarianceSample_mean_zero hQ htrace)]
  simp only [covarianceSample_norm_sq, ← Finset.sum_mul,
    positive_covarianceSample_weight_sum hQ htrace, one_mul]

theorem range_coordinate_zero {Q : Matrix ι ι ℝ} {i : ι}
    (hrow : ∀ j, Q i j = 0) {v : EuclideanSpace ℝ ι}
    (hv : v ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) Q).toLinearMap) :
    v i = 0 := by
  rcases hv with ⟨u, rfl⟩
  change (∑ j, Q i j * u j) = 0
  simp only [hrow, zero_mul, Finset.sum_const_zero]

/-- A zero covariance row preserves that coordinate in every positive branch. -/
theorem covarianceSample_preserves_frozen {Q : Matrix ι ι ℝ}
    (hQ : Q.PosSemidef) {i : ι} (hrow : ∀ j, Q i j = 0)
    (x : EuclideanSpace ℝ ι) (h : ℝ) (s : PositiveCovarianceOutcome hQ) :
    (x + h • covarianceSampleIncrement hQ s) i = x i := by
  have hz := range_coordinate_zero hrow (positive_covarianceSample_mem_range hQ s)
  change x i + h * covarianceSampleIncrement hQ s i = x i
  rw [hz, mul_zero, add_zero]

/-- The covariance after multiplying each live coordinate by `sqrt (1-xᵢ²)`. -/
def scaledCovariance (x : ι → ℝ) (Q : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal (fun i => Real.sqrt (1 - x i ^ 2)) * Q *
    Matrix.diagonal (fun i => Real.sqrt (1 - x i ^ 2))

theorem scaledCovariance_posSemidef (x : ι → ℝ) {Q : Matrix ι ι ℝ}
    (hQ : Q.PosSemidef) : (scaledCovariance x Q).PosSemidef := by
  simpa [scaledCovariance] using hQ.mul_mul_conjTranspose_same
    (Matrix.diagonal (fun i => Real.sqrt (1 - x i ^ 2)))

theorem scaledCovariance_trace (x : ι → ℝ) (Q : Matrix ι ι ℝ)
    (hx : ∀ i, x i ^ 2 ≤ 1) :
    realTrace (scaledCovariance x Q) = ∑ i, (1 - x i ^ 2) * Q i i := by
  simp only [scaledCovariance, realTrace, Matrix.trace, Matrix.diag,
    Matrix.mul_diagonal, Matrix.diagonal_mul, RCLike.re_to_real]
  apply Finset.sum_congr rfl
  intro i _
  have hs := Real.sq_sqrt (sub_nonneg.mpr (hx i))
  calc
    _ = Real.sqrt (1 - x i ^ 2) ^ 2 * Q i i := by ring
    _ = _ := by rw [hs]

theorem scaledCovariance_trace_lower (x : ι → ℝ) {Q : Matrix ι ι ℝ}
    (hQ : Q.PosSemidef) {r : ℝ} (hr : 0 ≤ r)
    (hx : ∀ i, r ≤ 1 - x i ^ 2) :
    r * realTrace Q ≤ realTrace (scaledCovariance x Q) := by
  have hxone : ∀ i, x i ^ 2 ≤ 1 := fun i => by linarith [hx i]
  rw [scaledCovariance_trace x Q hxone]
  simp only [realTrace, Matrix.trace, Matrix.diag, RCLike.re_to_real]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hdiag : 0 ≤ Q i i := by
    simpa using hQ.2 (Pi.single i 1)
  exact mul_le_mul_of_nonneg_right (hx i) hdiag

theorem eighth_scaledCovariance_trace_lower (x : ι → ℝ)
    {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    (hx : ∀ i, |x i| ≤ 1 / 8)
    (hcard : 1 ≤ Fintype.card ι)
    (htrace : 3 * (Fintype.card ι : ℝ) / 4 ≤ realTrace Q) :
    1 / 2 ≤ realTrace (scaledCovariance x Q) := by
  have hscaled := scaledCovariance_trace_lower x hQ (r := 63 / 64) (by norm_num)
    (fun i => by
      have hi := abs_le.mp (hx i)
      nlinarith [sq_nonneg (x i - 1 / 8),
        mul_nonneg (by linarith : 0 ≤ 1 / 8 - x i) (by linarith : 0 ≤ 1 / 8 + x i)])
  have hcard' : 1 ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hcard
  linarith

theorem eighth_scaledCovariance_trace_lower_of_trace (x : ι → ℝ)
    {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    (hx : ∀ i, |x i| ≤ 1 / 8) (htrace : 3 / 4 ≤ realTrace Q) :
    1 / 2 ≤ realTrace (scaledCovariance x Q) := by
  have hscaled := scaledCovariance_trace_lower x hQ (r := 63 / 64) (by norm_num)
    (fun i => by
      have hi := abs_le.mp (hx i)
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1 / 8 - x i)
        (by linarith : 0 ≤ 1 / 8 + x i)])
  linarith

/-- The eighth-cube trace hypothesis yields actual mean progress of at least `h²/2`. -/
theorem eighth_covarianceSample_progress (x : EuclideanSpace ℝ ι)
    {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    (hx : ∀ i, |x i| ≤ 1 / 8)
    (hcard : 1 ≤ Fintype.card ι)
    (htrace : 3 * (Fintype.card ι : ℝ) / 4 ≤ realTrace Q) (h : ℝ) :
    ‖x‖ ^ 2 + h ^ 2 / 2 ≤
      ∑ s, covarianceSampleWeight (scaledCovariance_posSemidef (WithLp.ofLp x) hQ) s *
        ‖x + h • covarianceSampleIncrement
          (scaledCovariance_posSemidef (WithLp.ofLp x) hQ) s‖ ^ 2 := by
  have hp := eighth_scaledCovariance_trace_lower (WithLp.ofLp x) hQ hx hcard htrace
  rw [covarianceSample_mean_norm_sq _ (by linarith) x h]
  nlinarith [sq_nonneg h]

/-- Coordinate scaling preserves all zero rows, including every frozen coordinate. -/
theorem scaledCovariance_row_zero (x : ι → ℝ) {Q : Matrix ι ι ℝ}
    {i : ι} (hrow : ∀ j, Q i j = 0) : ∀ j, scaledCovariance x Q i j = 0 := by
  intro j
  simp [scaledCovariance, Matrix.mul_diagonal, Matrix.diagonal_mul, hrow]

section Snapping
variable {N : ℕ}

theorem energy_eq_norm_sq (x : Fin N → ℝ) :
    KSCubePreparation.energy x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [KSCubePreparation.energy, Real.norm_eq_abs, sq_abs,
    PiLp.toLp_apply]

/-- Actual positive-probability children, followed by the defined outward snap. -/
theorem covarianceSample_snap_energy_progress {Q : Matrix (Fin N) (Fin N) ℝ}
    (hQ : Q.PosSemidef) (htrace : 0 < realTrace Q)
    (x : Fin N → ℝ) (h a ρ : ℝ)
    (hchild : ∀ s : PositiveCovarianceOutcome hQ,
      (fun i => x i + h * covarianceSampleIncrement hQ s i) ∈ ksCube a) :
    KSCubePreparation.energy x + h ^ 2 * realTrace Q ≤
      ∑ s : PositiveCovarianceOutcome hQ, covarianceSampleWeight hQ s *
        KSCubePreparation.energy (KSCubePreparation.snap a ρ
          (fun i => x i + h * covarianceSampleIncrement hQ s i)) := by
  have hmean := positive_covarianceSample_mean_norm_sq hQ htrace
    (WithLp.toLp 2 x) h
  have heq : (∑ s : PositiveCovarianceOutcome hQ, covarianceSampleWeight hQ s *
      KSCubePreparation.energy (fun i => x i + h * covarianceSampleIncrement hQ s i)) =
      KSCubePreparation.energy x + h ^ 2 * realTrace Q := by
    simpa only [energy_eq_norm_sq] using hmean
  rw [← heq]
  apply Finset.sum_le_sum
  intro s _
  exact mul_le_mul_of_nonneg_left (KSCubePreparation.snap_energy_progress (hchild s))
    s.property.le

/-- The eighth-cube covariance bound survives the controller's actual first preparation step.
`Tr Q ≥ 3/4` follows from `Tr Q ≥ 3k/4` whenever at least one coordinate is live. -/
theorem eighth_covarianceSample_snap_progress
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Q.PosSemidef)
    (x : Fin N → ℝ) (hx : x ∈ ksCube (1 / 8))
    (htrace : 3 / 4 ≤ realTrace Q) (h ρ : ℝ)
    (hchild : ∀ s : PositiveCovarianceOutcome (scaledCovariance_posSemidef x hQ),
      (fun i => x i + h * covarianceSampleIncrement
        (scaledCovariance_posSemidef x hQ) s i) ∈ ksCube (1 / 8)) :
    KSCubePreparation.energy x + h ^ 2 / 2 ≤
      ∑ s : PositiveCovarianceOutcome (scaledCovariance_posSemidef x hQ),
        covarianceSampleWeight (scaledCovariance_posSemidef x hQ) s *
        KSCubePreparation.energy (KSCubePreparation.snap (1 / 8) ρ
          (fun i => x i + h * covarianceSampleIncrement
            (scaledCovariance_posSemidef x hQ) s i)) := by
  have hp := eighth_scaledCovariance_trace_lower_of_trace x hQ
    (fun i => abs_le.mpr ⟨hx.1 i, hx.2 i⟩) htrace
  have hprogress := covarianceSample_snap_energy_progress
    (scaledCovariance_posSemidef x hQ) (by linarith) x h (1 / 8) ρ hchild
  nlinarith [sq_nonneg h]

/-- Sampling and snapping together preserve every already frozen coordinate. -/
theorem covarianceSample_snap_preserves_frozen
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Q.PosSemidef)
    (x : Fin N → ℝ) (h a ρ : ℝ) {i : Fin N}
    (hrow : ∀ j, Q i j = 0) (hi : |x i| = a)
    (s : PositiveCovarianceOutcome hQ) :
    KSCubePreparation.snap a ρ
      (fun j => x j + h * covarianceSampleIncrement hQ s j) i = x i := by
  have hz := range_coordinate_zero hrow (positive_covarianceSample_mem_range hQ s)
  have heq : x i + h * covarianceSampleIncrement hQ s i = x i := by
    rw [hz, mul_zero, add_zero]
  have hf := KSCubePreparation.snap_preserves_frozen (ρ := ρ)
    (fun j => x j + h * covarianceSampleIncrement hQ s j) i (heq ▸ hi)
  exact hf.trans heq

end Snapping

/-- The full-cube physical direction is the normalized direction multiplied by `sqrt dᵢ`. -/
def weightedDirection (x : ι → ℝ) (v : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => Real.sqrt (1 - x i ^ 2) * v i)

omit [DecidableEq ι] in
theorem weightedDirection_norm_sq (x : ι → ℝ) (v : EuclideanSpace ℝ ι)
    (hx : ∀ i, x i ^ 2 ≤ 1) :
    ‖weightedDirection x v‖ ^ 2 = ∑ i, (1 - x i ^ 2) * v i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  simp only [weightedDirection, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs, mul_pow]
  rw [Real.sq_sqrt (sub_nonneg.mpr (hx i))]

omit [DecidableEq ι] in
theorem weightedDirection_norm_sq_lower (x : ι → ℝ) (v : EuclideanSpace ℝ ι)
    {r : ℝ} (hr : 0 ≤ r) (hx : ∀ i, r ≤ 1 - x i ^ 2) :
    r * ‖v‖ ^ 2 ≤ ‖weightedDirection x v‖ ^ 2 := by
  rw [weightedDirection_norm_sq x v (fun i => by linarith [hx i]),
    EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  simp only [Real.norm_eq_abs, sq_abs]
  exact mul_le_mul_of_nonneg_right (hx i) (sq_nonneg _)

omit [DecidableEq ι] in
/-- A positive full-cube margin gives progress for a unit normalized direction.
The type `ι` here indexes the live coordinates; zero-extension preserves frozen ones. -/
theorem full_cube_symmetric_progress (x : EuclideanSpace ℝ ι)
    (v : EuclideanSpace ℝ ι) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρone : ρ ≤ 1)
    (hx : ∀ i, |x i| ≤ 1 - ρ) (hv : ‖v‖ = 1) (h : ℝ) :
    ‖x‖ ^ 2 + ρ * h ^ 2 ≤
      (‖x + h • weightedDirection (WithLp.ofLp x) v‖ ^ 2 +
        ‖x - h • weightedDirection (WithLp.ofLp x) v‖ ^ 2) / 2 := by
  have hw := weightedDirection_norm_sq_lower (WithLp.ofLp x) v hρ (fun i => by
    change ρ ≤ 1 - x i ^ 2
    have hi := abs_le.mp (hx i)
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - ρ - x i)
      (by linarith : 0 ≤ 1 - ρ + x i), mul_nonneg hρ (sub_nonneg.mpr hρone)])
  rw [hv] at hw
  rw [symmetric_norm_sq]
  nlinarith [sq_nonneg h]

omit [Fintype ι] [DecidableEq ι] in
theorem weightedDirection_coordinate_zero (x : ι → ℝ) (v : EuclideanSpace ℝ ι)
    {i : ι} (hi : v i = 0) : weightedDirection x v i = 0 := by
  simp [weightedDirection, hi]

section CubeLegality
variable {N : ℕ}

/-- The concrete symmetric covariance children remain in the cube if the step is
smaller than the live margin and the covariance has zero frozen rows. -/
theorem covarianceSample_child_mem_cube {Q : Matrix (Fin N) (Fin N) ℝ}
    (hQ : Q.PosSemidef) (x : Fin N → ℝ) (h a ρ : ℝ)
    (hx : x ∈ ksCube a)
    (hmargin : ∀ i, |x i| < a → ρ ≤ a - |x i|)
    (hfrozen : ∀ i, |x i| = a → ∀ j, Q i j = 0)
    (hstep : |h| * Real.sqrt (realTrace Q) ≤ ρ)
    (s : PositiveCovarianceOutcome hQ) :
    (fun i => x i + h * covarianceSampleIncrement hQ s i) ∈ ksCube a := by
  have hnorm : ‖covarianceSampleIncrement hQ s‖ = Real.sqrt (realTrace Q) := by
    rw [← covarianceSample_norm_sq hQ s, Real.sqrt_sq (norm_nonneg _)]
  have hi (i : Fin N) : |x i + h * covarianceSampleIncrement hQ s i| ≤ a := by
    by_cases hf : |x i| = a
    · have hz := range_coordinate_zero (hfrozen i hf)
        (positive_covarianceSample_mem_range hQ s)
      simp only [hz, mul_zero, add_zero, hf, le_refl]
    · have hxi : |x i| < a := lt_of_le_of_ne (abs_le.mpr ⟨hx.1 i, hx.2 i⟩) hf
      have hcoord : |covarianceSampleIncrement hQ s i| ≤ Real.sqrt (realTrace Q) := by
        simpa only [Real.norm_eq_abs, hnorm] using
          PiLp.norm_apply_le (covarianceSampleIncrement hQ s) i
      calc
        _ ≤ |x i| + |h * covarianceSampleIncrement hQ s i| := abs_add_le _ _
        _ = |x i| + |h| * |covarianceSampleIncrement hQ s i| := by rw [abs_mul]
        _ ≤ |x i| + |h| * Real.sqrt (realTrace Q) :=
          add_le_add_left (mul_le_mul_of_nonneg_left hcoord (abs_nonneg h)) _
        _ ≤ a := by linarith [hmargin i hxi]
  exact ⟨fun i => (abs_le.mp (hi i)).1, fun i => (abs_le.mp (hi i)).2⟩

/-- All geometric premises of the snapped eighth-cube progress bound are supplied
by explicit current-state, covariance, and mesh conditions. -/
theorem eighth_covarianceSample_prepared_progress
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Q.PosSemidef)
    (x : Fin N → ℝ) (hx : x ∈ ksCube (1 / 8))
    (htrace : 3 / 4 ≤ realTrace Q) (h ρ : ℝ)
    (hmargin : ∀ i, |x i| < 1 / 8 → ρ ≤ 1 / 8 - |x i|)
    (hfrozen : ∀ i, |x i| = 1 / 8 → ∀ j, Q i j = 0)
    (hstep : |h| * Real.sqrt (realTrace (scaledCovariance x Q)) ≤ ρ) :
    KSCubePreparation.energy x + h ^ 2 / 2 ≤
      ∑ s : PositiveCovarianceOutcome (scaledCovariance_posSemidef x hQ),
        covarianceSampleWeight (scaledCovariance_posSemidef x hQ) s *
        KSCubePreparation.energy (KSCubePreparation.snap (1 / 8) ρ
          (fun i => x i + h * covarianceSampleIncrement
            (scaledCovariance_posSemidef x hQ) s i)) := by
  apply eighth_covarianceSample_snap_progress hQ x hx htrace h ρ
  exact covarianceSample_child_mem_cube (scaledCovariance_posSemidef x hQ)
    x h (1 / 8) ρ hx hmargin
      (fun i hi => scaledCovariance_row_zero x (hfrozen i hi)) hstep

end CubeLegality

/-- In one nonzero live coordinate, imposing radial orthogonality kills movement. -/
theorem one_coordinate_orthogonal_forces_zero {x v : ℝ}
    (hx : x ≠ 0) (horthogonal : x * v = 0) : v = 0 :=
  (mul_eq_zero.mp horthogonal).resolve_left hx

end MatrixSpencer.KSSymmetricProgress
