import SeamlessKS.Projection
import MatrixSpencer.DensityDomain
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace RadialKS.Projection
open MatrixSpencer MatrixSpencer.KSSpinDrift MatrixSpencer.KSWeightedProjection
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def constraint (E F : Matrix ι ι ℝ) (a : ι → ℝ) :
    Matrix (ι ⊕ Unit) (ι ⊕ ι) ℝ :=
  fun i j => match i with
  | Sum.inl k => constraintMatrix E F k j
  | Sum.inr _ => Sum.elim (fun _ => 0) a j

def constraintLin (E F : Matrix ι ι ℝ) (a : ι → ℝ) :=
  Matrix.toEuclideanLin (constraint E F a)

def projection (E F : Matrix ι ι ℝ) (a : ι → ℝ) :=
  euclideanProjectionMatrix (LinearMap.ker (constraintLin E F a))

theorem projection_star (E F : Matrix ι ι ℝ) (a : ι → ℝ) :
    IsStarProjection (projection E F a) := euclideanProjectionMatrix_isStarProjection _

theorem projection_trace (E F : Matrix ι ι ℝ) (a : ι → ℝ) :
    (Fintype.card ι : ℝ) ≤ realTrace (projection E F a) + 1 := by
  rw [projection, euclideanProjectionMatrix_trace]
  have h := (constraintLin E F a).finrank_range_add_finrank_ker
  have hb := (LinearMap.range (constraintLin E F a)).finrank_le
  have hd : Module.finrank ℝ (EuclideanSpace ℝ (ι ⊕ ι)) = 2 * Fintype.card ι := by
    simp [Fintype.card_sum, two_mul]
  have hc : Module.finrank ℝ (EuclideanSpace ℝ (ι ⊕ Unit)) = Fintype.card ι + 1 := by simp
  rw [hd] at h
  rw [hc] at hb
  exact_mod_cast (show Fintype.card ι ≤ Module.finrank ℝ
    (LinearMap.ker (constraintLin E F a)) + 1 by omega)

theorem projection_constraint (E F : Matrix ι ι ℝ) (a : ι → ℝ) :
    constraint E F a * projection E F a = 0 := by
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
  have h := (LinearMap.ker (constraintLin E F a)).starProjection_apply_mem
    (WithLp.toLp 2 (Pi.single j 1))
  change constraintLin E F a
    ((LinearMap.ker (constraintLin E F a)).starProjection
      (WithLp.toLp 2 (Pi.single j 1))) = 0 at h
  rw [← toEuclideanCLM_projectionMatrix] at h
  have he := congrArg WithLp.ofLp h
  simpa only [constraintLin, projection, Matrix.ofLp_toEuclideanLin_apply,
    Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, WithLp.ofLp_zero,
    WithLp.ofLp_toLp] using he

theorem projection_legal (E F : Matrix ι ι ℝ) (a : ι → ℝ) :
    (topProjection - rowPerturbation E F) * projection E F a = 0 := by
  ext (i | i) j
  · have h := congrArg (fun A => A (Sum.inl i) j) (projection_constraint E F a)
    simpa [Matrix.mul_apply, topProjection, rowPerturbation, constraint,
      constraintMatrix, Fintype.sum_sum_type] using h
  · simp [Matrix.mul_apply, topProjection, rowPerturbation, Fintype.sum_sum_type]

theorem block_bounds (E F : Matrix ι ι ℝ) (a : ι → ℝ) :
    let P := projection E F a
    let α := hsSq E + hsSq F
    realTrace P.toBlocks₁₁ ≤ α ∧
    realTrace (1 - P.toBlocks₂₂) ≤ α + 1 ∧
    hsSq P.toBlocks₁₂ ≤ α ∧
    hsSq (1 - P.toBlocks₂₂) ≤ α + 1 := by
  let P := projection E F a
  let W := topProjection (ι := ι)
  have hW : IsStarProjection W := topProjection_isStarProjection
  have hP : IsStarProjection P := projection_star E F a
  have ht : realTrace (W * P) ≤ hsSq E + hsSq F := by
    simpa only [hsSq_rowPerturbation] using
      trace_projection_le_perturbation hW hP (projection_legal E F a)
  have hr : realTrace (1-W) ≤ realTrace P + 1 := by
    rw [realTrace_one_sub_topProjection]
    exact projection_trace E F a
  have hb : realTrace ((1-W)*(1-P)) ≤ realTrace (W*P) + 1 := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      realTrace_sub] at *
    linarith
  have hc := (cross_hsSq_le hW hP).trans ht
  have hb2 : realTrace ((1-W)*(1-P)) ≤ hsSq E + hsSq F + 1 := by linarith
  have hd := (complementary_hsSq_le hW hP).trans hb2
  have hall := And.intro ht (And.intro hb2 (And.intro hc hd))
  have hp := Matrix.fromBlocks_toBlocks P
  rw [← hp, show W = topProjection from rfl, one_sub_topProjection] at hall
  simpa [topProjection, one_sub_fromBlocks, Matrix.fromBlocks_multiply,
    realTrace_fromBlocks, hsSq_fromBlocks] using hall

theorem cross_identity (E F : Matrix ι ι ℝ) (a : ι → ℝ) :
    (projection E F a).toBlocks₁₂ =
      E * (projection E F a).toBlocks₁₂ + F * (projection E F a).toBlocks₂₂ := by
  ext i j
  have h12 := congrArg (fun A => A (Sum.inl i) (Sum.inr j)) (projection_legal E F a)
  simp [topProjection, rowPerturbation, Matrix.mul_apply, Fintype.sum_sum_type,
    sub_mul, Finset.sum_sub_distrib, Matrix.one_apply] at h12
  change (projection E F a) (Sum.inl i) (Sum.inr j) =
    (∑ k, E i k * (projection E F a) (Sum.inl k) (Sum.inr j)) +
    (∑ k, F i k * (projection E F a) (Sum.inr k) (Sum.inr j))
  linarith

theorem mixed_bound (E F : Matrix ι ι ℝ) (a z : ι → ℝ)
    (hz : ∀ i, |z i| ≤ 1) {h : ℝ} (hh : 1 ≤ h)
    (hE : hsSq E ≤ h) (hF : hsSq F ≤ 4 * h)
    (hbase : |realTrace (Matrix.diagonal z * F)| ≤ 2 * h) :
    |realTrace (Matrix.diagonal z * (projection E F a).toBlocks₁₂)| ≤
      (2 + Real.sqrt 5 + 2 * Real.sqrt 6) * h := by
  let P := projection E F a
  have hproj := block_bounds E F a
  dsimp only at hproj
  have hcross : hsSq P.toBlocks₁₂ ≤ 5 * h := hproj.2.2.1.trans (by linarith)
  have hdefect : hsSq (1 - P.toBlocks₂₂) ≤ 6 * h := hproj.2.2.2.trans (by linarith)
  have hid : Matrix.diagonal z * P.toBlocks₁₂ = Matrix.diagonal z * F +
      (Matrix.diagonal z * E) * P.toBlocks₁₂ -
      (Matrix.diagonal z * F) * (1 - P.toBlocks₂₂) := by
    have hk := cross_identity E F a
    change P.toBlocks₁₂ = E * P.toBlocks₁₂ + F * P.toBlocks₂₂ at hk
    calc
      _ = Matrix.diagonal z * (E * P.toBlocks₁₂ + F * P.toBlocks₂₂) := by
        exact congrArg (fun A => Matrix.diagonal z * A) hk
      _ = _ := by noncomm_ring
  have he : |realTrace ((Matrix.diagonal z * E) * P.toBlocks₁₂)| ≤
      Real.sqrt (h * (5 * h)) :=
    (abs_trace_mul_le_sqrt _ _).trans (sqrt_product_bound
      (hsSq_nonneg _) (hsSq_nonneg _)
      ((hsSq_diagonal_mul_le z hz E).trans hE) hcross)
  have hf : |realTrace ((Matrix.diagonal z * F) * (1 - P.toBlocks₂₂))| ≤
      Real.sqrt ((4 * h) * (6 * h)) :=
    (abs_trace_mul_le_sqrt _ _).trans (sqrt_product_bound
      (hsSq_nonneg _) (hsSq_nonneg _)
      ((hsSq_diagonal_mul_le z hz F).trans hF) hdefect)
  have hs₁ : Real.sqrt (h * (5 * h)) = Real.sqrt 5 * h := by
    rw [show h * (5 * h) = 5 * h ^ 2 by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by linarith : 0 ≤ h)]
  have hs₂ : Real.sqrt ((4 * h) * (6 * h)) = 2 * Real.sqrt 6 * h := by
    rw [show (4 * h) * (6 * h) = 4 * (6 * h ^ 2) by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_mul (by norm_num), Real.sqrt_sq (by linarith : 0 ≤ h)]
    norm_num
    ring
  rw [hs₁] at he
  rw [hs₂] at hf
  calc
    _ = |realTrace (Matrix.diagonal z * F) +
        realTrace ((Matrix.diagonal z * E) * P.toBlocks₁₂) -
        realTrace ((Matrix.diagonal z * F) * (1 - P.toBlocks₂₂))| := by
      rw [hid, realTrace_sub, realTrace_add]
    _ ≤ |realTrace (Matrix.diagonal z * F)| +
        |realTrace ((Matrix.diagonal z * E) * P.toBlocks₁₂)| +
        |realTrace ((Matrix.diagonal z * F) * (1 - P.toBlocks₂₂))| :=
      (abs_sub _ _).trans (add_le_add_right (abs_add_le _ _) _)
    _ ≤ _ := by linarith

theorem bottom_psd (E F : Matrix ι ι ℝ) (a : ι → ℝ) :
    (1 - (projection E F a).toBlocks₂₂).PosSemidef := by
  have h := ((projection_star E F a).one_sub.nonneg).posSemidef
  have hs := h.submatrix Sum.inr
  convert hs using 1
  ext i j
  simp [Matrix.toBlocks₂₂, Matrix.submatrix, Matrix.one_apply]

theorem direct_bound (E F : Matrix ι ι ℝ) (a d : ι → ℝ)
    {h u L : ℝ} (hh : 1 ≤ h) (hu : 0 < u) (hL : 0 ≤ L)
    (hd : ∀ i, d i ≤ L / u) (hsum : ∑ i, d i = h)
    (hE : hsSq E ≤ h) (hF : hsSq F ≤ 4 * h) :
    (1 - 6 * L / u) * h ≤
      realTrace (Matrix.diagonal d * (projection E F a).toBlocks₂₂) := by
  let P := projection E F a
  have hcap : Matrix.diagonal d ≤ (L / u) • (1 : Matrix ι ι ℝ) := by
    apply Matrix.le_iff.mpr
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.diagonal_sub]
    exact Matrix.posSemidef_diagonal_iff.mpr (fun i => by
      simpa using sub_nonneg.mpr (hd i))
  have ht := realTrace_mul_mono (bottom_psd E F a) hcap
  rw [realTrace_mul_comm (1 - P.toBlocks₂₂), Matrix.mul_smul, Matrix.mul_one,
    realTrace_smul, Matrix.mul_sub, Matrix.mul_one, realTrace_sub] at ht
  have htrace : realTrace (Matrix.diagonal d) = h := by
    simpa [realTrace] using hsum
  rw [htrace] at ht
  have htracebound : realTrace (1 - P.toBlocks₂₂) ≤ 6 * h :=
    (block_bounds E F a).2.1.trans (by linarith)
  have ht' := mul_le_mul_of_nonneg_left htracebound (div_nonneg hL hu.le)
  have heq : (1 - 6 * L / u) * h = h - (L / u) * (6 * h) := by ring
  rw [heq]
  linarith

theorem response_bound (E F : Matrix ι ι ℝ) (a : ι → ℝ)
    {H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ} (hH : H.PosSemidef)
    {h : ℝ} (htrace : realTrace H ≤ 5 * h) :
    realTrace (H * projection E F a) ≤ 5 * h := by
  have hb := realTrace_mul_mono hH (projection_star E F a).le_one
  rw [Matrix.mul_one] at hb
  exact hb.trans htrace

def average (E F : Matrix ι ι ℝ) (a d z : ι → ℝ)
    (H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (u : ℝ) : ℝ :=
  -realTrace (Matrix.diagonal d * (projection E F a).toBlocks₂₂) +
    realTrace (H * projection E F a) / u -
    realTrace (Matrix.diagonal z * (projection E F a).toBlocks₁₂) / u

theorem average_bound (E F : Matrix ι ι ℝ) (a d z : ι → ℝ)
    (H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) {h u L : ℝ}
    (hh : 1 ≤ h) (hu : 0 < u) (hL : 0 ≤ L)
    (hd : ∀ i, d i ≤ L / u) (hsum : ∑ i, d i = h)
    (hz : ∀ i, |z i| ≤ 1) (hE : hsSq E ≤ h) (hF : hsSq F ≤ 4 * h)
    (hbase : |realTrace (Matrix.diagonal z * F)| ≤ 2 * h)
    (hH : H.PosSemidef) (htrace : realTrace H ≤ 5 * h) :
    average E F a d z H u ≤
      -(1 - (6 * L + 7 + Real.sqrt 5 + 2 * Real.sqrt 6) / u) * h := by
  have hdirect := direct_bound E F a d hh hu hL hd hsum hE hF
  have hresp := div_le_div_of_nonneg_right (response_bound E F a hH htrace) hu.le
  have hmix := mixed_bound E F a z hz hh hE hF hbase
  have hmdiv := div_le_div_of_nonneg_right (neg_le_of_abs_le hmix) hu.le
  unfold average
  have he : -(1 - (6 * L + 7 + Real.sqrt 5 + 2 * Real.sqrt 6) / u) * h =
      -((1 - 6 * L / u) * h) + 5 * h / u +
        (2 + Real.sqrt 5 + 2 * Real.sqrt 6) * h / u := by ring
  rw [he]
  simp only [neg_div] at hmdiv
  linarith

theorem coefficient_pos :
    0 < 1 - (6 * (200 / 81 : ℝ) + 7 + Real.sqrt 5 + 2 * Real.sqrt 6) / 64 := by
  have h5 : Real.sqrt 5 < 3 := (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h6 : Real.sqrt 6 < 3 := (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  linarith

theorem upper_covariance_trace (E F : Matrix ι ι ℝ) (a d z : ι → ℝ)
    (H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (u : ℝ) :
    realTrace (upperMatrix d z H u * projection E F a) =
      average E F a d z H u := by
  let P := projection E F a
  rw [upperMatrix, Matrix.sub_mul, Matrix.smul_mul, realTrace_sub, realTrace_smul]
  have hp := Matrix.fromBlocks_toBlocks P
  have he : realTrace (Matrix.fromBlocks 0 ((1 / u) • Matrix.diagonal z) 0
      (Matrix.diagonal d) * P) =
      (1 / u) * realTrace (Matrix.diagonal z * P.toBlocks₁₂) +
      realTrace (Matrix.diagonal d * P.toBlocks₂₂) := by
    conv_lhs => arg 1; arg 2; rw [← hp]
    rw [Matrix.fromBlocks_multiply, realTrace_fromBlocks]
    simp only [Matrix.zero_mul, zero_add, Matrix.smul_mul, realTrace_smul]
    rw [projection_cross_trace P (projection_star E F a) z]
  rw [he]
  unfold average
  ring

theorem exists_negative_direction (E F : Matrix ι ι ℝ) (a d z : ι → ℝ)
    (H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (u : ℝ)
    (hneg : average E F a d z H u < 0) :
    ∃ x : ι ⊕ ι → ℝ,
      constraint E F a *ᵥ x = 0 ∧ x ⬝ᵥ (upperMatrix d z H u *ᵥ x) < 0 := by
  have hsum := projection_quadratic_sum (projection E F a) (upperMatrix d z H u)
    (projection_star E F a)
  rw [upper_covariance_trace] at hsum
  have hex : ∃ j, (projection E F a *ᵥ Pi.single j 1) ⬝ᵥ
      (upperMatrix d z H u *ᵥ (projection E F a *ᵥ Pi.single j 1)) < 0 := by
    by_contra h
    have hp : 0 ≤ ∑ j, (projection E F a *ᵥ Pi.single j 1) ⬝ᵥ
        (upperMatrix d z H u *ᵥ (projection E F a *ᵥ Pi.single j 1)) := by
      apply Finset.sum_nonneg
      intro j _
      exact le_of_not_gt (fun hj => h ⟨j, hj⟩)
    rw [hsum] at hp
    linarith
  obtain ⟨j, hj⟩ := hex
  refine ⟨projection E F a *ᵥ Pi.single j 1, ?_, hj⟩
  rw [Matrix.mulVec_mulVec, projection_constraint, Matrix.zero_mulVec]

section Physical
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}

theorem source_mass_one_le [Nonempty ι]
    (D : ι → Matrix n n ℂ) (hD : ∀ i, (D i).PosSemidef)
    {P : Matrix n n ℂ} (hP : P.PosSemidef)
    (hr : ∀ i, 0 < realTrace (D i)) (hm : ∀ i, 0 < realTrace (P * D i))
    (hfix : P = ∑ i, realTrace (P * D i) • D i) :
    1 ≤ ∑ i, realTrace (D i)^2 := by
  have he : realTrace P = ∑ i, realTrace (P * D i) * realTrace (D i) := by
    conv_lhs => rw [hfix]
    simp only [realTrace_sum, realTrace_smul]
  have hp : 0 < realTrace P := by
    rw [he]
    exact Finset.sum_pos (fun i _ => mul_pos (hm i) (hr i)) Finset.univ_nonempty
  have hpair (i : ι) : realTrace (P * D i) ≤ realTrace P * realTrace (D i) := by
    have h := realTrace_mul_mono (hD i) (posSemidef_le_trace_identity hP)
    rw [realTrace_mul_comm, Algebra.algebraMap_eq_smul_one, Matrix.mul_smul,
      Matrix.mul_one, realTrace_smul] at h
    exact h
  have hbound : realTrace P ≤ realTrace P * ∑ i, realTrace (D i)^2 := by
    rw [he, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have h := mul_le_mul_of_nonneg_right (hpair i) (hr i).le
    nlinarith
  nlinarith
theorem physical_average_bound [Nonempty ι]
    (D : ι → Matrix n n ℂ) (hD : ∀ i, (D i).PosSemidef)
    {P J : Matrix n n ℂ} (hP : P.PosSemidef) (hJ : J.IsHermitian)
    (hJJ : J * J = 1) (hc : ∀ i, J * D i = D i * J)
    (hr : ∀ i, 0 < realTrace (D i)) (hm : ∀ i, 0 < realTrace (P * D i))
    (hfix : P = ∑ i, realTrace (P * D i) • D i) (a z : ι → ℝ)
    (hz : ∀ i, |z i| ≤ 1) {u L : ℝ} (hu : 0 < u) (hL : 0 ≤ L)
    (hsmall : ∀ i, realTrace (D i) ^ 2 ≤ L / u) :
    average (spinE P D) (spinF P J D z) a (fun i => realTrace (D i) ^ 2) z
      (spinResponseGram P J D z) u ≤
      -(1 - (6 * L + 7 + Real.sqrt 5 + 2 * Real.sqrt 6) / u) * ∑ i, realTrace (D i) ^ 2 := by
  let R := fisherWeight P D
  let T := KSFisher.gram D
  let TJ := KSFisher.spinGram J D
  let Γ := physicalRealGram P D
  let d : ι → ℝ := fun i => realTrace (D i) ^ 2
  have hR := fisherWeight_pos D hr hm
  have hdiag : ∀ i, Γ i i / R i ≤ d i := fun i =>
    physical_weighted_diagonal hP D hD hr hm i
  have ht : Tᵀ = T := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (KSFisher.gram_isHermitian D).eq
  have htj : TJᵀ = TJ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (KSFisher.spinGram_isHermitian hJ D (fun i => (hD i).isHermitian)).eq
  have hfisher : Tᵀ * Matrix.diagonal R * T ≤ Γ := by
    rw [ht]
    exact KSFisher.gram_fisher D hD (fun i => realTrace (P * D i))
      (fun i => (hm i).le) hr hfix
  have hspin : TJᵀ * Matrix.diagonal R * TJ ≤ Γ := by
    rw [htj]
    exact KSFisher.spin_gram_fisher D hD (fun i => realTrace (P * D i))
      (fun i => (hm i).le) hr hfix hJ hJJ hc
  have henergy := weighted_pair_energy_bounds R d z hR hz T TJ Γ hfisher hspin hdiag
  have hbase := weighted_pair_mixed_baseline R d z hR hz T TJ
    (fun i => realTrace_mul_nonneg (hD i) (hD i))
    (fun i => gram_diagonal_le_trace_sq (hD i))
    (fun i => spin_gram_diagonal_abs_le hJ hJJ (hD i).isHermitian)
  have hresponse : (spinResponseGram P J D z).PosSemidef :=
    KSFisher.physicalGram_posSemidef hP _
      (jointFeatures_isHermitian D (fun i => (hD i).isHermitian) hJ hc R z)
  have htrace : realTrace (spinResponseGram P J D z) ≤ 5 * ∑ i, d i :=
    joint_response_trace_le D (fun i => (hD i).isHermitian) hP hJ hJJ hc R z d hR hz
      (fun i => physical_weighted_diagonal hP D hD hr hm i)
  have hh : 1 ≤ ∑ i, d i := source_mass_one_le D hD hP hr hm hfix
  exact average_bound (spinE P D) (spinF P J D z) a d z
    (spinResponseGram P J D z) hh hu hL hsmall rfl hz henergy.1 henergy.2
    hbase hresponse htrace


theorem physical_average_negative [Nonempty ι]
    (D : ι → Matrix n n ℂ) (hD : ∀ i, (D i).PosSemidef)
    {P J : Matrix n n ℂ} (hP : P.PosSemidef) (hJ : J.IsHermitian)
    (hJJ : J * J = 1) (hc : ∀ i, J * D i = D i * J)
    (hr : ∀ i, 0 < realTrace (D i)) (hm : ∀ i, 0 < realTrace (P * D i))
    (hfix : P = ∑ i, realTrace (P * D i) • D i) (a z : ι → ℝ)
    (hz : ∀ i, |z i| ≤ 1)
    (hsmall : ∀ i, realTrace (D i) ^ 2 ≤ (200 / 81 : ℝ) / 64) :
    average (spinE P D) (spinF P J D z) a (fun i => realTrace (D i) ^ 2) z
      (spinResponseGram P J D z) 64 < 0 := by
  have hbound := physical_average_bound D hD hP hJ hJJ hc hr hm hfix a z hz
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 200 / 81) hsmall
  have hh : 0 < ∑ i, realTrace (D i) ^ 2 :=
    Finset.sum_pos (fun i _ => sq_pos_of_pos (hr i)) Finset.univ_nonempty
  exact hbound.trans_lt (mul_neg_of_neg_of_pos
    (neg_neg_of_pos coefficient_pos) hh)


theorem exists_physical_direction [Nonempty ι]
    (D : ι → Matrix n n ℂ) (hD : ∀ i, (D i).PosSemidef)
    {P J : Matrix n n ℂ} (hP : P.PosSemidef) (hJ : J.IsHermitian)
    (hJJ : J * J = 1) (hc : ∀ i, J * D i = D i * J)
    (hr : ∀ i, 0 < realTrace (D i)) (hm : ∀ i, 0 < realTrace (P * D i))
    (hfix : P = ∑ i, realTrace (P * D i) • D i) (b z : ι → ℝ)
    (hz : ∀ i, |z i| ≤ 1)
    (hsmall : ∀ i, realTrace (D i) ^ 2 ≤ (200 / 81 : ℝ) / 64) :
    ∃ ω y : ι → ℝ, y ≠ 0 ∧ b ⬝ᵥ y = 0 ∧
      (1 - KSFisher.gram D) *ᵥ ω =
        (KSFisher.spinGram J D - KSFisher.gram D * Matrix.diagonal z) *ᵥ y ∧
      legalUpper P J D (fisherWeight P D) (fun i => realTrace (D i) ^ 2) z 64 ω y < 0 := by
  have hneg := physical_average_negative D hD hP hJ hJJ hc hr hm hfix (unwhiten (fisherWeight P D) b) z hz hsmall
  obtain ⟨x, hx, hqx⟩ := exists_negative_direction (spinE P D) (spinF P J D z) (unwhiten (fisherWeight P D) b)
    (fun i => realTrace (D i) ^ 2) z (spinResponseGram P J D z) 64 hneg
  have hR := fisherWeight_pos D hr hm
  have hresponse : (spinResponseGram P J D z).PosSemidef :=
    KSFisher.physicalGram_posSemidef hP _
      (jointFeatures_isHermitian D (fun i => (hD i).isHermitian) hJ hc (fisherWeight P D) z)
  refine ⟨unwhiten (fisherWeight P D) (x ∘ Sum.inl),
    unwhiten (fisherWeight P D) (x ∘ Sum.inr), ?_, ?_, ?_, ?_⟩
  · exact unwhiten_ne_zero _ hR
      (negative_kernel_bottom_ne_zero _ _ hresponse (by norm_num) hqx)
  · have hrad := congrFun hx (Sum.inr ())
    simpa [constraint, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      unwhiten_apply, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hrad
  · apply unwhiten_legal _ hR (KSFisher.gram D) (KSFisher.spinGram J D) z
    funext i
    have hi := congrFun hx (Sum.inl i)
    simpa [constraint, Matrix.mulVec, dotProduct] using hi
  · unfold spinResponseGram at hqx
    rwa [upperMatrix_eq_legalUpper P J D (fisherWeight P D) _ z hR 64 x] at hqx


end Physical
end RadialKS.Projection
