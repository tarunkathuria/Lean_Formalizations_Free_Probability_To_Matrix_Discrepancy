import SeamlessKS.NumericalRegularityJoint


open Matrix Set Filter
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff Topology
noncomputable section
namespace SeamlessKS
namespace NumericalRegularityParseval
open MatrixSpencer NumericalRegularityObjective NumericalRegularityDomain
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] [Nonempty n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}
set_option maxHeartbeats 1400000

theorem atom_norm_le_one (v : ι → n → ℂ) (hp : (∑ i, KSRankOne.atom (v i)) ≤ 1) (i : ι) :
    ‖KSRankOne.atom (v i)‖ ≤ 1 := by
  have hle : KSRankOne.atom (v i) ≤ 1 :=
    (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (KSRankOne.atom_posSemidef (v j)).nonneg)
      (Finset.mem_univ i)).trans hp
  apply (CStarAlgebra.norm_le_iff_le_algebraMap _ zero_le_one (KSRankOne.atom_posSemidef (v i)).nonneg).mpr
  simpa using hle

theorem sum_atom_norm_sq_le (v : ι → n → ℂ) (hp : (∑ i, KSRankOne.atom (v i)) ≤ 1) :
    (∑ i, ‖KSRankOne.atom (v i)‖ ^ 2) ≤ Fintype.card n := by
  have ht := realTrace_mul_mono (Matrix.PosSemidef.one : (1 : Matrix n n ℂ).PosSemidef) hp
  simp only [Matrix.one_mul, realTrace_sum] at ht
  have htr : realTrace (1 : Matrix n n ℂ) = Fintype.card n := by simp [realTrace]
  rw [htr] at ht
  have hs : (∑ i, ‖KSRankOne.atom (v i)‖ ^ 2) ≤ ∑ i, ‖KSRankOne.atom (v i)‖ := by
    apply Finset.sum_le_sum
    intro i _
    have hn := atom_norm_le_one v hp i
    nlinarith [norm_nonneg (KSRankOne.atom (v i))]
  exact hs.trans (by simpa only [KSRankOne.atom_norm] using ht)

theorem doubled_atom_norm_le (v : ι → n → ℂ) (i : ι) :
    ‖NumericalRegularitySource.atom v i‖ ≤ ‖KSRankOne.atom (v i)‖ := by
  have hA := KSRankOne.atom_posSemidef (v i)
  have ha : KSRankOne.atom (v i) ≤ ‖KSRankOne.atom (v i)‖ • (1 : Matrix n n ℂ) := by
    have h := (CStarAlgebra.norm_le_iff_le_algebraMap _ (norm_nonneg _) hA.nonneg).mp (le_refl ‖KSRankOne.atom (v i)‖)
    simpa only [Algebra.algebraMap_eq_smul_one] using h
  apply (CStarAlgebra.norm_le_iff_le_algebraMap _ (norm_nonneg _) (KSComplexSpinSource.atom_posSemidef v i).nonneg).mpr
  simpa only [Algebra.algebraMap_eq_smul_one] using KSDebitUniformFloor.doubled_le_scalar ha

theorem doubled_atom_trace (v : ι → n → ℂ) (i : ι) :
    realTrace (NumericalRegularitySource.atom v i) = 2 * ‖KSRankOne.atom (v i)‖ := by
  rw [KSRankOne.atom_norm]
  simp [NumericalRegularitySource.atom, KSComplexSpinSource.atom, KSSpinSource.doubled,
    realTrace, Matrix.trace, Matrix.diag, Fintype.sum_sum_type, two_mul]

theorem source_norm_le {ζ : ℝ} (hζ : 0 ≤ ζ) (hζone : ζ ≤ 1)
    (v : ι → n → ℂ) (hp : (∑ i, KSRankOne.atom (v i)) ≤ 1) (x h : ι → ℝ)
    (hx : ∀ i, |x i| ≤ 1) (hh : ∀ i, |h i| ≤ 2) (z : ℂ) (hz : ‖z‖ ≤ 1)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hS : ‖S‖ ≤ 2) :
    ‖NumericalRegularitySource.source ζ v x h (z,S)‖ ≤ 6400 * Fintype.card n := by
  have hs : ‖NumericalRegularitySource.source ζ v x h (z,S)‖ ≤
      ∑ i, 6400 * ‖KSRankOne.atom (v i)‖ ^ 2 := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_smul, norm_mul]
    have hc : ‖Source.complexWeight 64 ζ ((x i : ℂ) + z * (h i : ℂ))‖ ≤ 1600 :=
      (NumericalRegularityBounds.owner_norm_le hζ hζone (hx i) (hh i) hz).trans (by norm_num)
    have ht : ‖Matrix.trace (NumericalRegularitySource.atom v i * S)‖ ≤ 4 * ‖KSRankOne.atom (v i)‖ := by
      have hb := KSComplexOwnerPerturbation.norm_trace_mul_le (NumericalRegularitySource.atom v i) S
        (KSComplexSpinSource.atom_posSemidef v i)
      rw [doubled_atom_trace] at hb
      have hm := mul_le_mul_of_nonneg_right hS (show 0 ≤ 2 * ‖KSRankOne.atom (v i)‖ by positivity)
      nlinarith
    have ha := doubled_atom_norm_le v i
    calc
      _ ≤ 1600 * (4 * ‖KSRankOne.atom (v i)‖) * ‖KSRankOne.atom (v i)‖ := by gcongr
      _ = _ := by ring
  rw [← Finset.mul_sum] at hs
  exact hs.trans (mul_le_mul_of_nonneg_left (sum_atom_norm_sq_le v hp) (by norm_num))


theorem valueCap_le {θ : ℝ} (hθ : 0 ≤ θ) (hθone : θ ≤ 1) :
    KSComplexObjectiveBound.valueCap (Fintype.card (n ⊕ n)) 6 2 (6400 * Fintype.card n) θ ≤
      10000 * ((Fintype.card (n ⊕ n) : ℝ) + 1) ^ 2 := by
  have hd : (0 : ℝ) ≤ Fintype.card n := Nat.cast_nonneg _
  have hs : Real.sqrt (2 * (6400 * (Fintype.card n : ℝ))) ≤ 160 * ((Fintype.card n : ℝ) + 1) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg (Fintype.card n : ℝ)]
  have ht : Real.sqrt (2 : ℝ) ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * ((Fintype.card (n ⊕ n) : ℝ)) by positivity)
  have hreg : 2 * θ * (Fintype.card (n ⊕ n) : ℝ) * Real.sqrt 2 ≤ 4 * Fintype.card (n ⊕ n) := by
    have h := mul_le_mul hθone ht (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith [mul_le_mul_of_nonneg_left h (show 0 ≤ 2 * (Fintype.card (n ⊕ n) : ℝ) by positivity)]
  unfold KSComplexObjectiveBound.valueCap
  simp only [Fintype.card_sum, Nat.cast_add] at *
  nlinarith [sq_nonneg (Fintype.card n : ℝ)]


theorem slope_norm_le_two (v : ι → n → ℂ) (hp : (∑ i, KSRankOne.atom (v i)) ≤ 1)
    (h : ι → ℝ) (hh : ∀ i, |h i| ≤ 2) : ‖slope v h‖ ≤ 2 := by
  have hup (a : ι → ℝ) (ha : ∀ i, |a i| ≤ 2) :
      (∑ i, a i • KSRankOne.atom (v i)) ≤ (2 : ℝ) • (1 : Matrix n n ℂ) := by
    calc
      _ ≤ ∑ i, (2 : ℝ) • KSRankOne.atom (v i) := by
        apply Finset.sum_le_sum
        intro i _
        exact smul_le_smul_of_nonneg_right ((le_abs_self (a i)).trans (ha i)) (KSRankOne.atom_posSemidef (v i)).nonneg
      _ = (2 : ℝ) • ∑ i, KSRankOne.atom (v i) := by rw [Finset.smul_sum]
      _ ≤ _ := smul_le_smul_of_nonneg_left hp (by norm_num)
  have hlo : -((2 : ℝ) • (1 : Matrix n n ℂ)) ≤ ∑ i, h i • KSRankOne.atom (v i) := by
    have hn := hup (fun i => -h i) (by intro i; simpa using hh i)
    simp only [neg_smul, Finset.sum_neg_distrib] at hn
    exact neg_le.mp hn
  have hhH : (∑ i, h i • KSRankOne.atom (v i)).IsHermitian := by
    change (∑ i, h i • KSRankOne.atom (v i))ᴴ = _
    simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_trivial,
      fun i => (KSRankOne.atom_isHermitian (v i)).eq]
  have hn := hermitian_norm_le_of_order hhH hlo (hup h hh)
  rw [NumericalRegularityObjective.slope, ← signedLift_sum_smul]
  exact signedLift_norm_le hhH hn

theorem objective_norm_le_on_ball {ζ μ ρ θ : ℝ}
    (hζ : 0 < ζ) (hζone : ζ ≤ 1) (hμ : 0 < μ) (hρ : 0 < ρ)
    (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    (hparseval : (∑ i, KSRankOne.atom (v i)) ≤ 1) (x h : ι → ℝ) (t : ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (hfloor : μ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤ S)
    (hSnorm : ‖S‖ ≤ 1) (hx : ∀ i, |x i + t * h i| ≤ 1 - ρ) (hh : ∀ i, |h i| ≤ 2)
    (hcenter : ‖complexCenter M v h (t : ℂ)‖ ≤ 2)
    (p : KSComplexSpinSource.Space n)
    (hp : p ∈ Metric.ball ((t : ℂ),S) (NumericalRegularity.radius μ ρ ζ)) :
    ‖objective ζ M v θ x h p‖ ≤ 10000 * ((Fintype.card (n ⊕ n) : ℝ) + 1) ^ 2 := by
  have hn : ‖p - ((t : ℂ),S)‖ < NumericalRegularity.radius μ ρ ζ := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hp
  have ht : ‖p.1 - (t : ℂ)‖ ≤ NumericalRegularity.radius μ ρ ζ := (le_max_left _ _).trans hn.le
  have hS : ‖p.2 - S‖ ≤ NumericalRegularity.radius μ ρ ζ := (le_max_right _ _).trans hn.le
  have hr := NumericalRegularity.radius_le_one μ ρ ζ
  have htone : ‖p.1 - (t : ℂ)‖ ≤ 1 := by linarith
  have hStwo : ‖p.2‖ ≤ 2 := by
    have hb := norm_add_le (p.2 - S) S
    rw [sub_add_cancel] at hb
    linarith
  have hsource : ‖NumericalRegularitySource.source ζ v x h p‖ ≤ 6400 * Fintype.card n := by
    have hb := source_norm_le hζ.le hζone v hparseval (fun i => x i + t * h i) h
      (fun i => by have hi := hx i; linarith) hh (p.1 - t) htone p.2 hStwo
    rw [← NumericalRegularitySource.source_shift] at hb
    have he : ((t : ℂ) + (p.1 - t),p.2) = p := by ext <;> simp
    rwa [he] at hb
  have hcenter' : ‖complexCenter M v h p.1‖ ≤ 6 := by
    have hb := norm_add_le (complexCenter M v h (t : ℂ)) ((p.1 - t) • slope v h)
    rw [norm_smul] at hb
    have hs := slope_norm_le_two v hparseval h hh
    have hm := mul_le_mul htone hs (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    rw [← complexCenter_shift] at hb
    have he : (t : ℂ) + (p.1 - t) = p.1 := by ring
    rw [he] at hb
    linarith
  exact (NumericalRegularityBounds.objective_norm_le ζ M v x h hθ (by norm_num)
    p hcenter' hStwo hsource (product_domain hζ v x h t S hμ hfloor hρ hx hh p ht hS)
    (density_domain hζ hμ hfloor p.2 hS)).trans (valueCap_le hθ hθone)


def jointCap (μ ρ ζ : ℝ) : ℝ :=
  (10000 * ((Fintype.card (n ⊕ n) : ℝ) + 1) ^ 2) * (10 / NumericalRegularity.radius μ ρ ζ) ^ 4

theorem jointCap_nonneg (μ ρ ζ : ℝ) : 0 ≤ jointCap (n := n) μ ρ ζ := by
  unfold jointCap
  positivity

theorem joint_bounds {ζ μ ρ θ : ℝ} (hζ : 0 < ζ) (hζone : ζ ≤ 1)
    (hμ : 0 < μ) (hρ : 0 < ρ) (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hM : M.IsHermitian)
    (v : ι → n → ℂ) (hparseval : (∑ i, KSRankOne.atom (v i)) ≤ 1)
    (x h : ι → ℝ) (t : ℝ) (q : KSFrobeniusTangent.Coordinates (n ⊕ n))
    (hfloor : μ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤
      (KSFrobeniusTangent.chart (n ⊕ n) q : Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hSnorm : ‖(KSFrobeniusTangent.chart (n ⊕ n) q : Matrix (n ⊕ n) (n ⊕ n) ℂ)‖ ≤ 1)
    (hx : ∀ i, |x i + t * h i| ≤ 1 - ρ) (hh : ∀ i, |h i| ≤ 2)
    (hcenter : ‖complexCenter M v h (t : ℂ)‖ ≤ 2) :
    KSActualEnvelope.secondNorm (NumericalRegularityJoint.realObjective ζ M hM v θ x h) (t,q) ≤ jointCap (n := n) μ ρ ζ ∧
    KSActualEnvelope.thirdNorm (NumericalRegularityJoint.realObjective ζ M hM v θ x h) (t,q) ≤ jointCap (n := n) μ ρ ζ ∧
    KSActualEnvelope.fourthNorm (NumericalRegularityJoint.realObjective ζ M hM v θ x h) (t,q) ≤ jointCap (n := n) μ ρ ζ := by
  let F := objective ζ M v θ x h
  have hbase : KSComplexEnvelopeChart.base (n ⊕ n) + KSComplexEnvelopeChart.jointEmbedding (n ⊕ n) (t,q) =
      ((t : ℂ), (KSFrobeniusTangent.chart (n ⊕ n) q : Matrix (n ⊕ n) (n ⊕ n) ℂ)) :=
    KSComplexEnvelopeChart.base_add_jointEmbedding _ _
  have hF : ContDiffOn ℂ ∞ F
      (Metric.ball (KSComplexEnvelopeChart.base (n ⊕ n) + KSComplexEnvelopeChart.jointEmbedding (n ⊕ n) (t,q))
        (NumericalRegularity.radius μ ρ ζ)) := by
    rw [hbase]
    exact contDiffOn_objective hζ M v θ x h t _ hμ hfloor hρ hx hh
  have hbound : ∀ p ∈ Metric.ball
      (KSComplexEnvelopeChart.base (n ⊕ n) + KSComplexEnvelopeChart.jointEmbedding (n ⊕ n) (t,q))
        (NumericalRegularity.radius μ ρ ζ), ‖F p‖ ≤ 10000 * ((Fintype.card (n ⊕ n) : ℝ) + 1) ^ 2 := by
    rw [hbase]
    exact objective_norm_le_on_ball hζ hζone hμ hρ hθ hθone M v hparseval x h t _
      hfloor hSnorm hx hh hcenter
  have hb := KSComplexEnvelopeChart.chart_derivatives_le_common_cap (n ⊕ n) F
    (NumericalRegularity.radius_pos hμ hρ hζ)
    (show NumericalRegularity.radius μ ρ ζ ≤ 1 by have := NumericalRegularity.radius_le_one μ ρ ζ; linarith)
    (by positivity : 0 ≤ 10000 * ((Fintype.card (n ⊕ n) : ℝ) + 1) ^ 2) hF hbound
  exact KSInputJointBounds.nested_bounds_of_eventuallyEq
    (NumericalRegularityJoint.objective_eventuallyEq hζ M hM v θ x h t q
      (KSComplexSpinDomain.posDef_of_floor hμ hfloor) (fun i => by have hi := hx i; linarith)) hb

end NumericalRegularityParseval
end SeamlessKS
