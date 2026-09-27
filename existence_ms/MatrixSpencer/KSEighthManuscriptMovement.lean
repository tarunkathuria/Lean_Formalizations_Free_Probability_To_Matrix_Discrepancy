import MatrixSpencer.KSEighthManuscriptSampler
import MatrixSpencer.KSEighthLiveCoordinates



open Matrix Set
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.KSEighthManuscriptMovement
open KSEighthLiveEnumeration KSEighthLiveCoordinates KSEighthManuscriptSampler
variable {N : ℕ}

def livePoint (x : Fin N → ℝ) : Fin (count x) → ℝ := fun j => x (liveEquiv x j)

def physicalCovariance (x : Fin N → ℝ) (Q : Matrix (Fin (count x)) (Fin (count x)) ℝ) :=
  KSSymmetricProgress.scaledCovariance (livePoint x) Q

def increment (x : Fin N → ℝ) (Q : Matrix (Fin (count x)) (Fin (count x)) ℝ)
    (z : Fin (count x) × Bool) : EuclideanSpace ℝ (Fin N) :=
  extend x (KSEighthManuscriptSampler.increment (physicalCovariance x Q) z)

def proposal (x : Fin N → ℝ) (Q : Matrix (Fin (count x)) (Fin (count x)) ℝ)
    (h : ℝ) (z : Fin (count x) × Bool) : Fin N → ℝ :=
  WithLp.ofLp ((WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N)) + h • increment x Q z)

theorem count_le (x : Fin N → ℝ) : count x ≤ N := by
  unfold count labels
  simpa using List.length_filter_le (fun i : Fin N => decide (|x i| < (1/8 : ℝ))) (List.finRange N)

theorem physicalCovariance_posSemidef (x : Fin N → ℝ)
    {Q : Matrix (Fin (count x)) (Fin (count x)) ℝ} (hQ : Q.PosSemidef) :
    (physicalCovariance x Q).PosSemidef := KSSymmetricProgress.scaledCovariance_posSemidef _ hQ

theorem physicalCovariance_le_one (x : Fin N → ℝ)
    {Q : Matrix (Fin (count x)) (Fin (count x)) ℝ} (hQ1 : Q ≤ 1) :
    physicalCovariance x Q ≤ 1 := by
  let D := Matrix.diagonal (fun j => Real.sqrt (1 - livePoint x j ^ 2))
  have hm := (Matrix.le_iff.mp hQ1).mul_mul_conjTranspose_same D
  have hD : Dᴴ = D := by simp [D]
  rw [hD, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one] at hm
  have hupper : D * D ≤ (1 : Matrix (Fin (count x)) (Fin (count x)) ℝ) := by
    apply Matrix.le_iff.mpr
    have he : 1 - D*D = Matrix.diagonal (fun j => 1 - Real.sqrt (1 - livePoint x j^2)^2) := by
      simp [D, ← Matrix.diagonal_mul, ← Matrix.diagonal_sub, pow_two]
    rw [he]
    apply Matrix.PosSemidef.diagonal
    intro j
    have hs := Real.sqrt_le_one.mpr (show 1 - livePoint x j^2 ≤ 1 by nlinarith [sq_nonneg (livePoint x j)])
    change 0 ≤ 1 - Real.sqrt (1 - livePoint x j^2)^2
    nlinarith [Real.sqrt_nonneg (1 - livePoint x j^2)]
  exact (Matrix.le_iff.mpr hm).trans hupper

theorem increment_frozen (x : Fin N → ℝ)
    (Q : Matrix (Fin (count x)) (Fin (count x)) ℝ) (z : Fin (count x) × Bool)
    (i : Fin N) (hi : |x i| = (1/8 : ℝ)) : increment x Q z i = 0 :=
  extend_frozen x _ i hi

theorem increment_norm_le (x : Fin N → ℝ)
    {Q : Matrix (Fin (count x)) (Fin (count x)) ℝ} (hQ : Q.PosSemidef) (hQ1 : Q ≤ 1)
    (z : Fin (count x) × Bool) : ‖increment x Q z‖ ≤ Real.sqrt (N : ℝ) := by
  rw [increment, extend_norm]
  exact (KSEighthManuscriptSampler.increment_norm_le (physicalCovariance_posSemidef x hQ)
    (physicalCovariance_le_one x hQ1) z).trans (Real.sqrt_le_sqrt (by exact_mod_cast count_le x))

theorem proposal_frozen (x : Fin N → ℝ)
    (Q : Matrix (Fin (count x)) (Fin (count x)) ℝ) (h : ℝ)
    (z : Fin (count x) × Bool) (i : Fin N) (hi : |x i| = (1/8 : ℝ)) :
    proposal x Q h z i = x i := by
  change x i + h * increment x Q z i = x i
  rw [increment_frozen x Q z i hi, mul_zero, add_zero]

theorem proposal_mem_cube {x : Fin N → ℝ} (hx : x ∈ ksCube (1/8))
    {Q : Matrix (Fin (count x)) (Fin (count x)) ℝ} (hQ : Q.PosSemidef) (hQ1 : Q ≤ 1)
    {h ρ : ℝ} (hstep : |h| * Real.sqrt (N : ℝ) ≤ ρ)
    (hm : ∀ i, |x i| < 1/8 → ρ < 1/8 - |x i|) (z : Fin (count x) × Bool) :
    proposal x Q h z ∈ ksCube (1/8) := by
  have hall (i : Fin N) : |proposal x Q h z i| ≤ (1/8 : ℝ) := by
    rcases lt_or_eq_of_le (abs_le.mpr ⟨hx.1 i, hx.2 i⟩) with hi | hi
    · have hb : |increment x Q z i| ≤ Real.sqrt (N : ℝ) :=
        calc
          _ ≤ ‖increment x Q z‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (increment x Q z) i
          _ ≤ _ := increment_norm_le x hQ hQ1 z
      have he : |proposal x Q h z i| ≤ |x i| + |h| * |increment x Q z i| := by
        change |x i + h * increment x Q z i| ≤ _
        exact (abs_add_le _ _).trans_eq (by rw [abs_mul])
      have hs := mul_le_mul_of_nonneg_left hb (abs_nonneg h)
      linarith [hm i hi]
    · rw [proposal_frozen x Q h z i hi, hi]
  exact ⟨fun i => (abs_le.mp (hall i)).1, fun i => (abs_le.mp (hall i)).2⟩

theorem increment_mean_zero (x : Fin N → ℝ)
    (Q : Matrix (Fin (count x)) (Fin (count x)) ℝ) :
    (∑ z, weight z • increment x Q z) = 0 := by
  have he := congrArg (extensionLinear x) (KSEighthManuscriptSampler.mean_zero (physicalCovariance x Q))
  simpa only [map_sum, map_smul, map_zero] using he

theorem proposal_energy_mean (x : Fin N → ℝ)
    {Q : Matrix (Fin (count x)) (Fin (count x)) ℝ} (hQ : Q.PosSemidef)
    (hk : 0 < count x) (h : ℝ) :
    (∑ z, weight z * KSCubePreparation.energy (proposal x Q h z)) =
      KSCubePreparation.energy x + h^2 * realTrace (physicalCovariance x Q) := by
  simp only [proposal, KSSymmetricProgress.energy_eq_norm_sq, WithLp.toLp_ofLp]
  rw [KSSymmetricProgress.weighted_centered_norm_sq _ _ _ _ (weight_sum hk) (increment_mean_zero x Q)]
  have he := KSEighthManuscriptSampler.mean_norm_sq (physicalCovariance_posSemidef x hQ) hk 0 1
  simp only [zero_add, one_smul, norm_zero, zero_pow (by decide : 2 ≠ 0), one_pow, zero_add, one_mul] at he
  simp only [increment, extend_norm]
  rw [he]

theorem proposal_energy_progress (x : Fin N → ℝ)
    {Q : Matrix (Fin (count x)) (Fin (count x)) ℝ} (hQ : Q.PosSemidef)
    (hk : 0 < count x) (htrace : (3/4 : ℝ)*count x ≤ Matrix.trace Q) (h : ℝ) :
    KSCubePreparation.energy x + h^2/2 ≤
      ∑ z, weight z * KSCubePreparation.energy (proposal x Q h z) := by
  rw [proposal_energy_mean x hQ hk]
  have ht := KSSymmetricProgress.eighth_scaledCovariance_trace_lower (livePoint x) hQ
    (fun j => (liveEquiv x j).property.le) (by simpa using hk)
    (by simpa only [Fintype.card_fin, realTrace, RCLike.re_to_real, div_mul_eq_mul_div] using htrace)
  change (1/2 : ℝ) ≤ realTrace (physicalCovariance x Q) at ht
  nlinarith [mul_le_mul_of_nonneg_left ht (sq_nonneg h)]

end MatrixSpencer.KSEighthManuscriptMovement
