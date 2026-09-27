import MatrixSpencer.KSEighthManuscriptParameters
import MatrixSpencer.KSEighthManuscriptNormalizedSampler

/-! Exact equality of the sampled movement and its smooth retained-mask chart. -/

open Matrix Set
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.KSEighthManuscriptDriftGeometry
open KSEighthLiveEnumeration KSEighthLiveCoordinates KSEighthManuscriptMovement
variable {N d : ℕ}

theorem weightedMap_normalized (x : Fin N → ℝ)
    (Q : Matrix (Fin (count x)) (Fin (count x)) ℝ) (z : Fin (count x) × Bool) :
    weightedMap x (KSEighthManuscriptNormalizedSampler.normalized (livePoint x) Q z) = increment x Q z := by
  ext i
  rw [weightedMap_apply]
  by_cases hi : |x i| < (1/8 : ℝ)
  · let j : KSLiveCurve.Live (1/8) x := ⟨i,hi⟩
    rw [show i = j.val from rfl, extend_live]
    change Real.sqrt (1-x j^2) * _ = _
    have he := KSEighthManuscriptNormalizedSampler.weighted_normalized (livePoint x)
      (fun a => (liveEquiv x a).property.le) Q z ((liveEquiv x).symm j)
    simp only [livePoint, Equiv.apply_symm_apply] at he
    rw [he]
    exact (extend_live x _ j).symm
  · rw [extend_dead x _ i hi, mul_zero]
    exact (extend_dead x _ i hi).symm

theorem face_scaled_bounded (x : Fin N → ℝ)
    (Q : Matrix (Fin (count x)) (Fin (count x)) ℝ) (h : ℝ) (hN : 0 < N)
    (z : Fin (count x) × Bool) :
    face x ((h*Real.sqrt (N : ℝ)) • KSEighthManuscriptNormalizedSampler.bounded (livePoint x) Q N z) =
      proposal x Q h z := by
  have hs : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
  have he : (h*Real.sqrt (N : ℝ)) • KSEighthManuscriptNormalizedSampler.bounded (livePoint x) Q N z =
      h • KSEighthManuscriptNormalizedSampler.normalized (livePoint x) Q z := by
    unfold KSEighthManuscriptNormalizedSampler.bounded
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ hs, mul_one]
  rw [he]
  funext i
  rw [face,map_smul,weightedMap_normalized]
  rfl

theorem proposal_live_iff {x : Fin N → ℝ} (hx : x ∈ ksCube (1/8))
    {Q : Matrix (Fin (count x)) (Fin (count x)) ℝ} (hQ : Q.PosSemidef) (hQ1 : Q ≤ 1)
    {h ρ : ℝ} (hstep : |h| * Real.sqrt (N : ℝ) ≤ ρ)
    (hm : ∀ i, |x i| < 1/8 → ρ < 1/8 - |x i|) (z : Fin (count x) × Bool) (i : Fin N) :
    |proposal x Q h z i| < (1/8 : ℝ) ↔ |x i| < (1/8 : ℝ) := by
  rcases lt_or_eq_of_le (abs_le.mpr ⟨hx.1 i,hx.2 i⟩) with hi | hi
  · have hb : |increment x Q z i| ≤ Real.sqrt (N : ℝ) :=
      (show |increment x Q z i| ≤ ‖increment x Q z‖ by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (increment x Q z) i).trans
        (increment_norm_le x hQ hQ1 z)
    have ha : |proposal x Q h z i| ≤ |x i| + |h| * |increment x Q z i| := by
      change |x i+h*increment x Q z i| ≤ _
      exact (abs_add_le _ _).trans_eq (by rw [abs_mul])
    have hb' := mul_le_mul_of_nonneg_left hb (abs_nonneg h)
    have hp : |proposal x Q h z i| < (1/8 : ℝ) := by linarith [hm i hi]
    exact iff_of_true hp hi
  · rw [proposal_frozen x Q h z i hi, hi]

theorem proposal_live_mask {x : Fin N → ℝ} (hx : x ∈ ksCube (1/8))
    {Q : Matrix (Fin (count x)) (Fin (count x)) ℝ} (hQ : Q.PosSemidef) (hQ1 : Q ≤ 1)
    {h ρ : ℝ} (hstep : |h| * Real.sqrt (N : ℝ) ≤ ρ)
    (hm : ∀ i, |x i| < 1/8 → ρ < 1/8 - |x i|) (z : Fin (count x) × Bool) :
    KSPotentialModels.live (1/8) (proposal x Q h z) = KSPotentialModels.live (1/8) x := by
  ext i
  simp only [KSPotentialModels.live,Finset.mem_filter,Finset.mem_univ,true_and]
  exact proposal_live_iff hx hQ hQ1 hstep hm z i

/-- Equality at the entire finite query, not merely equality of derivatives at zero. -/
theorem potential_scaled_bounded (v : Fin N → Fin d → ℂ) {θ : ℝ} (hθ : 0 < θ) (hd : 0 < d)
    {x : Fin N → ℝ} (hx : x ∈ ksCube (1/8))
    {Q : Matrix (Fin (count x)) (Fin (count x)) ℝ} (hQ : Q.PosSemidef) (hQ1 : Q ≤ 1)
    {h ρ : ℝ} (hstep : |h| * Real.sqrt (N : ℝ) ≤ ρ) (hN : 0 < N)
    (hm : ∀ i, |x i| < 1/8 → ρ < 1/8 - |x i|) (z : Fin (count x) × Bool) :
    KSEighthFacePotential.potential v θ x
      ((h*Real.sqrt (N : ℝ)) • KSEighthManuscriptNormalizedSampler.bounded (livePoint x) Q N z) =
      KSPotentialModels.eighthPotential (fun i => KSRankOne.atom (v i)) θ (proposal x Q h z) := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have he := face_scaled_bounded x Q h hN z
  rw [KSEighthFacePotential.potential_eq_retained v hθ x _ (by norm_num : (1/8 : ℝ) ≤ 1)
    (by rw [he]; exact proposal_mem_cube hx hQ hQ1 hstep hm z),he]
  unfold KSPotentialModels.eighthPotential KSPotentialModels.truncatedOwners
  rw [proposal_live_mask hx hQ hQ1 hstep hm z]

end MatrixSpencer.KSEighthManuscriptDriftGeometry
