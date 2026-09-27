import SimpleMS.RealSpectralCutoff
import MatrixSpencer.OwnerShort
import MatrixSpencer.CoefficientSupportFrame
import MatrixSpencer.InverseComparison

open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace SimpleMS
open MatrixSpencer
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev CoefficientSpace (ι : Type*) [Fintype ι] := EuclideanSpace ℝ ι

def highProjection (C : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  if h : C.IsHermitian then RealSpectralCutoff.high h (1/2) else 0

def highSpace (C : Matrix ι ι ℝ) : Submodule ℝ (CoefficientSpace ι) :=
  LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) (highProjection C)).toLinearMap

def movementSpace (C : Matrix ι ι ℝ) (V : Submodule ℝ (CoefficientSpace ι)) := highSpace C ⊓ V

def flatCovariance (C : Matrix ι ι ℝ) (V : Submodule ℝ (CoefficientSpace ι)) : Matrix ι ι ℝ :=
  (1/2 : ℝ) • euclideanProjectionMatrix (movementSpace C V)

lemma highProjection_eq (C : Matrix ι ι ℝ) (hC : C.IsHermitian) :
    highProjection C = RealSpectralCutoff.high hC (1/2) := by simp [highProjection,hC]

lemma highProjection_isStarProjection (C : Matrix ι ι ℝ) (hC : C.IsHermitian) :
    IsStarProjection (highProjection C) := by
  rw [highProjection_eq C hC,isStarProjection_iff']
  exact ⟨RealSpectralCutoff.high_idempotent hC _, (RealSpectralCutoff.high_hermitian hC _).eq⟩

lemma projectionMatrix_mul_of_range {P : Matrix ι ι ℝ} (hP : P * P = P)
    (W : Submodule ℝ (CoefficientSpace ι))
    (hW : W ≤ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) P).toLinearMap) :
    P * euclideanProjectionMatrix W = euclideanProjectionMatrix W := by
  apply (Matrix.toEuclideanCLM (𝕜 := ℝ)).injective
  change Matrix.toEuclideanCLM (𝕜 := ℝ) (P * euclideanProjectionMatrix W) = Matrix.toEuclideanCLM (𝕜 := ℝ) (euclideanProjectionMatrix W)
  rw [map_mul]
  change Matrix.toEuclideanCLM (𝕜 := ℝ) P * Matrix.toEuclideanCLM (𝕜 := ℝ) (euclideanProjectionMatrix W) = Matrix.toEuclideanCLM (𝕜 := ℝ) (euclideanProjectionMatrix W)
  rw [toEuclideanCLM_projectionMatrix]
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨y,hy⟩ := hW (W.starProjection_apply_mem x)
  change (Matrix.toEuclideanCLM (𝕜 := ℝ) P) (W.starProjection x) = W.starProjection x
  rw [←hy]
  change (Matrix.toEuclideanCLM (𝕜 := ℝ) P * Matrix.toEuclideanCLM (𝕜 := ℝ) P) y = _
  rw [←map_mul,hP]
  rfl

lemma projectionMatrix_le_of_range {P : Matrix ι ι ℝ} (hP : IsStarProjection P)
    (W : Submodule ℝ (CoefficientSpace ι))
    (hW : W ≤ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) P).toLinearMap) :
    euclideanProjectionMatrix W ≤ P := by
  have hm := projectionMatrix_mul_of_range hP.isIdempotentElem.eq W hW
  exact sub_nonneg.mp ((euclideanProjectionMatrix_isStarProjection W).sub_of_mul_eq_right hP hm).nonneg

lemma flatCovariance_posSemidef (C : Matrix ι ι ℝ) (V : Submodule ℝ (CoefficientSpace ι)) :
    (flatCovariance C V).PosSemidef :=
  (euclideanProjectionMatrix_posSemidef _).smul (by norm_num)

lemma flatCovariance_le {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (V : Submodule ℝ (CoefficientSpace ι)) : flatCovariance C V ≤ C := by
  have hp := projectionMatrix_le_of_range (highProjection_isStarProjection C hC.isHermitian)
    (movementSpace C V) (show movementSpace C V ≤ highSpace C from inf_le_left)
  have hc := RealSpectralCutoff.high_le_inv_smul hC (show (0:ℝ)<1/2 by norm_num)
  rw [←highProjection_eq C hC.isHermitian] at hc
  have hh := smul_le_smul_of_nonneg_left (hp.trans hc) (show (0:ℝ)≤1/2 by norm_num)
  norm_num [smul_smul] at hh
  exact hh

lemma flatCovariance_trace (C : Matrix ι ι ℝ) (V : Submodule ℝ (CoefficientSpace ι)) :
    realTrace (flatCovariance C V) = (Module.finrank ℝ (movementSpace C V) : ℝ)/2 := by
  rw [flatCovariance,realTrace_smul,euclideanProjectionMatrix_trace]
  ring

lemma flatCovariance_range (C : Matrix ι ι ℝ) (V : Submodule ℝ (CoefficientSpace ι)) :
    LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) (flatCovariance C V)).toLinearMap ≤ V := by
  rintro _ ⟨x,rfl⟩
  change (Matrix.toEuclideanCLM (𝕜 := ℝ) (flatCovariance C V)) x ∈ V
  rw [flatCovariance,map_smul,toEuclideanCLM_projectionMatrix]
  exact V.smul_mem _ ((show movementSpace C V ≤ V from inf_le_right) ((movementSpace C V).starProjection_apply_mem x))

lemma eigenvalue_le_one {C : Matrix ι ι ℝ} (hC : C.IsHermitian) (hC1 : C ≤ 1) (j : ι) :
    hC.eigenvalues j ≤ 1 := by
  have hh := InverseComparison.quadratic_mono hC1 (WithLp.ofLp (hC.eigenvectorBasis j))
  have hn : WithLp.ofLp (hC.eigenvectorBasis j) ⬝ᵥ WithLp.ofLp (hC.eigenvectorBasis j) = 1 := by
    have hu := real_inner_self_eq_norm_sq (hC.eigenvectorBasis j)
    rw [hC.eigenvectorBasis.orthonormal.norm_eq_one j] at hu
    simpa only [PiLp.inner_apply,RCLike.inner_apply,star_trivial,dotProduct,one_pow,mul_comm] using hu
  dsimp only [InverseComparison.quadratic] at hh
  rw [hC.mulVec_eigenvectorBasis,Matrix.one_mulVec,dotProduct_smul,hn] at hh
  simpa only [smul_eq_mul,mul_one] using hh

lemma highProjection_trace_lower {C : Matrix ι ι ℝ} (hC : C.IsHermitian) (hC1 : C ≤ 1) :
    (Fintype.card ι : ℝ) - 2 * realTrace (1-C) ≤ realTrace (highProjection C) := by
  rw [realTrace_sub,highProjection_eq C hC,RealSpectralCutoff.high,RealSpectralCutoff.spectralMatrix_trace]
  have ht : realTrace (1 : Matrix ι ι ℝ) = (Fintype.card ι : ℝ) := by simp [realTrace]
  rw [ht]
  have he : realTrace C = ∑ j, hC.eigenvalues j := hC.trace_eq_sum_eigenvalues
  rw [he]
  have hb : (∑ j, (1 - 2 * (1-hC.eigenvalues j))) ≤
      ∑ j, if (1/2 : ℝ) ≤ hC.eigenvalues j then 1 else 0 := by
    apply Finset.sum_le_sum
    intro j _
    have hj := eigenvalue_le_one hC hC1 j
    split_ifs with hjhalf
    · linarith
    · have hh := lt_of_not_ge hjhalf
      linarith
  have heSum : (∑ j, (1 - 2 * (1-hC.eigenvalues j))) =
      (Fintype.card ι : ℝ) - 2 * ((Fintype.card ι : ℝ) - ∑ j, hC.eigenvalues j) := by
    rw [Finset.sum_sub_distrib,←Finset.mul_sum,Finset.sum_sub_distrib]
    simp
  rw [heSum] at hb
  exact hb

lemma matrix_trace_eq_finrank_range {P : Matrix ι ι ℝ} (hP : P*P=P) :
    realTrace P = (Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) P).toLinearMap) : ℝ) := by
  let L := (Matrix.toEuclideanCLM (𝕜 := ℝ) P).toLinearMap
  have hi : IsIdempotentElem L := by
    change L*L=L
    apply LinearMap.ext
    intro x
    change (Matrix.toEuclideanCLM (𝕜 := ℝ) P * Matrix.toEuclideanCLM (𝕜 := ℝ) P) x = _
    rw [←map_mul,hP]
    rfl
  have ht := (LinearMap.IsIdempotentElem.isProj_range L hi).trace
  dsimp only [L] at ht
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
    Matrix.toEuclideanLin_eq_toLin_orthonormal,Matrix.trace_toLin_eq] at ht
  exact ht

lemma flatCovariance_trace_lower {C : Matrix ι ι ℝ} (hC : C.IsHermitian) (hC1 : C ≤ 1)
    (V : Submodule ℝ (CoefficientSpace ι)) :
    ((Fintype.card ι : ℝ) - 2*realTrace (1-C) - (Module.finrank ℝ Vᗮ : ℝ))/2 ≤
      realTrace (flatCovariance C V) := by
  have hh := highProjection_trace_lower hC hC1
  rw [matrix_trace_eq_finrank_range (highProjection_isStarProjection C hC).isIdempotentElem.eq] at hh
  change (Fintype.card ι : ℝ)-2*realTrace (1-C) ≤ (Module.finrank ℝ (highSpace C) : ℝ) at hh
  have hi := (highSpace C).finrank_sup_add_finrank_inf_eq V
  have hu := (highSpace C ⊔ V).finrank_le
  have hv := V.finrank_add_finrank_orthogonal
  have hspace : Module.finrank ℝ (CoefficientSpace ι) = Fintype.card ι := by simp [CoefficientSpace]
  rw [hspace] at hu hv
  have hd : Module.finrank ℝ (highSpace C) ≤ Module.finrank ℝ (movementSpace C V) + Module.finrank ℝ Vᗮ := by
    dsimp only [movementSpace]
    omega
  have hdreal : (Module.finrank ℝ (highSpace C) : ℝ) ≤ (Module.finrank ℝ (movementSpace C V) : ℝ) + (Module.finrank ℝ Vᗮ : ℝ) := by exact_mod_cast hd
  rw [flatCovariance_trace]
  linarith

end SimpleMS
