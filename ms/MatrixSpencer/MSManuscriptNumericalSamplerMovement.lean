import MatrixSpencer.MSManuscriptNumericalSampler
import MatrixSpencer.CovarianceMovement
import MatrixSpencer.MSManuscriptAdaptive

/-! Exact covariance-matched withdrawal for the actual finite LDL sampler.
Every draw satisfies annihilating linear constraints, so radial orthogonality
produces deterministic squared-norm progress on every branch. -/
open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.MSManuscriptNumericalSamplerMovement
open MSManuscriptNumericalSampler
variable {d : ℕ}

def sample (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosSemidef) (hq : 0<realTrace Q) :
    MSManuscriptAdaptive.Sampler (EuclideanSpace ℝ (Fin d)) where
  Draws := Draws Q
  fintypeDraws := inferInstance
  weight := weight Q
  value := increment Q
  weight_nonneg := fun s => (weight_pos Q hq s).le
  weight_sum := weight_sum Q hQ hq

def move (Q : Matrix (Fin d) (Fin d) ℝ) (x : EuclideanSpace ℝ (Fin d)) (h : ℝ) (s : Draws Q) :=
  x+h • increment Q s

def withdraw (C Q : Matrix (Fin d) (Fin d) ℝ) (h : ℝ) := C-h^2 • Q

theorem constraint {E : Type*} [AddCommGroup E] [Module ℝ E]
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosSemidef)
    (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] E)
    (hT : T.comp (Matrix.toEuclideanCLM (𝕜 := ℝ) Q).toLinearMap=0) (s : Draws Q) :
    T (increment Q s)=0 := by
  obtain ⟨u,hu⟩ := increment_mem_range Q hQ s
  rw [←hu]
  exact LinearMap.congr_fun hT u

theorem orthogonal_of_annihilator (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosSemidef)
    (x : EuclideanSpace ℝ (Fin d)) (hx : Q*ᵥWithLp.ofLp x=0) (s : Draws Q) :
    inner ℝ x (increment Q s)=0 := by
  obtain ⟨u,hu⟩ := increment_mem_range Q hQ s
  rw [←hu]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (Q*ᵥWithLp.ofLp u)⬝ᵥWithLp.ofLp x=0
  rw [dotProduct_comm]
  rw [InverseComparison.symmetric_pairing hQ.isHermitian, hx,dotProduct_zero]

theorem frozen_increment (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosSemidef)
    (i : Fin d) (hi : Q*ᵥ(Pi.single i 1)=0) (s : Draws Q) : increment Q s i=0 := by
  have h := orthogonal_of_annihilator Q hQ (EuclideanSpace.single i 1) hi s
  simpa only [EuclideanSpace.inner_single_left,map_one,one_mul] using h

theorem norm_gain (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosSemidef)
    (x : EuclideanSpace ℝ (Fin d)) (hx : Q*ᵥWithLp.ofLp x=0) (h : ℝ) (s : Draws Q) :
    ‖move Q x h s‖^2=‖x‖^2+h^2*realTrace Q := by
  rw [move,norm_add_sq_real,real_inner_smul_right,orthogonal_of_annihilator Q hQ x hx s,
    mul_zero,mul_zero,add_zero,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,
    increment_norm_sq Q (realTrace_nonneg hQ)]

theorem frozen_preserved (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosSemidef)
    (x : EuclideanSpace ℝ (Fin d)) (h : ℝ) (s : Draws Q) (i : Fin d)
    (hi : Q*ᵥ(Pi.single i 1)=0) : move Q x h s i=x i := by
  change x i+h*increment Q s i=x i
  rw [frozen_increment Q hQ i hi s,mul_zero,add_zero]

theorem quadratic_expectation (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosSemidef)
    (hq : 0<realTrace Q) (G : Matrix (Fin d) (Fin d) ℝ) :
    (∑ s : Draws Q,weight Q s*(WithLp.ofLp (increment Q s)⬝ᵥ(G*ᵥWithLp.ofLp (increment Q s))))=
      realTrace (Q*G) := by
  conv_rhs => rw [←covariance Q hQ hq]
  rw [Matrix.sum_mul,realTrace_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Matrix.smul_mul,realTrace_smul,realTrace_rankOne_mul]

theorem linear_expectation (Q : Matrix (Fin d) (Fin d) ℝ)
    (g : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ) :
    (∑ s : Draws Q,weight Q s*g (increment Q s))=0 := by
  have h := congrArg g (mean_zero Q)
  simpa only [map_sum,map_smul,smul_eq_mul,map_zero] using h

/-- The actual covariance removed is exactly the actual second moment, with no
rational-normalization perturbation in this real-arithmetic specialization. -/
theorem withdrawal_matched (C Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosSemidef)
    (hq : 0<realTrace Q) (h : ℝ) :
    withdraw C Q h=C-h^2 • (∑ s : Draws Q,weight Q s • realRankOne (WithLp.ofLp (increment Q s))) := by
  rw [covariance Q hQ hq]
  rfl

theorem withdrawal_trace (C Q : Matrix (Fin d) (Fin d) ℝ) (h : ℝ) :
    realTrace (withdraw C Q h)=realTrace C-h^2*realTrace Q := covarianceMovement_trace C Q h

theorem withdrawal_lower (C Q : Matrix (Fin d) (Fin d) ℝ) (hQC : Q≤C) (h : ℝ) :
    (1-h^2) • C≤withdraw C Q h := covarianceMovement_lower hQC h

theorem withdrawal_valid (C Q : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef)
    (hQ : Q.PosSemidef) (hQC : Q≤C) {h : ℝ} (hh : h^2<1) :
    (withdraw C Q h).PosSemidef ∧ withdraw C Q h≤C ∧
      LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) (withdraw C Q h)).toLinearMap=
        LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) C).toLinearMap :=
  covarianceMovement_posSemidef_range hC hQ hQC hh

end MatrixSpencer.MSManuscriptNumericalSamplerMovement
