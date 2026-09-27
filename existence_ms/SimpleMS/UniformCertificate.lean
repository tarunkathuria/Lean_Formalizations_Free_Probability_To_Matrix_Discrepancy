import SimpleMS.UniformMoments
import MatrixSpencer.OwnerSamplerCertificate

/-! Exact anchored-certificate cancellation and tangent-square increments for
the actual uniform signed spectral-frame sampler. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace SimpleMS.UniformCertificate
open MatrixSpencer UniformSampler UniformMoments
variable {N : ℕ}

theorem linear_mean (W : Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    (g : EuclideanSpace ℝ (Fin N)→ₗ[ℝ]ℝ) :
    (∑s,weight W s*g (increment W s))=0 := by
  have hm := congrArg g (mean_zero W)
  simpa only [map_sum,map_smul,smul_eq_mul,map_zero] using hm

theorem dot_mean (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (g : Fin N→ℝ) :
    (∑s,weight W s*(g⬝ᵥWithLp.ofLp (increment W s)))=0 := by
  apply linear_mean W {
    toFun:=fun u=>g⬝ᵥWithLp.ofLp u
    map_add':=by intro x y; simp only [WithLp.ofLp_add,dotProduct_add]
    map_smul':=by intro t x; simp only [WithLp.ofLp_smul,dotProduct_smul,smul_eq_mul,RingHom.id_apply] }

theorem dot_square (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (hQ : (covMatrix W).PosSemidef)
    (hq : 0<realTrace (covMatrix W)) (g : Fin N→ℝ) :
    (∑s,weight W s*(g⬝ᵥWithLp.ofLp (increment W s))^2)=g⬝ᵥ(covMatrix W*ᵥg) := by
  have h := quadratic_expectation W hQ hq (realRankOne g)
  rw [realTrace_mul_comm,realTrace_rankOne_mul] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  simp only [realRankOne,Matrix.vecMulVec_mulVec,dotProduct_smul,op_smul_eq_smul,smul_eq_mul]
  rw [dotProduct_comm (WithLp.ofLp (increment W s)) g]
  ring

theorem affine_square (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (hQ : (covMatrix W).PosSemidef)
    (hq : 0<realTrace (covMatrix W)) (g : Fin N→ℝ) (m h : ℝ) :
    (∑s,weight W s*(m+h*(g⬝ᵥWithLp.ofLp (increment W s)))^2)=m^2+h^2*(g⬝ᵥ(covMatrix W*ᵥg)) := by
  have he (s : Draws W) : weight W s*(m+h*(g⬝ᵥWithLp.ofLp (increment W s)))^2=
      weight W s*m^2+2*m*h*(weight W s*(g⬝ᵥWithLp.ofLp (increment W s)))+
        h^2*(weight W s*(g⬝ᵥWithLp.ofLp (increment W s))^2) := by ring
  simp only [he,Finset.sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum,
    weights_sum W (rank_positive W hq),dot_mean W g,dot_square W hQ hq g,mul_zero,add_zero,one_mul]

variable {d : ℕ} [Nonempty (Fin d)]
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
local instance : NormedSpace ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) := inferInstance

theorem physical_linear_mean (A : Fin N→Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (S : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) :
    (∑s,weight W s*tracePairing S (ownerPhysicalIncrement A hA (increment W s)))=0 := by
  simpa only [LinearMap.comp_apply,ContinuousLinearMap.coe_coe,ownerPhysicalIncrementLinear] using
    linear_mean W ((tracePairing (S : Matrix (Fin d) (Fin d) ℂ)).toLinearMap.comp
      (ownerPhysicalIncrementLinear A hA))

/-- Exact cancellation of the fixed anchor gradient in the actual sampler. -/
theorem certificate_drift_eq (Hstar : Matrix (Fin d) (Fin d) ℂ)
    (A : Fin N→Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian) (θ : ℝ)
    (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) (C : Matrix (Fin N) (Fin N) ℝ) (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (h : ℝ) :
    (∑s,weight W s*(ownerCertificate Hstar A θ (H+h•ownerPhysicalIncrement A hA (increment W s))
      (C-h^2•covMatrix W)-ownerCertificate Hstar A θ H C))=
    ∑s,weight W s*(ownerPotential (H+h•ownerPhysicalIncrement A hA (increment W s)) A (C-h^2•covMatrix W) θ-
      ownerPotential H A C θ) := by
  let S : selfAdjoint (Matrix (Fin d) (Fin d) ℂ) :=
    ⟨ownerCertificateDensity Hstar θ,(ownerCertificateDensity_mem Hstar θ).1.isHermitian⟩
  have hz := physical_linear_mean A hA W S
  simp only [ownerCertificate_sampled_difference,mul_sub,Finset.sum_sub_distrib]
  have he : (∑s,weight W s*(h*tracePairing (ownerCertificateDensity Hstar θ)
      (ownerPhysicalIncrement A hA (increment W s))))=0 := by
    calc
      _=h*∑s,weight W s*tracePairing S (ownerPhysicalIncrement A hA (increment W s)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
      _=0 := by rw [hz,mul_zero]
  rw [he,sub_zero]

/-- Actual saved-anchor tangent second moment, with the unit family bound
supplying the covariance quadratic bound. -/
theorem tangent_square_le (Hstar : Matrix (Fin d) (Fin d) ℂ)
    (A : Fin N→Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian) (hAn : ∀i,‖A i‖≤1) (θ : ℝ)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (hQ : (covMatrix W).PosSemidef) (hQ1 : covMatrix W≤1) (hq : 0<realTrace (covMatrix W)) (m h : ℝ) :
    (∑s,weight W s*(m+h*(ownerCertificateGradient Hstar A θ⬝ᵥWithLp.ofLp (increment W s)))^2)≤ m^2+h^2*N := by
  rw [affine_square W hQ hq]
  have hb := (ownerCertificateGradient_covariance_bound Hstar A hA hAn θ hQ hQ1).2
  simp only [Fintype.card_fin] at hb
  exact add_le_add_left (mul_le_mul_of_nonneg_left hb (sq_nonneg h)) _

end SimpleMS.UniformCertificate
