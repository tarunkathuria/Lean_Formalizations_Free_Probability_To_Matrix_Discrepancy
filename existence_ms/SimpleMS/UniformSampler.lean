import SimpleMS.SpectralFrame
import MatrixSpencer.CovarianceSampler
import MatrixSpencer.MSManuscriptAdaptive

open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace SimpleMS.UniformSampler
open MatrixSpencer
variable {ι : Type} [Fintype ι] [DecidableEq ι]

abbrev Index (W : Submodule ℝ (EuclideanSpace ℝ ι)) := SpectralFrame.Index W
abbrev Draws (W : Submodule ℝ (EuclideanSpace ℝ ι)) := Index W × Bool

def basisVector (W : Submodule ℝ (EuclideanSpace ℝ ι)) (j : Index W) : EuclideanSpace ℝ ι :=
  SpectralFrame.vector W j

def weight (W : Submodule ℝ (EuclideanSpace ℝ ι)) (_ : Draws W) : ℝ :=
  1 / (2 * (Module.finrank ℝ W : ℝ))

def increment (W : Submodule ℝ (EuclideanSpace ℝ ι)) (s : Draws W) : EuclideanSpace ℝ ι :=
  if s.2 then Real.sqrt ((Module.finrank ℝ W : ℝ)/2) • basisVector W s.1
  else -(Real.sqrt ((Module.finrank ℝ W : ℝ)/2) • basisVector W s.1)

lemma weight_positive (W : Submodule ℝ (EuclideanSpace ℝ ι)) (hW : 0 < Module.finrank ℝ W) (s : Draws W) :
    0 < weight W s := by unfold weight; positivity

lemma weights_sum (W : Submodule ℝ (EuclideanSpace ℝ ι)) (hW : 0 < Module.finrank ℝ W) :
    (∑ s : Draws W, weight W s) = 1 := by
  have hr : (0:ℝ) < Module.finrank ℝ W := by exact_mod_cast hW
  simp only [weight,Finset.sum_const,Finset.card_univ,Fintype.card_prod,SpectralFrame.card_index,Fintype.card_bool,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
  field_simp

lemma mean_zero (W : Submodule ℝ (EuclideanSpace ℝ ι)) :
    (∑ s : Draws W, weight W s • increment W s) = 0 := by
  rw [Fintype.sum_prod_type]
  simp [weight,increment]

lemma increment_mem (W : Submodule ℝ (EuclideanSpace ℝ ι)) (s : Draws W) : increment W s ∈ W := by
  unfold increment
  split_ifs
  · exact W.smul_mem _ (SpectralFrame.vector_mem W s.1)
  · exact W.neg_mem (W.smul_mem _ (SpectralFrame.vector_mem W s.1))

lemma increment_norm_sq (W : Submodule ℝ (EuclideanSpace ℝ ι)) (s : Draws W) :
    ‖increment W s‖^2 = (Module.finrank ℝ W : ℝ)/2 := by
  have hn : ‖basisVector W s.1‖=1 := SpectralFrame.vector_norm W s.1
  rcases s with ⟨j,b⟩
  cases b <;> simp only [increment,Bool.false_eq_true,↓reduceIte,norm_neg,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),hn,mul_one,Real.sq_sqrt (by positivity : (0:ℝ)≤(Module.finrank ℝ W : ℝ)/2)]

lemma frame_projection (W : Submodule ℝ (EuclideanSpace ℝ ι)) :
    CoefficientSupportFrame.frame W * (CoefficientSupportFrame.frame W)ᵀ = euclideanProjectionMatrix W := by
  have hr : LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) (euclideanProjectionMatrix W)).toLinearMap ≤ W := by
    rw [toEuclideanCLM_projectionMatrix]
    rintro _ ⟨x,rfl⟩
    exact W.starProjection_apply_mem x
  have hh := CoefficientSupportFrame.reconstruct_of_range W (euclideanProjectionMatrix_posSemidef W).isHermitian hr
  simpa only [CoefficientSupportFrame.reduced_projection,covarianceLift,Matrix.mul_one] using hh

lemma basis_rankOne_sum (W : Submodule ℝ (EuclideanSpace ℝ ι)) :
    (∑ j : Index W, realRankOne (WithLp.ofLp (basisVector W j))) = euclideanProjectionMatrix W :=
  SpectralFrame.rankOne_sum W

lemma increment_rankOne (W : Submodule ℝ (EuclideanSpace ℝ ι)) (s : Draws W) :
    realRankOne (WithLp.ofLp (increment W s)) =
      ((Module.finrank ℝ W : ℝ)/2) • realRankOne (WithLp.ofLp (basisVector W s.1)) := by
  rcases s with ⟨j,b⟩
  cases b <;> simp only [increment,Bool.false_eq_true,↓reduceIte,WithLp.ofLp_neg,
    WithLp.ofLp_smul,realRankOne_neg,realRankOne_smul,Real.sq_sqrt (by positivity : (0:ℝ)≤(Module.finrank ℝ W : ℝ)/2)]

lemma covariance (W : Submodule ℝ (EuclideanSpace ℝ ι)) (hW : 0 < Module.finrank ℝ W) :
    (∑ s : Draws W, weight W s • realRankOne (WithLp.ofLp (increment W s))) =
      (1/2 : ℝ) • euclideanProjectionMatrix W := by
  have hr : (0:ℝ) < Module.finrank ℝ W := by exact_mod_cast hW
  rw [Fintype.sum_prod_type]
  simp only [increment_rankOne,weight,Fintype.sum_bool,smul_smul]
  have hh : 1 / (2 * (Module.finrank ℝ W : ℝ)) * ((Module.finrank ℝ W : ℝ)/2) +
      1 / (2 * (Module.finrank ℝ W : ℝ)) * ((Module.finrank ℝ W : ℝ)/2) = (1/2 : ℝ) := by field_simp; ring
  simp only [←add_smul,hh]
  rw [←Finset.smul_sum,basis_rankOne_sum]

def sample (W : Submodule ℝ (EuclideanSpace ℝ ι)) (hW : 0 < Module.finrank ℝ W) :
    MSManuscriptAdaptive.Sampler (EuclideanSpace ℝ ι) where
  Draws := Draws W
  fintypeDraws := inferInstance
  weight := weight W
  value := increment W
  weight_nonneg s := (weight_positive W hW s).le
  weight_sum := weights_sum W hW

end SimpleMS.UniformSampler
