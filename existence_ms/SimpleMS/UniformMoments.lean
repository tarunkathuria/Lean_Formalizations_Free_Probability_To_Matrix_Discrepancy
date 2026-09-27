import SimpleMS.UniformSampler
import MatrixSpencer.FiniteOwnerDrift

/-! Exact pairing, quadratic moments, and physical norms for the uniform signed spectral-frame data. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace SimpleMS.UniformMoments
open MatrixSpencer UniformSampler
variable {N : ℕ}
def covMatrix (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) : Matrix (Fin N) (Fin N) ℝ :=
  (1/2:ℝ) • euclideanProjectionMatrix W
lemma covMatrix_trace (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) :
    realTrace (covMatrix W)=(Module.finrank ℝ W : ℝ)/2 := by
  rw [covMatrix,realTrace_smul,euclideanProjectionMatrix_trace]
  ring
lemma rank_positive (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (hq : 0<realTrace (covMatrix W)) :
    0<Module.finrank ℝ W := by
  rw [covMatrix_trace] at hq
  have hh : (0:ℝ)<Module.finrank ℝ W := by linarith
  exact_mod_cast hh


def flip (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) : Draws W ≃ Draws W where
  toFun s := (s.1,!s.2)
  invFun s := (s.1,!s.2)
  left_inv s := by simp
  right_inv s := by simp

theorem weight_flip (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (s : Draws W) : weight W (flip W s)=weight W s := rfl

theorem increment_flip (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (s : Draws W) :
    increment W (flip W s) = -increment W s := by
  rcases s with ⟨i,b⟩
  cases b <;> simp [increment,flip]

theorem pair_average_eq (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (f : Draws W → ℝ) :
    (∑s,weight W s*f s) = ∑s,weight W s*((f s+f (flip W s))/2) := by
  have he := (flip W).sum_comp (fun s => weight W s*f s)
  simp only [weight_flip] at he
  have hp : (∑s,weight W s*((f s+f (flip W s))/2)) =
      ((∑s,weight W s*f s)+(∑s,weight W s*f (flip W s)))/2 := by
    rw [←Finset.sum_add_distrib,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [hp,he]
  ring

theorem weighted_pair_le (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (hQ : (covMatrix W).PosSemidef)
    (hq : 0<realTrace (covMatrix W)) (f q : Draws W → ℝ) {e : ℝ}
    (hpair : ∀s,(f s+f (flip W s))/2 ≤ q s+e) :
    (∑s,weight W s*f s) ≤ (∑s,weight W s*q s)+e := by
  rw [pair_average_eq W f]
  calc
    _ ≤ ∑s,weight W s*(q s+e) := Finset.sum_le_sum (fun s _ =>
      mul_le_mul_of_nonneg_left (hpair s) (weight_positive W (rank_positive W hq) s).le)
    _ = _ := by rw [Finset.sum_congr rfl (fun s _ => mul_add _ _ _),Finset.sum_add_distrib,
      ←Finset.sum_mul,weights_sum W (rank_positive W hq),one_mul]

theorem quadratic_expectation (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (hQ : (covMatrix W).PosSemidef)
    (hq : 0<realTrace (covMatrix W)) (G : Matrix (Fin N) (Fin N) ℝ) :
    (∑s : Draws W,weight W s*(WithLp.ofLp (increment W s)⬝ᵥ(G*ᵥWithLp.ofLp (increment W s))))=
      realTrace (covMatrix W*G) := by
  change _ = realTrace (((1/2:ℝ) • euclideanProjectionMatrix W)*G)
  conv_rhs => rw [←covariance W (rank_positive W hq)]
  rw [Matrix.sum_mul,realTrace_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Matrix.smul_mul,realTrace_smul,realTrace_rankOne_mul]

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

def physical (A : Fin N → Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (s : Draws W) := ownerPhysicalIncrement A hA (increment W s)

theorem physical_flip (A : Fin N → Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (s : Draws W) : physical A hA W (flip W s) = -physical A hA W s := by
  change ownerPhysicalIncrementLinear A hA (increment W (flip W s)) = -ownerPhysicalIncrementLinear A hA (increment W s)
  rw [increment_flip,map_neg]

def directionCap (N : ℕ) (L : ℝ) : ℝ := Real.sqrt (N : ℝ)*(N : ℝ)*L

theorem directionCap_nonneg {L : ℝ} (hL : 0 ≤ L) : 0 ≤ directionCap N L := by unfold directionCap; positivity

theorem physical_norm_le (A : Fin N → Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian)
    {L : ℝ} (hL : 0≤L) (hAnorm : ∀i,‖A i‖≤L)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (hQ : (covMatrix W).PosSemidef) (hQ1 : covMatrix W≤1) (s : Draws W) :
    ‖(physical A hA W s : Matrix n n ℂ)‖ ≤ directionCap N L := by
  have htr : realTrace (covMatrix W) ≤ (N : ℝ) := by
    have hh := realTrace_mul_mono Matrix.PosSemidef.one hQ1
    simpa only [Matrix.one_mul,realTrace,Matrix.trace_one,RCLike.natCast_re,Fintype.card_fin] using hh
  have hn : ‖increment W s‖ ≤ Real.sqrt (N : ℝ) := by
    rw [←Real.sqrt_sq (norm_nonneg (increment W s)),increment_norm_sq W s]
    rw [covMatrix_trace] at htr
    exact Real.sqrt_le_sqrt htr
  have hs : (∑i,‖A i‖) ≤ (N : ℝ)*L := by
    calc _ ≤ ∑i : Fin N,L := Finset.sum_le_sum (fun i _ => hAnorm i)
      _ = _ := by simp
  calc
    _ ≤ ‖increment W s‖*(∑i,‖A i‖) := ownerPhysicalIncrement_norm_le A hA (increment W s)
    _ ≤ Real.sqrt (N : ℝ)*((N : ℝ)*L) := mul_le_mul hn hs
      (Finset.sum_nonneg (fun i _ => norm_nonneg (A i))) (Real.sqrt_nonneg _)
    _ = _ := by unfold directionCap; ring

theorem half_hessian_expectation (A : Fin N → Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : Matrix (Fin N) (Fin N) ℝ) (θ : ℝ) (H : selfAdjoint (Matrix n n ℂ))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (hQ : (covMatrix W).PosSemidef) (hq : 0<realTrace (covMatrix W)) :
    (∑s,weight W s*((1/2:ℝ)*ownerCenterHessian A C θ H (physical A hA W s) (physical A hA W s)))=
      realTrace (covMatrix W*ownerCoefficientResponse A hA C θ H) := by
  simpa only [ownerCoefficientResponse_quadratic,physical,ownerPhysicalIncrement] using
    quadratic_expectation W hQ hq (ownerCoefficientResponse A hA C θ H)

end SimpleMS.UniformMoments
