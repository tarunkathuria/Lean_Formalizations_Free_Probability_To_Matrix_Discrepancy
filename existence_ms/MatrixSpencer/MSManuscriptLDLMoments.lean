import MatrixSpencer.MSManuscriptNumericalSamplerData
import MatrixSpencer.FiniteOwnerDrift

/-! Exact pairing, quadratic moments, and physical norms for the finite LDL data. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptLDLMoments
open MSManuscriptNumericalSamplerData
variable {N : ℕ}

def flip (Q : Matrix (Fin N) (Fin N) ℝ) : Draws Q ≃ Draws Q where
  toFun s := (s.1,!s.2)
  invFun s := (s.1,!s.2)
  left_inv s := by simp
  right_inv s := by simp

theorem weight_flip (Q : Matrix (Fin N) (Fin N) ℝ) (s : Draws Q) : weight Q (flip Q s)=weight Q s := rfl

theorem increment_flip (Q : Matrix (Fin N) (Fin N) ℝ) (s : Draws Q) :
    increment Q (flip Q s) = -increment Q s := by
  rcases s with ⟨i,b⟩
  cases b <;> simp [increment,flip,selectedLabel]

theorem pair_average_eq (Q : Matrix (Fin N) (Fin N) ℝ) (f : Draws Q → ℝ) :
    (∑s,weight Q s*f s) = ∑s,weight Q s*((f s+f (flip Q s))/2) := by
  have he := (flip Q).sum_comp (fun s => weight Q s*f s)
  simp only [weight_flip] at he
  have hp : (∑s,weight Q s*((f s+f (flip Q s))/2)) =
      ((∑s,weight Q s*f s)+(∑s,weight Q s*f (flip Q s)))/2 := by
    rw [←Finset.sum_add_distrib,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [hp,he]
  ring

theorem weighted_pair_le (Q : Matrix (Fin N) (Fin N) ℝ) (hQ : Q.PosSemidef)
    (hq : 0<realTrace Q) (f q : Draws Q → ℝ) {e : ℝ}
    (hpair : ∀s,(f s+f (flip Q s))/2 ≤ q s+e) :
    (∑s,weight Q s*f s) ≤ (∑s,weight Q s*q s)+e := by
  rw [pair_average_eq Q f]
  calc
    _ ≤ ∑s,weight Q s*(q s+e) := Finset.sum_le_sum (fun s _ =>
      mul_le_mul_of_nonneg_left (hpair s) (weight_pos Q hq s).le)
    _ = _ := by rw [Finset.sum_congr rfl (fun s _ => mul_add _ _ _),Finset.sum_add_distrib,
      ←Finset.sum_mul,weight_sum Q hQ hq,one_mul]

theorem quadratic_expectation (Q : Matrix (Fin N) (Fin N) ℝ) (hQ : Q.PosSemidef)
    (hq : 0<realTrace Q) (G : Matrix (Fin N) (Fin N) ℝ) :
    (∑s : Draws Q,weight Q s*(WithLp.ofLp (increment Q s)⬝ᵥ(G*ᵥWithLp.ofLp (increment Q s))))=
      realTrace (Q*G) := by
  conv_rhs => rw [←covariance Q hQ hq]
  rw [Matrix.sum_mul,realTrace_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Matrix.smul_mul,realTrace_smul,realTrace_rankOne_mul]

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

def physical (A : Fin N → Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian)
    (Q : Matrix (Fin N) (Fin N) ℝ) (s : Draws Q) := ownerPhysicalIncrement A hA (increment Q s)

theorem physical_flip (A : Fin N → Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian)
    (Q : Matrix (Fin N) (Fin N) ℝ) (s : Draws Q) : physical A hA Q (flip Q s) = -physical A hA Q s := by
  change ownerPhysicalIncrementLinear A hA (increment Q (flip Q s)) = -ownerPhysicalIncrementLinear A hA (increment Q s)
  rw [increment_flip,map_neg]

def directionCap (N : ℕ) (L : ℝ) : ℝ := Real.sqrt (N : ℝ)*(N : ℝ)*L

theorem directionCap_nonneg {L : ℝ} (hL : 0 ≤ L) : 0 ≤ directionCap N L := by unfold directionCap; positivity

theorem physical_norm_le (A : Fin N → Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian)
    {L : ℝ} (hL : 0≤L) (hAnorm : ∀i,‖A i‖≤L)
    (Q : Matrix (Fin N) (Fin N) ℝ) (hQ : Q.PosSemidef) (hQ1 : Q≤1) (s : Draws Q) :
    ‖(physical A hA Q s : Matrix n n ℂ)‖ ≤ directionCap N L := by
  have htr : realTrace Q ≤ (N : ℝ) := by
    have hh := realTrace_mul_mono Matrix.PosSemidef.one hQ1
    simpa only [Matrix.one_mul,realTrace,Matrix.trace_one,RCLike.natCast_re,Fintype.card_fin] using hh
  have hn : ‖increment Q s‖ ≤ Real.sqrt (N : ℝ) := by
    rw [←Real.sqrt_sq (norm_nonneg (increment Q s)),increment_norm_sq Q hQ s]
    exact Real.sqrt_le_sqrt htr
  have hs : (∑i,‖A i‖) ≤ (N : ℝ)*L := by
    calc _ ≤ ∑i : Fin N,L := Finset.sum_le_sum (fun i _ => hAnorm i)
      _ = _ := by simp
  calc
    _ ≤ ‖increment Q s‖*(∑i,‖A i‖) := ownerPhysicalIncrement_norm_le A hA (increment Q s)
    _ ≤ Real.sqrt (N : ℝ)*((N : ℝ)*L) := mul_le_mul hn hs
      (Finset.sum_nonneg (fun i _ => norm_nonneg (A i))) (Real.sqrt_nonneg _)
    _ = _ := by unfold directionCap; ring

theorem half_hessian_expectation (A : Fin N → Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : Matrix (Fin N) (Fin N) ℝ) (θ : ℝ) (H : selfAdjoint (Matrix n n ℂ))
    (Q : Matrix (Fin N) (Fin N) ℝ) (hQ : Q.PosSemidef) (hq : 0<realTrace Q) :
    (∑s,weight Q s*((1/2:ℝ)*ownerCenterHessian A C θ H (physical A hA Q s) (physical A hA Q s)))=
      realTrace (Q*ownerCoefficientResponse A hA C θ H) := by
  simpa only [ownerCoefficientResponse_quadratic,physical,ownerPhysicalIncrement] using
    quadratic_expectation Q hQ hq (ownerCoefficientResponse A hA C θ H)

end MatrixSpencer.MSManuscriptLDLMoments
