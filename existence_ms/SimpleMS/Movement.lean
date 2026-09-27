import SimpleMS.UniformSampler
import SimpleMS.LegalSpace
import MatrixSpencer.CovarianceTraceLedger

open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace SimpleMS.Movement
open MatrixSpencer
variable {N : ℕ}

def covariance (C : Matrix (Fin N) (Fin N) ℝ) (F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N)) :=
  flatCovariance C (legalSpace F x)
abbrev Space (C : Matrix (Fin N) (Fin N) ℝ) (F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N)) :=
  movementSpace C (legalSpace F x)
abbrev Draws (C : Matrix (Fin N) (Fin N) ℝ) (F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N)) :=
  UniformSampler.Draws (Space C F x)
def weight (C : Matrix (Fin N) (Fin N) ℝ) (F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N)) :=
  UniformSampler.weight (Space C F x)
def increment (C : Matrix (Fin N) (Fin N) ℝ) (F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N)) :=
  UniformSampler.increment (Space C F x)
def nextPoint (C : Matrix (Fin N) (Fin N) ℝ) (F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N))
    (h : ℝ) (s : Draws C F x) := x+h • increment C F x s
def nextOwner (C : Matrix (Fin N) (Fin N) ℝ) (F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N)) (h : ℝ) :=
  C-h^2 • covariance C F x

lemma covariance_posSemidef (C : Matrix (Fin N) (Fin N) ℝ) (F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N)) :
    (covariance C F x).PosSemidef := flatCovariance_posSemidef C _
lemma covariance_le (C : Matrix (Fin N) (Fin N) ℝ) (hC : C.PosSemidef)
    (F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N)) : covariance C F x≤C := flatCovariance_le hC _
lemma rank_positive (C : Matrix (Fin N) (Fin N) ℝ) (F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N))
    (hq : 0<realTrace (covariance C F x)) : 0 < Module.finrank ℝ (Space C F x) := by
  rw [covariance,flatCovariance_trace] at hq
  have hh : (0:ℝ) < Module.finrank ℝ (Space C F x) := by linarith
  exact_mod_cast hh

def sample (C : Matrix (Fin N) (Fin N) ℝ) (F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N))
    (hq : 0<realTrace (covariance C F x)) : MSManuscriptAdaptive.Sampler (EuclideanSpace ℝ (Fin N)) :=
  UniformSampler.sample (Space C F x) (rank_positive C F x hq)

lemma weight_positive (C : Matrix (Fin N) (Fin N) ℝ) (F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N))
    (hq : 0<realTrace (covariance C F x)) (s : Draws C F x) : 0<weight C F x s :=
  UniformSampler.weight_positive _ (rank_positive C F x hq) s
lemma weights_sum (C : Matrix (Fin N) (Fin N) ℝ) (F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N))
    (hq : 0<realTrace (covariance C F x)) : (∑ s : Draws C F x,weight C F x s)=1 :=
  UniformSampler.weights_sum _ (rank_positive C F x hq)
lemma mean_zero (C : Matrix (Fin N) (Fin N) ℝ) (F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N)) :
    (∑s : Draws C F x,weight C F x s • increment C F x s)=0 := UniformSampler.mean_zero _
lemma covariance_exact (C : Matrix (Fin N) (Fin N) ℝ) (F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N))
    (hq : 0<realTrace (covariance C F x)) :
    (∑s : Draws C F x,weight C F x s • realRankOne (WithLp.ofLp (increment C F x s)))=covariance C F x :=
  UniformSampler.covariance _ (rank_positive C F x hq)
lemma increment_constraints (C : Matrix (Fin N) (Fin N) ℝ) (F : Finset (Fin N))
    (x : EuclideanSpace ℝ (Fin N)) (s : Draws C F x) :
    (∀i∈F,increment C F x s i=0) ∧ inner ℝ x (increment C F x s)=0 := by
  have hm := UniformSampler.increment_mem (Space C F x) s
  exact (mem_legalSpace F x _).mp ((show Space C F x ≤ legalSpace F x from inf_le_right) hm)
lemma increment_norm_sq (C : Matrix (Fin N) (Fin N) ℝ) (F : Finset (Fin N))
    (x : EuclideanSpace ℝ (Fin N)) (s : Draws C F x) :
    ‖increment C F x s‖^2=realTrace (covariance C F x) := by
  rw [covariance,flatCovariance_trace]
  exact UniformSampler.increment_norm_sq _ s
lemma norm_gain (C : Matrix (Fin N) (Fin N) ℝ) (F : Finset (Fin N))
    (x : EuclideanSpace ℝ (Fin N)) (h : ℝ) (s : Draws C F x) :
    ‖nextPoint C F x h s‖^2=‖x‖^2+h^2*realTrace (covariance C F x) := by
  rw [nextPoint,norm_add_sq_real,real_inner_smul_right,(increment_constraints C F x s).2,
    mul_zero,mul_zero,add_zero,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,increment_norm_sq]
lemma frozen_preserved (C : Matrix (Fin N) (Fin N) ℝ) (F : Finset (Fin N))
    (x : EuclideanSpace ℝ (Fin N)) (h : ℝ) (s : Draws C F x) (i : Fin N) (hi : i∈F) :
    nextPoint C F x h s i=x i := by
  change x i+h*increment C F x s i=x i
  rw [(increment_constraints C F x s).1 i hi,mul_zero,add_zero]
lemma nextOwner_valid (C : Matrix (Fin N) (Fin N) ℝ) (hC : C.PosSemidef) (F : Finset (Fin N))
    (x : EuclideanSpace ℝ (Fin N)) {h : ℝ} (hh : h^2<1) :
    (nextOwner C F x h).PosSemidef ∧ nextOwner C F x h≤C ∧
      LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) (nextOwner C F x h)).toLinearMap=
        LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) C).toLinearMap :=
  covarianceMovement_posSemidef_range hC (covariance_posSemidef C F x) (covariance_le C hC F x) hh
lemma nextOwner_trace (C : Matrix (Fin N) (Fin N) ℝ) (F : Finset (Fin N))
    (x : EuclideanSpace ℝ (Fin N)) (h : ℝ) :
    realTrace (nextOwner C F x h)=realTrace C-h^2*realTrace (covariance C F x) := by simp [nextOwner]
lemma nextOwner_matched (C : Matrix (Fin N) (Fin N) ℝ) (F : Finset (Fin N))
    (x : EuclideanSpace ℝ (Fin N)) (hq : 0<realTrace (covariance C F x)) (h : ℝ) :
    nextOwner C F x h=C-h^2 • (∑s : Draws C F x,weight C F x s • realRankOne (WithLp.ofLp (increment C F x s))) := by
  rw [covariance_exact C F x hq]
  rfl
lemma nextPoint_mem_cube (C : Matrix (Fin N) (Fin N) ℝ) (F : Finset (Fin N))
    (x : EuclideanSpace ℝ (Fin N)) (hx : ∀i,|x i|≤1) {ρ h : ℝ}
    (hmargin : ∀i,i∉F→|x i|≤1-ρ) (hstep : |h| *Real.sqrt (realTrace (covariance C F x))≤ρ)
    (s : Draws C F x) : ∀i,|nextPoint C F x h s i|≤1 := by
  intro i
  by_cases hi : i∈F
  · rw [frozen_preserved C F x h s i hi]
    exact hx i
  have hn : ‖increment C F x s‖=Real.sqrt (realTrace (covariance C F x)) := by
    rw [←increment_norm_sq C F x s,Real.sqrt_sq (norm_nonneg _)]
  have hc : |increment C F x s i|≤Real.sqrt (realTrace (covariance C F x)) := by
    simpa only [Real.norm_eq_abs,hn] using PiLp.norm_apply_le (increment C F x s) i
  have hs := mul_le_mul_of_nonneg_left hc (abs_nonneg h)
  have ht := abs_add_le (x i) (h*increment C F x s i)
  rw [abs_mul] at ht
  change |x i+h*increment C F x s i|≤1
  linarith [hmargin i hi]

end SimpleMS.Movement
