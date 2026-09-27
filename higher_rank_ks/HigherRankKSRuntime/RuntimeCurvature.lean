import AugmentedHigherRankKS.ActualPreparation
import AugmentedHigherRankKS.FourBlockLocalCurvature
import AugmentedHigherRankKS.RuntimeQueryFloors
import HigherRankKSRuntime.ValueDecisions
import MatrixSpencer.KSNumericalHessian

/-! Rejected actual preparation probes imply a negative tangent Rayleigh value
for the actual optimized potential. No favorable Hessian direction is supplied. -/
noncomputable section
open Matrix MatrixSpencer Set
open scoped BigOperators Topology ContDiff MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace HigherRankKSRuntime.RuntimeCurvature
open AugmentedHigherRankKS
variable {m : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local instance runtimeCurvatureCStar {j : Type*} [Fintype j] [DecidableEq j] :
  CStarAlgebra (Matrix j j ℂ) := {}
abbrev Space (m : ℕ) := EuclideanSpace ℝ (Fin m)

def chart (H : Matrix (FourSpin n) (FourSpin n) ℂ) (A : Fin m → Matrix n n ℂ)
    (β θ a : ℝ) (x c : Fin m → ℝ) (u : Space m) : ℝ :=
  potential (H+Frames.coefficientForce A x u) A β (fun i => c i-a*(u i)^2) θ

def prepCurve (H : Matrix (FourSpin n) (FourSpin n) ℂ) (A : Fin m → Matrix n n ℂ)
    (β θ a : ℝ) (c : Fin m → ℝ) (i : Fin m) (t : ℝ) : ℝ :=
  potential (H+t • ((1/a) • augmentedCenter 0 (A i))) A β (fun j => c j-if j=i then t else 0) θ

theorem chart_smooth (H : Matrix (FourSpin n) (FourSpin n) ℂ)
    (A : Fin m → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) {θ : ℝ} (hθ : 0 < θ) (a : ℝ)
    (x c : Fin m → ℝ) (hc : ∀ i, 0 < c i) :
    ContDiffAt ℝ ∞ (chart H A ((1:ℝ)/2^k) θ a x c) 0 := by
  apply contDiffAt_potential_of_positive_weights A hA k hk θ hθ
    (fun u : Space m => H+Frames.coefficientForce A x u)
    (fun u : Space m => fun i => c i-a*(u i)^2) 0
  · unfold Frames.coefficientForce
    fun_prop
  · apply contDiffAt_pi.mpr
    intro i
    fun_prop
  · simpa using hc

theorem chart_line (H : Matrix (FourSpin n) (FourSpin n) ℂ)
    (A : Fin m → Matrix n n ℂ) (β θ a : ℝ) (x c h : Fin m → ℝ) (t : ℝ) :
    chart H A β θ a x c (t • (WithLp.toLp 2 h : Space m)) =
      potential (H+t • Frames.coefficientForce A x h) A β
        (QuadraticReserveCurve.curve c a h t) θ := by
  unfold chart Frames.coefficientForce QuadraticReserveCurve.curve
  have hh : (∑ i, (t • (WithLp.toLp 2 h : Space m)) i • forceAtom (x i) (A i)) =
      t • ∑ i, h i • forceAtom (x i) (A i) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul]
    rfl
  rw [hh]
  congr 1
  funext i
  change c i-a*(t*h i)^2 = c i-a*t^2*(h i)^2
  ring

/-- The scalar cap uses the actual envelope derivative and actual matrix probes. -/
theorem rejected_preparation_cap (H : Matrix (FourSpin n) (FourSpin n) ℂ)
    (A : Fin m → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) {θ a p₀ : ℝ} (hθ : 0 < θ) (ha : 0 < a) (hp₀ : 0 < p₀)
    (c : Fin m → ℝ) (hc : ∀ i, 0 < c i) (hccap : ∀ i, c i ≤ 4*a)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef)
    (ht : realTrace (S : Matrix (FourSpin n) (FourSpin n) ℂ) = 1)
    (hmax : ∀ T ∈ densitySet, objective H A ((1:ℝ)/2^k) c θ T ≤ objective H A ((1:ℝ)/2^k) c θ S)
    (hp : ∀ i, p₀ ≤ HigherRankKS.BalancedFrames.carrierMass (SupportedSpin.probe A) (SupportedSpin.density A S) i)
    (hreject : ∀ i, -(p₀/(2*a)) < deriv (prepCurve H A ((1:ℝ)/2^k) θ a c i) 0) :
    ∀ i, Frames.r A ((1:ℝ)/2^k) c S i ^ 2 ≤ 9/a := by
  intro i
  let p := HigherRankKS.BalancedFrames.carrierMass (SupportedSpin.probe A) (SupportedSpin.density A S) i
  let τ := HigherRankKS.BalancedFrames.transportMass (SupportedSpin.term A ((1:ℝ)/2^k) S)
    (SupportedSpin.transport A ((1:ℝ)/2^k) c S) i
  have hp' : 0 < p := hp₀.trans_le (hp i)
  have htau : 0 ≤ τ := realTrace_mul_nonneg
    (SupportedSpin.transport_posDef A hA hc hS k hk).posSemidef
    (SupportedSpin.term_posSemidef A ((1:ℝ)/2^k) hS.posSemidef i)
  have hd := preparation_potential_deriv A hA k hk θ hθ H c hc a i S ⟨hS.posSemidef,ht⟩ hmax
  have hb := budgetProbe_trace_le (hA i) hS.posSemidef
  have hsource : deriv (prepCurve H A ((1:ℝ)/2^k) θ a c i) 0 ≤ p/a-τ := by
    change deriv (fun t => potential (H+t • ((1/a) • augmentedCenter 0 (A i)))
      A ((1:ℝ)/2^k) (fun j => c j-if j=i then t else 0) θ) 0 ≤ p/a-τ
    rw [hd]
    apply sub_le_sub_right
    apply div_le_div_of_nonneg_right _ ha.le
    change _ ≤ HigherRankKS.BalancedFrames.carrierMass (SupportedSpin.probe A) (SupportedSpin.density A S) i
    rw [HigherRankKS.BalancedFrames.carrierMass,SupportedSpin.probe_pairing A hA]
    exact hb
  have hq := preparation_probe_cap ha hp' (hp i) hsource (hreject i)
  have he : Frames.r A ((1:ℝ)/2^k) c S i^2 = c i*(τ/p)^2 := by
    unfold Frames.r HigherRankKS.BalancedFrames.probeScale
    change (Real.sqrt (c i)*τ/p)^2 = c i*(τ/p)^2
    rw [div_pow,mul_pow,Real.sq_sqrt (hc i).le]
    ring
  rw [he]
  have hq0 : 0 ≤ τ/p := div_nonneg htau hp'.le
  have hqu := (sq_le_sq₀ hq0 (by positivity : 0 ≤ 3/(2*a))).mpr hq.le
  calc c i*(τ/p)^2 ≤ (4*a)*(3/(2*a))^2 :=
         mul_le_mul (hccap i) hqu (sq_nonneg _) (by positivity)
       _ = 9/a := by field_simp <;> ring

/-- Normalizing a genuine negative direction preserves a quantitative gap and tangency. -/
theorem unit_witness_of_gap (f : Space m → ℝ) (x w : Space m) (hf : ContDiffAt ℝ 2 f 0)
    (hw : w ≠ 0) (horth : inner ℝ x w = 0) {gap : ℝ}
    (hcurv : iteratedDeriv 2 (fun t : ℝ => f (t • w)) 0 < -gap*‖w‖^2) :
    ∃ g : Space m, ‖g‖ = 1 ∧ inner ℝ x g = 0 ∧
      KSRayleighAccuracy.realRayleigh (KSNumericalHessian.hessian f 0) g < -gap := by
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hi : 0 < ‖w‖⁻¹ := inv_pos.mpr hn
  let g : Space m := ‖w‖⁻¹ • w
  have hg : ‖g‖ = 1 := by
    rw [show g=‖w‖⁻¹ • w from rfl,norm_smul,Real.norm_eq_abs,abs_of_pos hi,inv_mul_cancel₀ hn.ne']
  refine ⟨g,hg,?_,?_⟩
  · simp only [g,inner_smul_right,horth,mul_zero]
  · have hline := KSFourthDifference.line_second f 0 w hf
    simp only [zero_add] at hline
    rw [hline] at hcurv
    rw [KSNumericalHessian.hessian_rayleigh]
    change fderiv ℝ (fderiv ℝ f) 0 (‖w‖⁻¹ • w) (‖w‖⁻¹ • w) < -gap
    simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
    have hh := mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hcurv hi) hi
    have he : ‖w‖⁻¹*(‖w‖⁻¹*(-gap*‖w‖^2)) = -gap := by field_simp <;> ring
    exact hh.trans_eq he
/-- Preparation rejection, proved probe floors and the matrix response theorem
produce a unit tangent witness for the exact Hessian matrix. -/
theorem exists_unit_negative_hessian (hm : 0 < m)
    (H : Matrix (FourSpin n) (FourSpin n) ℂ) (A : Fin m → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hne : ∀ i, A i ≠ 0)
    (k : ℕ) (hk : 1 ≤ k) {θ a p₀ τ₀ : ℝ} (hθ : 0 < θ) (ha : 0 < a)
    (hp₀ : 0 < p₀) (haresponse : 120/((1:ℝ)/2^k) ≤ a) (hacap : 9/a ≤ 1/48)
    (x : Space m) (hx : ∀ i, |x i| ≤ 1)
    (c : Fin m → ℝ) (hc : ∀ i, 0 < c i) (hccap : ∀ i, c i ≤ 4*a)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef)
    (ht : realTrace (S : Matrix (FourSpin n) (FourSpin n) ℂ) = 1)
    (hmax : ∀ T ∈ densitySet, objective H A ((1:ℝ)/2^k) c θ T ≤ objective H A ((1:ℝ)/2^k) c θ S)
    (hp : ∀ i, p₀ ≤ HigherRankKS.BalancedFrames.carrierMass (SupportedSpin.probe A) (SupportedSpin.density A S) i)
    (htau : ∀ i, τ₀ ≤ HigherRankKS.BalancedFrames.transportMass (SupportedSpin.term A ((1:ℝ)/2^k) S)
      (SupportedSpin.transport A ((1:ℝ)/2^k) c S) i)
    (hreject : ∀ i, -(p₀/(2*a)) < deriv (prepCurve H A ((1:ℝ)/2^k) θ a c i) 0) :
    ∃ g : Space m, ‖g‖=1 ∧ inner ℝ x g=0 ∧
      KSRayleighAccuracy.realRayleigh (KSNumericalHessian.hessian (chart H A ((1:ℝ)/2^k) θ a x c) 0) g < -a*τ₀ := by
  letI : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  have hcap := rejected_preparation_cap H A hA k hk hθ ha hp₀ c hc hccap S hS ht hmax hp hreject
  obtain ⟨h,hh,horth,hcurv⟩ := Frames.exists_negative_curvature A hA hne k hk c hc x x hx
    H θ hθ S hS ht hmax (fun i => (hcap i).trans hacap) haresponse
  let w : Space m := WithLp.toLp 2 h
  have hw : w ≠ 0 := by
    intro he
    apply hh
    funext i
    exact congrArg (fun v : Space m => v i) he
  have hworth : inner ℝ x w = 0 := by
    change (∑ i, h i*x i)=0
    simpa only [mul_comm] using horth
  have hnorm : ‖w‖^2 = ∑ i, (h i)^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs,sq_abs]
    rfl
  have hdebit : τ₀*‖w‖^2 ≤ Frames.debit A ((1:ℝ)/2^k) c S h := by
    rw [hnorm,Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (htau i) (sq_nonneg _)
  have hline : (fun t : ℝ => chart H A ((1:ℝ)/2^k) θ a x c (t • w)) =
      (fun t : ℝ => potential (H+t • Frames.coefficientForce A x h) A ((1:ℝ)/2^k)
        (QuadraticReserveCurve.curve c a h t) θ) :=
    funext (chart_line H A ((1:ℝ)/2^k) θ a x c h)
  have hg := unit_witness_of_gap (chart H A ((1:ℝ)/2^k) θ a x c) x w
    ((chart_smooth H A hA k hk hθ a x c hc).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))) hw hworth (gap := a*τ₀) (by
      rw [hline]
      have hbound := mul_le_mul_of_nonpos_left hdebit (neg_nonpos.mpr ha.le)
      exact hcurv.trans_le (by nlinarith [hbound]))
  simpa only [neg_mul] using hg

open RuntimeParameters in
/-- In the actual runtime parameter regime, the optimizer and all its probe
floors are obtained from the input. Only the observed rejected-preparation
branch remains as a condition for this local algorithmic alternative. -/
theorem runtime_negative_tangent_witness (hm : 0 < m)
    (z : RuntimeParameters.Dimensions) (hz : z ∈ RuntimeParameters.Domain)
    (hd : (Fintype.card n : ℝ) ≤ z.D)
    (H : Matrix (FourSpin n) (FourSpin n) ℂ) (hH : H.IsHermitian) (hH8 : ‖H‖ ≤ 8)
    (A : Fin m → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r : ℕ} (hr : ∀ i, (A i).rank ≤ r) (k : ℕ) (hk : 1 ≤ k) (hq : z.q=2^k)
    (hrβ : (r:ℝ)^((1:ℝ)/2^k) ≤ 2)
    (x : Space m) (hx : ∀ i, |x i| ≤ 1)
    (c : Fin m → ℝ) (hc : ∀ i, 0 < c i) (hccap : ∀ i, c i ≤ 4*a z)
    (hlarge : ∀ i, eta z ≤ ‖A i‖)
    (hreject : ∀ i, -(p0 z/(2*a z)) < deriv (prepCurve H A ((1:ℝ)/2^k) (theta z) (a z) c i) 0) :
    ∃ g : Space m, ‖g‖=1 ∧ inner ℝ x g=0 ∧
      KSRayleighAccuracy.realRayleigh (KSNumericalHessian.hessian
        (chart H A ((1:ℝ)/2^k) (theta z) (a z) x c) 0) g ≤ -4*gamma z := by
  have ha := a_poly.positive z hz
  have hc8 : ∀ i, c i ≤ 8*a z := fun i => (hccap i).trans (by linarith)
  obtain ⟨S,hS,ht,hmax,_,_⟩ := exists_runtime_query_optimizer z hz hd H hH hH8 A hA hsum
    hε hε1 hN hr k hk hrβ c hc hc8
  have hprobe := fun i => runtime_query_probe_floors z hz hd H hH hH8 A hA hsum hε hε1 hN hr
    k hk hrβ c hc hc8 S hS ht hmax i (hlarge i)
  have hne : ∀ i, A i ≠ 0 := by
    intro i hi
    have hh := hlarge i
    rw [hi,norm_zero] at hh
    exact (not_le_of_gt (theta_poly.positive z hz)) hh
  have har : 120/((1:ℝ)/2^k) ≤ a z := by
    dsimp only [a]
    rw [hq]
    have hp : 0 < (2:ℝ)^k := by positivity
    field_simp
    nlinarith
  obtain ⟨g,hg,ho,hcurv⟩ := exists_unit_negative_hessian hm H A hA hne k hk
    (theta_poly.positive z hz) ha (p0_poly.positive z hz) har (cap_slack z hz).le x hx c hc hccap
    S hS ht hmax (fun i => (hprobe i).1) (fun i => (hprobe i).2) hreject
  refine ⟨g,hg,ho,hcurv.le.trans_eq ?_⟩
  unfold gamma
  ring

end HigherRankKSRuntime.RuntimeCurvature
