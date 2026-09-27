import AugmentedHigherRankKS.FourBlockJointRegularity
import AugmentedHigherRankKS.RuntimeRegularity.QuadraticCoefficients

/-! Joint and envelope derivative bounds for the actual reserve query curves. -/
open Matrix MatrixSpencer HigherRankKS Filter
open scoped BigOperators Topology ContDiff MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 300000
namespace AugmentedHigherRankKS
open BalancedTransportJets BalancedRegularity
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance queryRegCStar {m : Type*} [Fintype m] [DecidableEq m] :
    CStarAlgebra (Matrix m m ℂ) := {}
local instance : NormedAddCommGroup (densityTangent (n := FourSpin n)) := inferInstance
local instance : NormedSpace ℝ (densityTangent (n := FourSpin n)) := inferInstance
local instance : NormedAddCommGroup (ℝ × densityTangent (n := FourSpin n)) := inferInstance
local instance : NormedSpace ℝ (ℝ × densityTangent (n := FourSpin n)) := inferInstance
local instance : NormedAddCommGroup ((ℝ × densityTangent (n := FourSpin n)) →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ ((ℝ × densityTangent (n := FourSpin n)) →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup ((ℝ × densityTangent (n := FourSpin n)) →L[ℝ]
    (ℝ × densityTangent (n := FourSpin n)) →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ ((ℝ × densityTangent (n := FourSpin n)) →L[ℝ]
    (ℝ × densityTangent (n := FourSpin n)) →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup ((ℝ × densityTangent (n := FourSpin n)) →L[ℝ]
    (ℝ × densityTangent (n := FourSpin n)) →L[ℝ]
    (ℝ × densityTangent (n := FourSpin n)) →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ ((ℝ × densityTangent (n := FourSpin n)) →L[ℝ]
    (ℝ × densityTangent (n := FourSpin n)) →L[ℝ]
    (ℝ × densityTangent (n := FourSpin n)) →L[ℝ] ℝ) := inferInstance

def jointAmplitude (d C θ : ℝ) : ℝ := 1+20*d+2*C+θ*d
def jointScale (d Lc s : ℝ) : ℝ := 100*d*(Lc+2/s+1)

theorem contDiffAt_chartObjective_data
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (θ : ℝ)
    (H : ℝ → Matrix (FourSpin n) (FourSpin n) ℂ) (c : ℝ → ι → ℝ)
    (hH : ContDiffAt ℝ ∞ H 0) (hc : ContDiffAt ℝ ∞ c 0)
    (hc0 : ∀ i, 0 < c 0 i)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    ContDiffAt ℝ ∞ (chartObjective H A ((1:ℝ)/2^k) c θ S) (0,0) := by
  have hchart : ContDiff ℝ ∞ (densityChart S) :=
    contDiff_const.add (densityTangent (n := FourSpin n)).subtypeL.contDiff
  have hmap : ContDiffAt ℝ ∞
      (fun P : ℝ × densityTangent (n := FourSpin n) => (P.1,densityChart S P.2)) (0,0) :=
    contDiffAt_fst.prodMk (hchart.contDiffAt.comp (0,0) (f := Prod.snd) contDiffAt_snd)
  have ho := contDiffAt_objective_of_data A hA k hk θ H c 0 hH hc hc0 S hS
  have ho' : ContDiffAt ℝ ∞
      (fun P : ℝ × selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ) =>
        hermitianObjective (H P.1) A ((1:ℝ)/2^k) (c P.1) θ P.2) (0,densityChart S 0) := by
    simpa only [densityChart_zero] using ho
  exact ho'.comp (0,0) hmap

/-- Actual joint derivative norms, with scalar reserve jets as the sole local
input estimate. Both concrete query families discharge these jets below. -/
theorem chartObjective_joint_norms
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (H K : Matrix (FourSpin n) (FourSpin n) ℂ)
    (c : ℝ → ι → ℝ) (hc : ContDiffAt ℝ ∞ c 0) (hc0 : ∀ i, 0 < c 0 i)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef)
    (ht : realTrace (S : Matrix (FourSpin n) (FourSpin n) ℂ) = 1)
    {θ s Lc d C0 : ℝ} (hθ : 0 ≤ θ) (hs : 0 < s) (hLc : 0 ≤ Lc)
    (hd : 1 ≤ d) (hdn : Real.sqrt (Fintype.card (FourSpin n) : ℝ) ≤ d)
    (hC0 : 0 ≤ C0) (hK : ‖K‖ ≤ 2)
    (hfloor : s • (1 : Matrix (FourSpin n) (FourSpin n) ℂ) ≤ S)
    (hbudget : fidelity (S : Matrix (FourSpin n) (FourSpin n) ℂ)
      (source A ((1:ℝ)/2^k) (c 0) S) ≤ C0)
    (hcoeff : ∀ ξ i j, j ≤ 3 →
      ‖iteratedDeriv j (fun t : ℝ => c (t*ξ) i) 0‖ ≤
        (j.factorial : ℝ)*(Lc*|ξ|)^j*c 0 i) :
    KSActualEnvelope.secondNorm (chartObjective (fun t => H+t•K) A ((1:ℝ)/2^k) c θ S) (0,0) ≤
      4*jointAmplitude d C0 θ*(jointScale d Lc s)^2 ∧
    KSActualEnvelope.thirdNorm (chartObjective (fun t => H+t•K) A ((1:ℝ)/2^k) c θ S) (0,0) ≤
      27*jointAmplitude d C0 θ*(jointScale d Lc s)^3 := by
  let F := chartObjective (fun t => H+t•K) A ((1:ℝ)/2^k) c θ S
  let L := Lc+2/s+1
  have hL : 1 ≤ L := by
    have hh : 0 ≤ 2/s := by positivity
    dsimp [L]
    linarith
  have hLc0 : 0 ≤ L := by linarith
  have hd0 : 0 ≤ d := by linarith
  have hAmp : 0 ≤ jointAmplitude d C0 θ := by unfold jointAmplitude; positivity
  have hScale : 0 ≤ jointScale d Lc s := by unfold jointScale; positivity
  have hF : ContDiffAt ℝ ∞ F (0,0) := contDiffAt_chartObjective_data A hA k hk θ
    (fun t => H+t•K) c (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)) hc hc0 S hS
  have hline (j : ℕ) (hj2 : 2 ≤ j) (hj3 : j ≤ 3)
      (v : ℝ × densityTangent (n := FourSpin n)) :
      |iteratedDeriv j (fun t : ℝ => F ((0,0)+t•v)) 0| ≤
        (j.factorial : ℝ)*jointAmplitude d C0 θ*(jointScale d Lc s)^j*‖v‖^j := by
    let X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ) := v.2
    let cv := fun t : ℝ => c (t*v.1)
    have hξ : |v.1| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le v
    have hX : ‖(X : Matrix (FourSpin n) (FourSpin n) ℂ)‖ ≤ ‖v‖ := norm_snd_le v
    have hr : 0 ≤ ‖v‖ := norm_nonneg v
    have hb : 0 ≤ ‖v‖/s := div_nonneg hr hs.le
    have hdc : 0 ≤ Lc*‖v‖ := mul_nonneg hLc hr
    have hrel := density_relative_order X.property hs hr hfloor hX
    have hcv : ContDiffAt ℝ 3 cv 0 := by
      have hc3 := hc.of_le (WithTop.coe_le_coe.mpr (show (3:ℕ∞) ≤ ⊤ from le_top))
      have hc3' : ContDiffAt ℝ 3 c ((0:ℝ)*v.1) := by simpa only [zero_mul] using hc3
      exact hc3'.comp 0 (contDiffAt_id.mul contDiffAt_const)
    have hcv0 : ∀ i, 0 < cv 0 i := by simpa only [cv,zero_mul] using hc0
    have hcoef : ∀ i l, l ≤ 3 →
        ‖iteratedDeriv l (fun t => cv t i) 0‖ ≤
          (l.factorial : ℝ)*(Lc*‖v‖)^l*cv 0 i := by
      intro i l hl
      apply (hcoeff v.1 i l hl).trans
      simp only [cv,zero_mul]
      gcongr
      exact (hc0 i).le
    have hKv : ‖v.1 • K‖ ≤ 2*‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      nlinarith [mul_le_mul hξ hK (norm_nonneg K) hr]
    have hls : Lc*‖v‖+2*(‖v‖/s) ≤ L*‖v‖ := by
      calc
        _ ≤ (Lc*‖v‖+2*(‖v‖/s))+‖v‖ := le_add_of_nonneg_right hr
        _ = _ := by dsimp [L]; ring
    have hbgt : fidelity (S : Matrix (FourSpin n) (FourSpin n) ℂ)
        (source A ((1:ℝ)/2^k) (cv 0) S) ≤ C0 := by simpa only [cv,zero_mul] using hbudget
    have hj := objective_scalarJet_le A hA k hk H (v.1•K) S X hS ht cv hcv hcv0
      hθ hb hdc hd hdn hL hr hC0 hbgt hrel.1 hrel.2 hKv hX hls hcoef j hj2 hj3
    have he : (fun t : ℝ => F ((0,0)+t•v)) =
        (fun t : ℝ => objective (H+t•(v.1•K)) A ((1:ℝ)/2^k) (cv t) θ (S+t•X)) := by
      funext t
      rw [show ((0,0) : ℝ × densityTangent (n := FourSpin n))+t•v = (t*v.1,t•v.2) by
        ext <;> simp]
      change objective (H+(t*v.1)•K) A ((1:ℝ)/2^k) (c (t*v.1)) θ
        ((S : Matrix (FourSpin n) (FourSpin n) ℂ)+t•(X : Matrix (FourSpin n) (FourSpin n) ℂ)) = _
      rw [smul_smul]
    rw [he]
    apply (scalarJet_bound_to_iteratedDeriv hj).trans
    have hp : 0 ≤ (100*d*L*‖v‖)^j := by positivity
    have ha : 1+2*C0+θ*d ≤ jointAmplitude d C0 θ := by unfold jointAmplitude; linarith
    calc
      _ ≤ (j.factorial : ℝ)*(jointAmplitude d C0 θ*(100*d*L*‖v‖)^j) := by
        gcongr
      _ = _ := by simp only [jointScale, L, mul_pow]; ring
  constructor
  · have hb := JointPolarization.second_derivative_norm F (0,0)
      (hF.of_le (WithTop.coe_le_coe.mpr (show (2:ℕ∞) ≤ ⊤ from le_top)))
      (C := 2*jointAmplitude d C0 θ*(jointScale d Lc s)^2) (by positivity)
      (fun v => by simpa [Nat.factorial] using hline 2 (by omega) (by omega) v)
    change ‖fderiv ℝ (fderiv ℝ F) (0,0)‖ ≤ _
    nlinarith
  · have hb := JointPolarization.third_derivative_norm F (0,0)
      (hF.of_le (WithTop.coe_le_coe.mpr (show (3:ℕ∞) ≤ ⊤ from le_top)))
      (C := 6*jointAmplitude d C0 θ*(jointScale d Lc s)^3) (by positivity)
      (fun v => by simpa [Nat.factorial] using hline 3 (by omega) (by omega) v)
    change ‖fderiv ℝ (fderiv ℝ (fderiv ℝ F)) (0,0)‖ ≤ _
    nlinarith

/-- The reserve polynomial used by the actual curvature queries. -/
def quadraticReserve (c u g : ι → ℝ) (a : ℝ) (t : ℝ) (i : ι) : ℝ :=
  c i-a*(u i+t*g i)^2

theorem contDiff_quadraticReserve (c u g : ι → ℝ) (a : ℝ) :
    ContDiff ℝ ∞ (quadraticReserve c u g a) := by
  apply contDiff_pi.mpr
  intro i
  unfold quadraticReserve
  fun_prop

theorem quadraticReserve_scaled_jets (c u g : ι → ℝ) {a ζ : ℝ}
    (ha : 1 ≤ a) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hc : ∀ i, ζ ≤ c i-a*(u i)^2) (hu : ∀ i, |u i| ≤ 1) (hg : ∀ i, |g i| ≤ 1) :
    ∀ ξ i j, j ≤ 3 →
      ‖iteratedDeriv j (fun t : ℝ => quadraticReserve c u g a (t*ξ) i) 0‖ ≤
        (j.factorial : ℝ)*((4*a/ζ)*|ξ|)^j*quadraticReserve c u g a 0 i := by
  intro ξ i j hj
  have hh : |ξ*g i| ≤ |ξ| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hg i) (abs_nonneg ξ)).trans_eq (mul_one _)
  have h := HigherRankKSRuntime.QuadraticCoefficients.reserve_coefficient_bound
    ha hζ hζ1 (hc i) (hu i) hh j
  have he : (fun t : ℝ => quadraticReserve c u g a (t*ξ) i) =
      fun t => c i-a*(u i+t*(ξ*g i))^2 := by
    funext t
    unfold quadraticReserve
    ring
  rw [he]
  simpa only [quadraticReserve, zero_mul, add_zero] using h

/-- The actual quadratic reserve family satisfies the joint derivative bounds
without any source or derivative bound hypothesis. -/
theorem quadratic_query_joint_norms
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (H K : Matrix (FourSpin n) (FourSpin n) ℂ)
    (c u g : ι → ℝ) {a ζ : ℝ} (ha : 1 ≤ a) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hc : ∀ i, ζ ≤ c i-a*(u i)^2) (hu : ∀ i, |u i| ≤ 1) (hg : ∀ i, |g i| ≤ 1)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef)
    (ht : realTrace (S : Matrix (FourSpin n) (FourSpin n) ℂ) = 1)
    {θ s d C0 : ℝ} (hθ : 0 ≤ θ) (hs : 0 < s)
    (hd : 1 ≤ d) (hdn : Real.sqrt (Fintype.card (FourSpin n) : ℝ) ≤ d)
    (hC0 : 0 ≤ C0) (hK : ‖K‖ ≤ 2)
    (hfloor : s • (1 : Matrix (FourSpin n) (FourSpin n) ℂ) ≤ S)
    (hbudget : fidelity (S : Matrix (FourSpin n) (FourSpin n) ℂ)
      (source A ((1:ℝ)/2^k) (fun i => c i-a*(u i)^2) S) ≤ C0) :
    KSActualEnvelope.secondNorm (chartObjective (fun t => H+t•K) A ((1:ℝ)/2^k)
      (quadraticReserve c u g a) θ S) (0,0) ≤
      4*jointAmplitude d C0 θ*(jointScale d (4*a/ζ) s)^2 ∧
    KSActualEnvelope.thirdNorm (chartObjective (fun t => H+t•K) A ((1:ℝ)/2^k)
      (quadraticReserve c u g a) θ S) (0,0) ≤
      27*jointAmplitude d C0 θ*(jointScale d (4*a/ζ) s)^3 := by
  apply chartObjective_joint_norms A hA k hk H K (quadraticReserve c u g a)
    (contDiff_quadraticReserve c u g a).contDiffAt _ S hS ht hθ hs
    (by positivity) hd hdn hC0 hK hfloor _
    (quadraticReserve_scaled_jets c u g ha hζ hζ1 hc hu hg)
  · intro i
    simpa only [quadraticReserve,zero_mul,add_zero] using hζ.trans_le (hc i)
  · have he : quadraticReserve c u g a 0 = fun i => c i-a*(u i)^2 := by
      funext i
      simp only [quadraticReserve,zero_mul,add_zero]
    rw [he]
    exact hbudget

/-- The affine reserve family used by preparation. -/
def affineReserve (c w : ι → ℝ) (t : ℝ) (i : ι) : ℝ := c i+t*w i

theorem contDiff_affineReserve (c w : ι → ℝ) : ContDiff ℝ ∞ (affineReserve c w) := by
  apply contDiff_pi.mpr
  intro i
  unfold affineReserve
  fun_prop

theorem affineReserve_scaled_jets (c w : ι → ℝ) {a ζ : ℝ}
    (ha : 1 ≤ a) (hζ : 0 < ζ)
    (hc : ∀ i, ζ ≤ c i) (hw : ∀ i, |w i| ≤ 1) :
    ∀ ξ i j, j ≤ 3 →
      ‖iteratedDeriv j (fun t : ℝ => affineReserve c w (t*ξ) i) 0‖ ≤
        (j.factorial : ℝ)*((4*a/ζ)*|ξ|)^j*affineReserve c w 0 i := by
  intro ξ i j hj
  have hc0 : 0 ≤ c i := hζ.le.trans (hc i)
  have hLc : 0 ≤ 4*a/ζ := by positivity
  have hcap : 1 ≤ (4*a/ζ)*c i := by
    calc
      1 ≤ 4*a := by linarith
      _ = (4*a/ζ)*ζ := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hc i) hLc
  have hv : |ξ*w i| ≤ ((4*a/ζ)*|ξ|)*c i := by
    calc
      _ ≤ |ξ| := by
        rw [abs_mul]
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (hw i) (abs_nonneg ξ)
      _ ≤ |ξ| * ((4*a/ζ)*c i) := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hcap (abs_nonneg ξ)
      _ = _ := by ring
  have hh := HigherRankKSRuntime.QuadraticCoefficients.quadratic_coefficient_bound
    hc0 (show 0 ≤ (4*a/ζ)*|ξ| by positivity) hv
    (show |(0:ℝ)| ≤ ((4*a/ζ)*|ξ|)^2*c i by rw [abs_zero]; positivity) j
  have he : (fun t : ℝ => affineReserve c w (t*ξ) i) =
      HigherRankKSRuntime.QuadraticCoefficients.quadratic (c i) (ξ*w i) 0 := by
    funext t
    unfold affineReserve HigherRankKSRuntime.QuadraticCoefficients.quadratic
    ring
  rw [he]
  simpa only [affineReserve,zero_mul,add_zero] using hh

theorem affine_query_joint_norms
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (H K : Matrix (FourSpin n) (FourSpin n) ℂ)
    (c w : ι → ℝ) {a ζ : ℝ} (ha : 1 ≤ a) (hζ : 0 < ζ)
    (hc : ∀ i, ζ ≤ c i) (hw : ∀ i, |w i| ≤ 1)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef)
    (ht : realTrace (S : Matrix (FourSpin n) (FourSpin n) ℂ) = 1)
    {θ s d C0 : ℝ} (hθ : 0 ≤ θ) (hs : 0 < s)
    (hd : 1 ≤ d) (hdn : Real.sqrt (Fintype.card (FourSpin n) : ℝ) ≤ d)
    (hC0 : 0 ≤ C0) (hK : ‖K‖ ≤ 2)
    (hfloor : s • (1 : Matrix (FourSpin n) (FourSpin n) ℂ) ≤ S)
    (hbudget : fidelity (S : Matrix (FourSpin n) (FourSpin n) ℂ)
      (source A ((1:ℝ)/2^k) c S) ≤ C0) :
    KSActualEnvelope.secondNorm (chartObjective (fun t => H+t•K) A ((1:ℝ)/2^k)
      (affineReserve c w) θ S) (0,0) ≤
      4*jointAmplitude d C0 θ*(jointScale d (4*a/ζ) s)^2 ∧
    KSActualEnvelope.thirdNorm (chartObjective (fun t => H+t•K) A ((1:ℝ)/2^k)
      (affineReserve c w) θ S) (0,0) ≤
      27*jointAmplitude d C0 θ*(jointScale d (4*a/ζ) s)^3 := by
  apply chartObjective_joint_norms A hA k hk H K (affineReserve c w)
    (contDiff_affineReserve c w).contDiffAt _ S hS ht hθ hs
    (by positivity) hd hdn hC0 hK hfloor _
    (affineReserve_scaled_jets c w ha hζ hc hw)
  · intro i
    simpa only [affineReserve,zero_mul,add_zero] using hζ.trans_le (hc i)
  · have he : affineReserve c w 0 = c := by
      funext i
      simp only [affineReserve,zero_mul,add_zero]
    rw [he]
    exact hbudget

/-- The computed joint bounds instantiate the genuine optimizer envelope.
No upper derivative bound for the value function is assumed. -/
theorem query_potential_derivative_bounds
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (H K : Matrix (FourSpin n) (FourSpin n) ℂ)
    (c : ℝ → ι → ℝ) (hc : ContDiffAt ℝ ∞ c 0) (hc0 : ∀ i, 0 < c 0 i)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hSpos : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef)
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ) ∈ densitySet)
    {θ s Lc d C0 : ℝ} (hθ : 0 < θ) (hs : 0 < s) (hLc : 0 ≤ Lc)
    (hd : 1 ≤ d) (hdn : Real.sqrt (Fintype.card (FourSpin n) : ℝ) ≤ d)
    (hC0 : 0 ≤ C0) (hK : ‖K‖ ≤ 2)
    (hfloor : s • (1 : Matrix (FourSpin n) (FourSpin n) ℂ) ≤ S)
    (hbudget : fidelity (S : Matrix (FourSpin n) (FourSpin n) ℂ)
      (source A ((1:ℝ)/2^k) (c 0) S) ≤ C0)
    (hmax : ∀ T ∈ densitySet, objective H A ((1:ℝ)/2^k) (c 0) θ T ≤
      objective H A ((1:ℝ)/2^k) (c 0) θ S)
    (hcoeff : ∀ ξ i j, j ≤ 3 →
      ‖iteratedDeriv j (fun t : ℝ => c (t*ξ) i) 0‖ ≤
        (j.factorial : ℝ)*(Lc*|ξ|)^j*c 0 i) :
    let B2 := 4*jointAmplitude d C0 θ*(jointScale d Lc s)^2
    let B3 := 27*jointAmplitude d C0 θ*(jointScale d Lc s)^3
    let M := B3*(1+B2/(θ/2))^3
    |iteratedDeriv 2 (fun t => potential (H+t•K) A ((1:ℝ)/2^k) (c t) θ) 0| ≤ M ∧
    |iteratedDeriv 3 (fun t => potential (H+t•K) A ((1:ℝ)/2^k) (c t) θ) 0| ≤ M := by
  let B2 := 4*jointAmplitude d C0 θ*(jointScale d Lc s)^2
  let B3 := 27*jointAmplitude d C0 θ*(jointScale d Lc s)^3
  have hd0 : 0 ≤ d := by linarith
  have hAmp : 0 ≤ jointAmplitude d C0 θ := by unfold jointAmplitude; positivity
  have hL : 1 ≤ Lc+2/s+1 := by
    have hh : 0 ≤ 2/s := by positivity
    linarith
  have hScale : 1 ≤ jointScale d Lc s := by
    unfold jointScale
    nlinarith [mul_le_mul hd hL (by norm_num : (0:ℝ) ≤ 1) hd0]
  have hB2 : 0 ≤ B2 := by dsimp [B2]; positivity
  have hB3 : 0 ≤ B3 := by dsimp [B3]; positivity
  have h23 : B2 ≤ B3 := by
    have hh := mul_le_mul_of_nonneg_left hScale
      (show 0 ≤ 4*jointAmplitude d C0 θ*(jointScale d Lc s)^2 by positivity)
    dsimp [B2,B3]
    nlinarith [mul_nonneg hAmp (pow_nonneg (show 0 ≤ jointScale d Lc s by linarith) 3)]
  have hn := chartObjective_joint_norms A hA k hk H K c hc hc0 S hSpos hS.2 hθ.le hs
    hLc hd hdn hC0 hK hfloor hbudget hcoeff
  have hH : ContDiffAt ℝ ∞ (fun t : ℝ => H+t•K) 0 :=
    contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
  have hm : ∀ T ∈ densitySet, objective (H+(0:ℝ)•K) A ((1:ℝ)/2^k) (c 0) θ T ≤
      objective (H+(0:ℝ)•K) A ((1:ℝ)/2^k) (c 0) θ S := by
    simpa only [zero_smul,add_zero] using hmax
  have h2 := potential_second_abs_le A hA k hk θ hθ (fun t => H+t•K) c hH hc hc0
    S hS hm hB2 hn.1
  have h3 := potential_third_le A hA k hk θ hθ (fun t => H+t•K) c hH hc hc0
    S hS hm hB2 hB3 hn.1 hn.2
  refine ⟨h2.trans ?_, h3⟩
  have hf : 1 ≤ 1+B2/(θ/2) := by
    have hh : 0 ≤ B2/(θ/2) := by positivity
    linarith
  calc
    B2*(1+B2/(θ/2))^2 ≤ B3*(1+B2/(θ/2))^2 :=
      mul_le_mul_of_nonneg_right h23 (sq_nonneg _)
    _ ≤ B3*(1+B2/(θ/2))^3 := by
      apply mul_le_mul_of_nonneg_left _ hB3
      nlinarith [mul_le_mul_of_nonneg_left hf (sq_nonneg (1+B2/(θ/2)))]

end AugmentedHigherRankKS
