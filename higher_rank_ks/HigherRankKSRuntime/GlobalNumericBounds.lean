import HigherRankKSRuntime.ExecutedEpoch
import AugmentedHigherRankKS.RuntimeParameters
import AugmentedHigherRankKS.Parameters

open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace HigherRankKSRuntime.GlobalEpochs
open AugmentedHigherRankKS RuntimeParameters

def alpha (z : Dimensions) (ε : ℝ) := 8*a z*ε
def delta (z : Dimensions) (ε : ℝ) := 5*Real.sqrt (alpha z ε)
def cleanupCharge (z : Dimensions) (ε : ℝ) := 2*ε*(rho z+zeta z/a z)

theorem cleanupCharge_nonneg (z : Dimensions) (hz : z ∈ Domain)
    {ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ cleanupCharge z ε := by
  have ha := a_poly.positive z hz
  have ht := theta_poly.positive z hz
  unfold cleanupCharge rho zeta
  positivity

theorem numeric_error_small (z : Dimensions) (hz : z ∈ Domain)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hεN : 1/z.N ≤ ε) :
    2*theta z*Real.sqrt (4*z.D)+z.N*cleanupCharge z ε ≤ alpha z ε := by
  have hN := hz.1
  have hD := hz.2.1
  have hq := hz.2.2
  have hT : 4 ≤ size z := by dsimp [size]; linarith
  have hTpos : 0 < size z := by linarith
  have hNpos : 0 < z.N := by linarith
  have ha1 : 1 ≤ a z := le_trans (by norm_num) (a_ge z hz)
  have ha : 0 < a z := by linarith
  have ht := theta_poly.positive z hz
  have hsqrt : Real.sqrt (4*z.D) ≤ 2*z.D := by
    have hs := Real.sq_sqrt (show 0 ≤ 4*z.D by positivity)
    have hn := Real.sqrt_nonneg (4*z.D)
    nlinarith
  have hdiv : theta z/a z ≤ theta z := (div_le_iff₀ ha).2 (by nlinarith)
  have hc : cleanupCharge z ε ≤ 4*theta z := by
    unfold cleanupCharge rho zeta
    have he := mul_le_mul_of_nonneg_right hε1 (show 0 ≤ theta z+theta z/a z by positivity)
    nlinarith
  have herr : 2*theta z*Real.sqrt (4*z.D)+z.N*cleanupCharge z ε ≤
      4*size z*theta z := by
    have hs := mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ 2*theta z by positivity)
    have hn := mul_le_mul_of_nonneg_left hc (show 0 ≤ z.N by linarith)
    have hND : z.N+z.D ≤ size z := by dsimp [size]; linarith
    nlinarith
  have hTN : z.N ≤ size z := by dsimp [size]; linarith
  have hT8 : 4 ≤ size z^8 := by
    have hh : size z ≤ size z^8 := by
      simpa using pow_le_pow_right₀ (show 1 ≤ size z by linarith) (show 1≤8 by omega)
    linarith
  have hpow : 4*z.N*size z ≤ size z^10 := by
    calc
      _ ≤ 4*size z*size z := by gcongr
      _ ≤ size z^8*size z^2 := by nlinarith
      _ = _ := by ring
  have hsmall : 4*size z*theta z ≤ 1/z.N := by
    unfold theta
    apply (le_div_iff₀ hNpos).2
    have hp : 0 < size z^10 := pow_pos hTpos _
    calc
      4*size z*(size z^10)⁻¹*z.N = (4*z.N*size z)/(size z^10) := by ring
      _ ≤ 1 := (div_le_one hp).2 hpow
  have hα : 1/z.N ≤ alpha z ε := by
    unfold alpha
    have hh := mul_le_mul_of_nonneg_right ha1 hε
    linarith
  exact herr.trans (hsmall.trans hα)

theorem initial_numeric_budget {N d r : ℕ} [NeZero d]
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i,(A i).PosSemidef)
    (x : CubePoint (Fin N)) (z : Dimensions) (hz : z ∈ Domain)
    (hNdim : (N:ℝ)=z.N) (hDdim : (d:ℝ)=z.D)
    {ε β : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hεN : 1/z.N ≤ ε)
    (hAnorm : ∀ i,‖A i‖ ≤ ε) (hr : ∀ i,(A i).rank ≤ r)
    (hβ : 0 < β) (hβ1 : β < 1) (hrpow : (r:ℝ)^β ≤ 2)
    (hlarge : (delta z ε)^2 < ‖cubeMass A x‖) :
    epochPotential A β (theta z) x.val (resetState (a z) 4 x)+
      (N:ℝ)*cleanupCharge z ε ≤ delta z ε*Real.sqrt ‖cubeMass A x‖ := by
  have ha := a_poly.positive z hz
  have ht := theta_poly.positive z hz
  have hi := resetState_potential_le A hA x hε hAnorm hr hβ hβ1
    (by positivity : 0 ≤ a z*4) ht.le
  have hcard : (Fintype.card (FourSpin (Fin d)):ℝ) = 4*z.D := by
    simp [FourSpin,Fintype.card_sum]
    rw [← hDdim]
    ring
  rw [hcard] at hi
  have hb : 0 ≤ ‖cubeMass A x‖ := norm_nonneg _
  have hrad : 0 ≤ 4*(a z*4)*ε*(r:ℝ)^β*‖cubeMass A x‖ := by positivity
  have hα : 0 ≤ alpha z ε := by unfold alpha; positivity
  have hrp := mul_le_mul_of_nonneg_right hrpow
    (show 0 ≤ 4*(a z*4)*ε*‖cubeMass A x‖ by positivity)
  have hs1 := Real.sq_sqrt hrad
  have hs2 := Real.sq_sqrt (mul_nonneg hα hb)
  have hn1 := Real.sqrt_nonneg (4*(a z*4)*ε*(r:ℝ)^β*‖cubeMass A x‖)
  have hn2 := Real.sqrt_nonneg (alpha z ε*‖cubeMass A x‖)
  have hmain : 2*Real.sqrt (4*(a z*4)*ε*(r:ℝ)^β*‖cubeMass A x‖) ≤
      4*Real.sqrt (alpha z ε*‖cubeMass A x‖) := by
    have hrle : 4*(a z*4)*ε*(r:ℝ)^β*‖cubeMass A x‖ ≤
        4*(alpha z ε*‖cubeMass A x‖) := by dsimp [alpha]; nlinarith
    have hh := Real.sqrt_le_sqrt hrle
    conv_rhs at hh => rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]
    rw [show Real.sqrt (4:ℝ)=2 by norm_num] at hh
    linarith
  have he := numeric_error_small z hz hε hε1 hεN
  have habs := epoch_error_absorption hα hlarge he
  rw [hNdim]
  unfold delta at *
  linarith

theorem delta_le_rank_scale (z : Dimensions) {ε : ℝ} (hε : 0 ≤ ε)
    (hq : 0 ≤ z.q) : delta z ε ≤ 500*Real.sqrt (ε*z.q) := by
  have he : alpha z ε = 8192*(ε*z.q) := by unfold alpha a; ring
  unfold delta
  rw [he,Real.sqrt_mul (by norm_num : (0:ℝ)≤8192)]
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤8192)
  have hn := Real.sqrt_nonneg (8192:ℝ)
  have hb : 5*Real.sqrt (8192:ℝ) ≤ 500 := by nlinarith
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg (ε*z.q))

theorem discard_error_le (z : Dimensions) (hz : z ∈ Domain)
    {ε : ℝ} (hεN : 1/z.N ≤ ε) : z.N*eta z ≤ ε := by
  have hN := hz.1
  have hT : 1 ≤ size z := size_one z hz
  have hNT : z.N ≤ size z := by rcases hz with ⟨_,hD,hq⟩; dsimp [size]; linarith
  have hpow : z.N^2 ≤ size z^10 := by
    exact (pow_le_pow_left₀ (by linarith) hNT 2).trans
      (pow_le_pow_right₀ hT (by omega))
  have hNpos : 0 < z.N := by linarith
  have hp : 0 < size z^10 := pow_pos (by linarith) _
  have hh : z.N*eta z ≤ 1/z.N := by
    apply (le_div_iff₀ hNpos).2
    unfold eta theta
    calc
      z.N*(size z^10)⁻¹*z.N = z.N^2/(size z^10) := by ring
      _ ≤ 1 := (div_le_one hp).2 hpow
  exact hh.trans hεN

theorem final_rank_bound (z : Dimensions) (hz : z ∈ Domain)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hεN : 1/z.N ≤ ε) :
    4*delta z ε+z.N*eta z ≤ 3000*Real.sqrt (ε*z.q) := by
  have hd := delta_le_rank_scale z hε (by linarith [hz.2.2])
  have he := discard_error_le z hz hεN
  have hs : ε ≤ Real.sqrt (ε*z.q) := by
    have hq := hz.2.2
    have heq : ε^2 ≤ ε*z.q := by nlinarith
    have hsq := Real.sq_sqrt (show 0 ≤ ε*z.q by positivity)
    have hsn := Real.sqrt_nonneg (ε*z.q)
    nlinarith
  nlinarith [Real.sqrt_nonneg (ε*z.q)]

theorem runtime_log_conversion {r : ℕ} (hr : 1 ≤ r) {q ε : ℝ}
    (hq : 0 ≤ q) (hqupper : q ≤ 2*HigherRankKS.logRank r) (hε : 0 ≤ ε) :
    3000*Real.sqrt (ε*q) ≤ 6000*Real.sqrt (ε*Real.log (2*(r:ℝ))) := by
  have hlog : 0 ≤ Real.log (2*(r:ℝ)) := by
    apply Real.log_nonneg
    have hr' : (1:ℝ)≤r := by exact_mod_cast hr
    linarith
  have hlog2 := Real.log_two_gt_d9
  have hlog2pos : 0 < Real.log 2 := by linarith
  have hq4 : q ≤ 4*Real.log (2*(r:ℝ)) := by
    apply hqupper.trans
    unfold HigherRankKS.logRank Real.logb
    apply (le_of_mul_le_mul_right ?_ hlog2pos)
    have he : 2*(Real.log (2*(r:ℝ))/Real.log 2)*Real.log 2 =
        2*Real.log (2*(r:ℝ)) := by field_simp
    rw [he]
    nlinarith
  have hh := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hq4 hε)
  rw [show ε*(4*Real.log (2*(r:ℝ))) = 4*(ε*Real.log (2*(r:ℝ))) by ring] at hh
  conv_rhs at hh => rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]
  rw [show Real.sqrt (4:ℝ)=2 by norm_num] at hh
  linarith

end HigherRankKSRuntime.GlobalEpochs
