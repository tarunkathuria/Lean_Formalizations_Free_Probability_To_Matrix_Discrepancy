import MatrixSpencer.RectangularRidgePrimitiveParameters
import MatrixSpencer.RectangularRidgeNumericalOptimizerFloor

/-! One response coefficient for all live subsets, with the exponent and
weight tuned once at the original input count. Its aspect-ratio dependence
is retained; the polynomial bound is used only to choose the numerical mesh. -/

noncomputable section
namespace MatrixSpencer.RectangularRidgeUniformResponse
open RectangularRidgePrimitiveParameters
open RectangularRidgeNumericalOptimizerFloor (size)

def coefficient (N D : ℕ) (hN : 1≤N) : ℝ :=
  RectangularParameters.globalResponseCoefficient (exponent N D hN) (weight N D hN) N

theorem coefficient_two_le {N D : ℕ} (hN : 1≤N) (hND : N≤D) : 2≤coefficient N D hN :=
  RectangularParameters.globalResponseCoefficient_two_le (exponent_positive N D hN)
    (weight_positive hN hND) (Nat.cast_nonneg N)

theorem local_response_le {N D : ℕ} (hN : 1≤N) (hND : N≤D)
    {ℓ : ℝ} (hℓ : 0≤ℓ) (hℓN : ℓ≤N) :
    2*Real.sqrt ℓ+(6*(4096:ℝ)^exponent N D hN/(weight N D hN*exponent N D hN))*
      ℓ^(1-exponent N D hN)≤coefficient N D hN*Real.sqrt ℓ :=
  RectangularParameters.response_le_global_coefficient (exponent_positive N D hN)
    (exponent_le_half N D hN) (weight_positive hN hND) hℓ hℓN

theorem scaled_coefficient_le {N D : ℕ} (hN : 1≤N) (hND : N≤D) :
    (coefficient N D hN+1)*Real.sqrt (N:ℝ)≤
      486*Real.sqrt ((N:ℝ)*(1+Real.log ((D:ℝ)/N))) := by
  have hq := exponent_positive N D hN
  have hqh := exponent_le_half N D hN
  have hθ := weight_positive hN hND
  have hreg : 0≤weight N D hN*(D:ℝ)^exponent N D hN/(1-exponent N D hN) := by
    have hq1 : 0<1-exponent N D hN := by linarith
    positivity
  have he := RectangularParameters.global_coefficient_budget_identity
    (θ:=weight N D hN) hqh (show (0:ℝ)≤N from Nat.cast_nonneg N)
  change (coefficient N D hN+1)*Real.sqrt (N:ℝ)=_ at he
  have hr : 6*(4096:ℝ)^exponent N D hN/(weight N D hN*exponent N D hN)*(N:ℝ)^(1-exponent N D hN)=
      6*((4096:ℝ)^exponent N D hN*(N:ℝ)^(1-exponent N D hN)/(weight N D hN*exponent N D hN)) := by ring
  rw [hr] at he
  have hb := RectangularRidgeTuning.optimized_budget_le hN hND
  change Real.sqrt (N:ℝ)+weight N D hN*(D:ℝ)^exponent N D hN/(1-exponent N D hN)+
    (4096:ℝ)^exponent N D hN*(N:ℝ)^(1-exponent N D hN)/(weight N D hN*exponent N D hN)≤_ at hb
  nlinarith [Real.sqrt_nonneg (N:ℝ)]

/-- The logarithmic aspect-ratio factor remains in the bound; no square-case
constant response coefficient is being substituted. -/
theorem logarithmic_coefficient_le {N D : ℕ} (hN : 1≤N) (hND : N≤D) :
    coefficient N D hN+1≤486*Real.sqrt (1+Real.log ((D:ℝ)/N)) := by
  have hn : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hs : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hn
  have hh := scaled_coefficient_le hN hND
  rw [Real.sqrt_mul hn.le] at hh
  apply (mul_le_mul_right hs).mp
  convert hh using 1 <;> ring

theorem polynomial_coefficient_le {N D : ℕ} (hN : 1≤N) (hND : N≤D) :
    coefficient N D hN+1≤RectangularRidgeNumericalParameters.phaseResponse (size D N) := by
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hd : (1:ℝ)≤D := by exact_mod_cast hN.trans hND
  have hr : (1:ℝ)≤(D:ℝ)/N := by
    apply (le_div_iff₀ (by linarith : (0:ℝ)<N)).mpr
    simpa using (Nat.cast_le.mpr hND : (N:ℝ)≤D)
  have hb := scaled_coefficient_le hN hND
  have hlog := RectangularRidgeParameters.logarithmic_scale_le_size hd hn
  rw [RectangularParameters.aspect,max_eq_right hr] at hlog
  have hsqrt : 1≤Real.sqrt (N:ℝ) := Real.le_sqrt_of_sq_le (by simpa using hn)
  have hB := coefficient_two_le hN hND
  have hfirst : coefficient N D hN+1≤486*size D N := by
    have hm := mul_le_mul_of_nonneg_left hsqrt (by linarith : 0≤coefficient N D hN+1)
    dsimp [RectangularRidgeParameters.size,size] at *
    nlinarith
  have hs : 1≤size D N := by dsimp [size]; linarith
  have hp : size D N≤size D N^3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hs (show 1≤(3:ℕ) by omega)
  calc
    coefficient N D hN+1≤486*size D N := hfirst
    _ ≤ 8192*size D N := by nlinarith
    _ ≤ 8192*size D N^3 := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = _ := by norm_num [RectangularRidgeNumericalParameters.phaseResponse,RectangularRidgeNumericalParameters.big]

def duration (N D : ℕ) (hN : 1≤N) : ℝ := 1/(coefficient N D hN+1)

theorem duration_positive {N D : ℕ} (hN : 1≤N) (hND : N≤D) : 0<duration N D hN := by
  have := coefficient_two_le hN hND
  unfold duration
  positivity

theorem duration_le_third {N D : ℕ} (hN : 1≤N) (hND : N≤D) : duration N D hN≤1/3 :=
  one_div_le_one_div_of_le (by norm_num) (by linarith [coefficient_two_le hN hND])

theorem mesh_time_le {N D : ℕ} (hN : 1≤N) (hND : N≤D) :
    RectangularRidgeNumericalParameters.mesh (size D N)^2≤duration N D hN/2 := by
  have hB := coefficient_two_le hN hND
  have hs : 1≤size D N := by
    have hn : (1:ℝ)≤N := by exact_mod_cast hN
    dsimp [size]
    linarith [show (0:ℝ)≤D from Nat.cast_nonneg D]
  have hh := RectangularRidgeNumericalParameters.mesh_time_le hs (by linarith : 0<coefficient N D hN+1)
    (polynomial_coefficient_le hN hND)
  simpa only [duration,one_div] using hh

end MatrixSpencer.RectangularRidgeUniformResponse
