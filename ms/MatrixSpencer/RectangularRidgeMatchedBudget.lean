import MatrixSpencer.MSManuscriptMatchedJointBounds
import MatrixSpencer.RectangularRidgeCovarianceBudget

/-! Explicit polynomial scalar caps for the actual matched movement objective
and the fourth-derivative envelope expression. The separate analytic theorems
connect these expressions to the objective and its maximizing density. -/

noncomputable section
namespace MatrixSpencer.RectangularRidgeMatchedBudget
open RectangularRidgeNumericalParameters
set_option exponentiation.threshold 2048
set_option maxRecDepth 4096

variable {ι n : Type*} [Fintype ι] [Fintype n]

theorem valueCap_le {P R b L : ℝ} (hP : 1 ≤ P)
    (hi : (Fintype.card ι : ℝ) ≤ P) (hn : (Fintype.card n : ℝ) ≤ P)
    (hR : 0 ≤ R) (hRP : R ≤ P^2) (hb : 0 ≤ b) (hbP : b ≤ P^2)
    (hL : 0 ≤ L) (hLP : L ≤ P) :
    MSManuscriptComplexValueBoundScaled.valueCap ι n (R+b) 0 L ≤ big P 4 3 := by
  have hP0 : 0 ≤ P := by linarith
  have hprod : (Fintype.card ι : ℝ) * L ≤ P^2 := by
    simpa [pow_two] using mul_le_mul hi hLP hL hP0
  have hs : Real.sqrt (2 * (4 * (Fintype.card ι : ℝ)^2 * L^2)) ≤
      3 * (Fintype.card ι : ℝ) * L := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith [sq_nonneg ((Fintype.card ι : ℝ)*L)]
  have hs' : Real.sqrt (2 * (4 * (Fintype.card ι : ℝ)^2 * L^2)) ≤ 3*P^2 :=
    hs.trans (by nlinarith)
  have hh := mul_le_mul hn (show R+b ≤ 2*P^2 by linarith) (add_nonneg hR hb) hP0
  have hf := mul_le_mul hn hs' (Real.sqrt_nonneg _) hP0
  unfold MSManuscriptComplexValueBoundScaled.valueCap KSComplexObjectiveBound.valueCap big
  norm_num only [zero_mul, add_zero, Nat.reducePow]
  nlinarith [pow_nonneg hP0 3]

theorem radius_inverse_le {P γ μ : ℝ} (hP : 1 ≤ P)
    (hγ : ((2:ℝ)^15)⁻¹ ≤ γ) (hμ : densityFloor P ≤ μ) :
    10 / MSManuscriptMatchedComplex.radius γ μ ≤ big P 38 6 := by
  have hh := RectangularRidgeCovarianceBudget.radius_inverse_le hP hγ hμ
  calc
    10 / MSManuscriptMatchedComplex.radius γ μ =
        4 * (10 / MSManuscriptComplexSourceDomain.radius γ μ) := by
      unfold MSManuscriptMatchedComplex.radius
      ring
    _ ≤ 4 * big P 36 6 := mul_le_mul_of_nonneg_left hh (by norm_num)
    _ = big P 38 6 := by norm_num [big]; ring

theorem source_jointCap_le {P R b γ μ L : ℝ} (hP : 1 ≤ P)
    (hi : (Fintype.card ι : ℝ) ≤ P) (hn : (Fintype.card n : ℝ) ≤ P)
    (hR : 0 ≤ R) (hRP : R ≤ P^2) (hb : 0 ≤ b) (hbP : b ≤ P^2)
    (hL : 0 ≤ L) (hLP : L ≤ P)
    (hγ : ((2:ℝ)^15)⁻¹ ≤ γ) (hμ : densityFloor P ≤ μ) :
    MSManuscriptMatchedJointBounds.jointCap ι n R b 0 γ μ L ≤ big P 156 27 := by
  have hP0 : 0 < P := by linarith
  have hγ0 : 0 < γ := lt_of_lt_of_le (by positivity) hγ
  have hμ0 : 0 < μ := lt_of_lt_of_le (small_pos hP0 10 6) hμ
  have hp : 0 ≤ 10 / MSManuscriptMatchedComplex.radius γ μ := by
    unfold MSManuscriptMatchedComplex.radius MSManuscriptComplexSourceDomain.radius
    positivity
  have hp4 : (10 / MSManuscriptMatchedComplex.radius γ μ)^4 ≤ big P 152 24 := by
    calc
      _ ≤ (big P 38 6)^4 := pow_le_pow_left₀ hp (radius_inverse_le hP hγ hμ) 4
      _ = _ := by simp only [big, mul_pow, ← pow_mul]
  unfold MSManuscriptMatchedJointBounds.jointCap
  calc
    _ ≤ big P 4 3 * big P 152 24 :=
      mul_le_mul (valueCap_le hP hi hn hR hRP hb hbP hL hLP) hp4 (by positivity)
        (big_pos hP0 4 3).le
    _ = _ := big_mul P 4 3 152 24

def commonJointCap (P : ℝ) : ℝ := big P 160 32

/-- The actual mixed-regularizer norm formula has a polynomial bound, including
the fourth power of the dyadic order. The relaxed weight bound is sufficient
for the primitive arithmetic tuning. -/
theorem regularizer_budget_le {P θ κ d p μ : ℝ} (hP : 1 ≤ P)
    (hw : θ+κ ≤ 128*P) (hd0 : 0 ≤ d) (hd : d ≤ P)
    (hp0 : 0 ≤ p) (hp : p ≤ 8*P) (hμ : densityFloor P ≤ μ) :
    256*(2*(θ+κ)*d*(p^4*(120/μ)^4)) ≤ big P 96 30 := by
  have hP0 : 0 < P := by linarith
  have hμ0 : 0 < μ := lt_of_lt_of_le (small_pos hP0 10 6) hμ
  have ha : 120/μ ≤ big P 17 6 := by
    calc
      _ ≤ 120/small P 10 6 :=
        div_le_div_of_nonneg_left (by norm_num) (small_pos hP0 10 6) hμ
      _ = 120*big P 10 6 := by simp [small, div_eq_mul_inv]
      _ ≤ 128*big P 10 6 := by nlinarith [big_pos hP0 10 6]
      _ = big P 17 6 := by norm_num [big]; ring
  have ha4 : (120/μ)^4 ≤ big P 68 24 := by
    calc
      _ ≤ (big P 17 6)^4 := pow_le_pow_left₀ (by positivity) ha 4
      _ = _ := by simp only [big, mul_pow, ← pow_mul]
  have hp4 : p^4 ≤ big P 12 4 := by
    calc
      _ ≤ (8*P)^4 := pow_le_pow_left₀ hp0 hp 4
      _ = _ := by norm_num [big, mul_pow]
  have hinner : p^4*(120/μ)^4 ≤ big P 80 28 := by
    calc
      _ ≤ big P 12 4 * big P 68 24 := mul_le_mul hp4 ha4 (by positivity)
        (big_pos hP0 12 4).le
      _ = _ := big_mul P 12 4 68 24
  have hwprod := mul_le_mul hw hd hd0 (by positivity : 0≤128*P)
  have houter : 512*(θ+κ)*d ≤ big P 16 2 := by
    calc
      _ ≤ 512*((128*P)*P) := by nlinarith
      _ = _ := by norm_num [big]; ring
  calc
    _ = (512*(θ+κ)*d)*(p^4*(120/μ)^4) := by ring
    _ ≤ big P 16 2 * big P 80 28 := mul_le_mul houter hinner (by positivity)
      (big_pos hP0 16 2).le
    _ = _ := big_mul P 16 2 80 28

theorem source_add_regularizer_le {P J R : ℝ} (hP : 1 ≤ P)
    (hJ : J ≤ big P 156 27) (hR : R ≤ big P 96 30) :
    J+R ≤ commonJointCap P := by
  have h1 : J ≤ big P 159 32 := hJ.trans (big_mono hP (by omega) (by omega))
  have h2 : R ≤ big P 159 32 := hR.trans (big_mono hP (by omega) (by omega))
  calc
    _ ≤ big P 159 32 + big P 159 32 := add_le_add h1 h2
    _ = _ := by norm_num [commonJointCap, big]; ring

/-- The explicit response envelope is bounded by the final fourth-derivative
numerical budget whenever its common joint cap has the displayed size. -/
theorem envelope_fourth_le {P B κ : ℝ} (hP : 1 ≤ P) (hB0 : 0 ≤ B)
    (hB : B ≤ commonJointCap P) (hκ : P⁻¹ ≤ κ) :
    (B + 3*B^2/(κ/2)) * (1+B/(κ/2))^4 ≤ fourthCap P := by
  let G := commonJointCap P
  have hP0 : 0 < P := by linarith
  have hG1 : 1 ≤ G := big_one_le hP 160 32
  have hG0 : 0 ≤ G := by linarith
  have hκ0 : 0 < κ := lt_of_lt_of_le (inv_pos.mpr hP0) hκ
  have hPk : 1 ≤ P*κ := by
    have hh := mul_le_mul_of_nonneg_left hκ hP0.le
    simpa [ne_of_gt hP0] using hh
  have hik : (κ/2)⁻¹ ≤ 2*P := (inv_le_iff_one_le_mul₀ (by positivity)).2 (by nlinarith)
  have hdiv : B/(κ/2) ≤ 2*P*G := by
    rw [div_eq_mul_inv]
    have hh := mul_le_mul hB hik (by positivity) hG0
    nlinarith
  have hBsq : B^2 ≤ G^2 := pow_le_pow_left₀ hB0 hB 2
  have hdiv2 : 3*B^2/(κ/2) ≤ 6*P*G^2 := by
    rw [div_eq_mul_inv]
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hBsq (by norm_num : (0:ℝ)≤3))
      hik (by positivity) (by positivity : 0≤3*G^2)
    nlinarith
  have hPG : G ≤ P*G^2 := by
    have hs : G ≤ G^2 := by nlinarith
    have hp := mul_le_mul_of_nonneg_right hP (sq_nonneg G)
    nlinarith
  have hfirst : B+3*B^2/(κ/2) ≤ big P 323 65 := by
    calc
      _ ≤ 8*P*G^2 := by nlinarith [show B≤G from hB, mul_nonneg hP0.le (sq_nonneg G)]
      _ = big P 323 65 := by
        dsimp [G, commonJointCap]
        simp only [big, mul_pow, ← pow_mul]
        norm_num
        ring
  have hPG1 : 1 ≤ P*G := one_le_mul_of_one_le_of_one_le hP hG1
  have hsecond : 1+B/(κ/2) ≤ big P 162 33 := by
    calc
      _ ≤ 4*P*G := by nlinarith
      _ = big P 162 33 := by norm_num [G, commonJointCap, big]; ring
  have hsecond0 : 0 ≤ 1+B/(κ/2) := by positivity
  have hfourth : (1+B/(κ/2))^4 ≤ big P 648 132 := by
    calc
      _ ≤ (big P 162 33)^4 := pow_le_pow_left₀ hsecond0 hsecond 4
      _ = _ := by simp only [big, mul_pow, ← pow_mul]
  calc
    _ ≤ big P 323 65 * big P 648 132 := mul_le_mul hfirst hfourth (by positivity)
      (big_pos hP0 323 65).le
    _ = big P 971 197 := big_mul P 323 65 648 132
    _ ≤ fourthCap P := big_mono hP (by omega) (by omega)

end MatrixSpencer.RectangularRidgeMatchedBudget
