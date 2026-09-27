import MatrixSpencer.KSHermitianDirections
import MatrixSpencer.KSComplexProjectionGeometry

/-!
# Arithmetic finite-difference reports for the physical Hermitian gradient

Only matrix units, scalar arithmetic, and the supplied value report occur in
the numerical definition. The analytic chart is used to identify the exact
gradient and measure its Frobenius error, never as an algorithm input.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSHermitianGradientReport

open KSHermitianDirections KSFullHermitianChart KSComplexProjectionGeometry
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

def difference (value : Matrix n n ℂ → ℝ) (S D : Matrix n n ℂ) (t : ℝ) : ℝ :=
  (value (S + t • D) - value (S - t • D)) / (2 * t)

def rawReport (value : Matrix n n ℂ → ℝ) (S : Matrix n n ℂ) (t : ℝ) :
    Matrix n n ℂ := fun i j =>
  ⟨difference value S (realDirection i j) t, difference value S (imagDirection i j) t⟩

def hermitianize (A : Matrix n n ℂ) : Matrix n n ℂ := (1 / 2 : ℝ) • (A + Aᴴ)

def report (value : Matrix n n ℂ → ℝ) (S : Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ :=
  hermitianize (rawReport value S t)

theorem hermitianize_isHermitian (A : Matrix n n ℂ) : (hermitianize A).IsHermitian := by
  unfold hermitianize Matrix.IsHermitian
  simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_add,
    Matrix.conjTranspose_conjTranspose]
  rw [add_comm]

theorem report_isHermitian (value : Matrix n n ℂ → ℝ) (S : Matrix n n ℂ) (t : ℝ) :
    (report value S t).IsHermitian := hermitianize_isHermitian _

theorem hermitianize_entry_error {G A : Matrix n n ℂ} (hG : G.IsHermitian) {e : ℝ}
    (hre : ∀ i j, |(A i j).re - (G i j).re| ≤ e)
    (him : ∀ i j, |(A i j).im - (G i j).im| ≤ e) :
    ∀ i j, |(hermitianize A i j).re - (G i j).re| ≤ e ∧
      |(hermitianize A i j).im - (G i j).im| ≤ e := by
  intro i j
  have hji : G j i = star (G i j) := (hG.apply j i).symm
  have hr := abs_le.mp (hre i j)
  have hr' := abs_le.mp (hre j i)
  have hi := abs_le.mp (him i j)
  have hi' := abs_le.mp (him j i)
  simp only [hji, Complex.star_def, Complex.conj_re, Complex.conj_im] at hr' hi'
  simp only [hermitianize, Matrix.smul_apply, Matrix.add_apply, Matrix.conjTranspose_apply,
    Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, sub_zero, Complex.add_re, Complex.add_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith

theorem energy_le_of_entry_error {A G : Matrix n n ℂ} {e : ℝ} (he : 0 ≤ e)
    (hre : ∀ i j, |(A i j).re - (G i j).re| ≤ e)
    (him : ∀ i j, |(A i j).im - (G i j).im| ≤ e) :
    complexEnergy (A - G) ≤ (2 * (Fintype.card n : ℝ) * e) ^ 2 := by
  calc
    complexEnergy (A - G) ≤ ∑ _i : n, ∑ _j : n, 2 * e ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have hr := (sq_le_sq₀ (abs_nonneg _) he).mpr (hre i j)
      have hi := (sq_le_sq₀ (abs_nonneg _) he).mpr (him i j)
      simp only [Matrix.sub_apply, Complex.sq_norm, Complex.normSq_apply,
        Complex.sub_re, Complex.sub_im]
      rw [sq_abs] at hr hi
      nlinarith
    _ ≤ (2 * (Fintype.card n : ℝ) * e) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      nlinarith [sq_nonneg ((Fintype.card n : ℝ) * e)]

/-- Scalar derivative reports with entry error `e` give a physical Frobenius
gradient error at most `2 * dimension * e`, including dimension zero. -/
theorem report_energy_le (value : Matrix n n ℂ → ℝ) (S G : Matrix n n ℂ)
    (hG : G.IsHermitian) (t : ℝ) {e : ℝ} (he : 0 ≤ e)
    (hre : ∀ i j, |difference value S (realDirection i j) t - (G i j).re| ≤ e)
    (him : ∀ i j, |difference value S (imagDirection i j) t - (G i j).im| ≤ e) :
    Real.sqrt (complexEnergy (report value S t - G)) ≤ 2 * (Fintype.card n : ℝ) * e := by
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  have hh := hermitianize_entry_error hG (A := rawReport value S t) hre him
  exact energy_le_of_entry_error he (fun i j => (hh i j).1) (fun i j => (hh i j).2)

/-- The chart norm agrees with the full physical Frobenius energy. -/
theorem chart_energy (x : Coordinates n) :
    complexEnergy (chart n x : Matrix n n ℂ) = ‖x‖ ^ 2 := by
  have hH : (chart n x : Matrix n n ℂ).IsHermitian := (chart n x).property
  have he := entryEnergy_eq_realTrace_adjoint_mul (chart n x : Matrix n n ℂ)
  rw [hH.eq, chart_trace_square] at he
  simpa only [entryEnergy, complexEnergy, Complex.normSq_eq_norm_sq] using he

theorem chart_inverse_energy (S : selfAdjoint (Matrix n n ℂ)) :
    complexEnergy (S : Matrix n n ℂ) = ‖(chartEquiv n).symm S‖ ^ 2 := by
  simpa only [chart, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply] using chart_energy ((chartEquiv n).symm S)

theorem chart_inverse_norm (S : selfAdjoint (Matrix n n ℂ)) :
    ‖(chartEquiv n).symm S‖ = Real.sqrt (complexEnergy (S : Matrix n n ℂ)) := by
  rw [chart_inverse_energy, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- The exact gradient in physical matrix form represents the actual
Fréchet derivative in every Hermitian direction. -/
theorem trace_gradient_direction (f : Coordinates n → ℝ) (x : Coordinates n)
    (D : selfAdjoint (Matrix n n ℂ)) :
    realTrace ((chart n (gradient f x) : Matrix n n ℂ) * (D : Matrix n n ℂ)) =
      fderiv ℝ f x ((chartEquiv n).symm D) := by
  have hD : (D : Matrix n n ℂ) = (chart n ((chartEquiv n).symm D) : Matrix n n ℂ) :=
    congrArg Subtype.val ((chartEquiv n).apply_symm_apply D).symm
  rw [hD, chart_trace_pairing]
  exact InnerProductSpace.toDual_symm_apply

theorem real_gradient_entry (f : Coordinates n → ℝ) (x : Coordinates n) (i j : n) :
    ((chart n (gradient f x) : Matrix n n ℂ) i j).re =
      fderiv ℝ f x ((chartEquiv n).symm
        ⟨realDirection i j, realDirection_isHermitian i j⟩) := by
  rw [← trace_realDirection _ (chart n (gradient f x)).property]
  exact trace_gradient_direction f x ⟨_, realDirection_isHermitian i j⟩

theorem imag_gradient_entry (f : Coordinates n → ℝ) (x : Coordinates n) (i j : n) :
    ((chart n (gradient f x) : Matrix n n ℂ) i j).im =
      fderiv ℝ f x ((chartEquiv n).symm
        ⟨imagDirection i j, imagDirection_isHermitian i j⟩) := by
  rw [← trace_imagDirection _ (chart n (gradient f x)).property]
  exact trace_gradient_direction f x ⟨_, imagDirection_isHermitian i j⟩

/-- Error against the actual full gradient, in precisely the Hilbert norm
used by the proved projected-iteration estimate. -/
theorem report_coordinate_error (value : Matrix n n ℂ → ℝ) (S : Matrix n n ℂ)
    (f : Coordinates n → ℝ) (x : Coordinates n) (t : ℝ) {e : ℝ} (he : 0 ≤ e)
    (hre : ∀ i j, |difference value S (realDirection i j) t -
      fderiv ℝ f x ((chartEquiv n).symm
        ⟨realDirection i j, realDirection_isHermitian i j⟩)| ≤ e)
    (him : ∀ i j, |difference value S (imagDirection i j) t -
      fderiv ℝ f x ((chartEquiv n).symm
        ⟨imagDirection i j, imagDirection_isHermitian i j⟩)| ≤ e) :
    ‖(chartEquiv n).symm ⟨report value S t, report_isHermitian value S t⟩ - gradient f x‖ ≤
      2 * (Fintype.card n : ℝ) * e := by
  have hgrad : gradient f x = (chartEquiv n).symm (chart n (gradient f x)) :=
    ((chartEquiv n).symm_apply_apply (gradient f x)).symm
  conv_lhs => rhs; rw [hgrad]
  rw [← map_sub, chart_inverse_norm]
  apply report_energy_le value S _ (chart n (gradient f x)).property t he
  · intro i j
    rw [real_gradient_entry]
    exact hre i j
  · intro i j
    rw [imag_gradient_entry]
    exact him i j

end MatrixSpencer.KSHermitianGradientReport
