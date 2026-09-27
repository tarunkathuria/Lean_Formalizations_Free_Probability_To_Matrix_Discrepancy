import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Arithmetic error propagation for the KS finite-difference stencils

These theorems take Taylor remainder bounds and value-report accuracies as
explicit hypotheses.  They do not prove differentiability, a Taylor theorem,
or the existence/cost of the actual potential's value oracle.
-/

noncomputable section

namespace MatrixSpencer
namespace KSFiniteDifference

/-- The degree-three Taylor polynomial with derivatives as coefficients. -/
def cubic (f₀ d₁ d₂ d₃ t : ℝ) : ℝ :=
  f₀ + d₁ * t + d₂ * t ^ 2 / 2 + d₃ * t ^ 3 / 6

/-- Opposite evaluations cancel the first and third Taylor terms exactly. -/
theorem cubic_symmetric_sum (f₀ d₁ d₂ d₃ t : ℝ) :
    cubic f₀ d₁ d₂ d₃ t + cubic f₀ d₁ d₂ d₃ (-t) =
      2 * f₀ + d₂ * t ^ 2 := by
  unfold cubic
  ring

/-- The symmetric average has only its quadratic term and the averaged
remainders.  Each fourth-order remainder has the usual factor `1/24`. -/
theorem symmetric_average_error (f₀ d₁ d₂ d₃ t fPlus fMinus M : ℝ)
    (hplus : |fPlus - cubic f₀ d₁ d₂ d₃ t| ≤ M * t ^ 4 / 24)
    (hminus : |fMinus - cubic f₀ d₁ d₂ d₃ (-t)| ≤ M * t ^ 4 / 24) :
    |(fPlus + fMinus) / 2 - f₀ - d₂ * t ^ 2 / 2| ≤ M * t ^ 4 / 24 := by
  have hs := cubic_symmetric_sum f₀ d₁ d₂ d₃ t
  rcases abs_le.mp hplus with ⟨hp₁, hp₂⟩
  rcases abs_le.mp hminus with ⟨hm₁, hm₂⟩
  apply abs_le.mpr
  constructor <;> linarith

/-- Absolute value-report errors and Taylor remainders give the centered
second-derivative error.  The four units of report error are `1 + 2 + 1`. -/
theorem centered_second_difference_error (f₀ d₁ d₂ d₃ t fPlus fMinus vPlus v₀ vMinus M ν : ℝ)
    (ht : 0 < t)
    (hplus : |fPlus - cubic f₀ d₁ d₂ d₃ t| ≤ M * t ^ 4 / 24)
    (hminus : |fMinus - cubic f₀ d₁ d₂ d₃ (-t)| ≤ M * t ^ 4 / 24)
    (hvplus : |vPlus - fPlus| ≤ ν) (hvzero : |v₀ - f₀| ≤ ν) (hvminus : |vMinus - fMinus| ≤ ν) :
    |(vPlus - 2 * v₀ + vMinus) / t ^ 2 - d₂| ≤ M * t ^ 2 / 12 + 4 * ν / t ^ 2 := by
  have ht₂ : 0 < t ^ 2 := sq_pos_of_pos ht
  have hs := cubic_symmetric_sum f₀ d₁ d₂ d₃ t
  rcases abs_le.mp hplus with ⟨hp₁, hp₂⟩
  rcases abs_le.mp hminus with ⟨hm₁, hm₂⟩
  rcases abs_le.mp hvplus with ⟨hvp₁, hvp₂⟩
  rcases abs_le.mp hvzero with ⟨hvz₁, hvz₂⟩
  rcases abs_le.mp hvminus with ⟨hvm₁, hvm₂⟩
  have hn : |vPlus - 2 * v₀ + vMinus - d₂ * t ^ 2| ≤ M * t ^ 4 / 12 + 4 * ν := by
    apply abs_le.mpr
    constructor <;> linarith
  have he : (vPlus - 2 * v₀ + vMinus) / t ^ 2 - d₂ =
      (vPlus - 2 * v₀ + vMinus - d₂ * t ^ 2) / t ^ 2 := by
    field_simp
  rw [he, abs_div, abs_of_pos ht₂]
  calc
    _ ≤ (M * t ^ 4 / 12 + 4 * ν) / t ^ 2 := div_le_div_of_nonneg_right hn ht₂.le
    _ = M * t ^ 2 / 12 + 4 * ν / t ^ 2 := by
      field_simp

/-- The perturbation bound for the four-point mixed stencil. -/
theorem mixed_stencil_report_error (aPP aPM aMP aMM vPP vPM vMP vMM t ν : ℝ)
    (ht : 0 < t)
    (hPP : |vPP - aPP| ≤ ν) (hPM : |vPM - aPM| ≤ ν)
    (hMP : |vMP - aMP| ≤ ν) (hMM : |vMM - aMM| ≤ ν) :
    |(vPP - vPM - vMP + vMM) / (4 * t ^ 2) -
      (aPP - aPM - aMP + aMM) / (4 * t ^ 2)| ≤ ν / t ^ 2 := by
  have ht₂ : 0 < t ^ 2 := sq_pos_of_pos ht
  have hd : 0 < 4 * t ^ 2 := by positivity
  rcases abs_le.mp hPP with ⟨hpp₁, hpp₂⟩
  rcases abs_le.mp hPM with ⟨hpm₁, hpm₂⟩
  rcases abs_le.mp hMP with ⟨hmp₁, hmp₂⟩
  rcases abs_le.mp hMM with ⟨hmm₁, hmm₂⟩
  have hn : |(vPP - vPM - vMP + vMM) - (aPP - aPM - aMP + aMM)| ≤ 4 * ν := by
    apply abs_le.mpr
    constructor <;> linarith
  rw [← sub_div, abs_div, abs_of_pos hd]
  calc
    _ ≤ (4 * ν) / (4 * t ^ 2) := div_le_div_of_nonneg_right hn hd.le
    _ = ν / t ^ 2 := by ring

/-- A bivariate cubic, with the ten derivative coefficients of its Taylor
polynomial.  Coefficient `4` is the mixed second derivative. -/
def cubic₂ (c : Fin 10 → ℝ) (x y : ℝ) : ℝ :=
  c 0 + c 1 * x + c 2 * y + c 3 * x ^ 2 / 2 + c 4 * x * y + c 5 * y ^ 2 / 2 +
    c 6 * x ^ 3 / 6 + c 7 * x ^ 2 * y / 2 + c 8 * x * y ^ 2 / 2 + c 9 * y ^ 3 / 6

/-- The mixed four-point stencil cancels every other term of a cubic. -/
theorem cubic₂_mixed_stencil (c : Fin 10 → ℝ) (t : ℝ) (ht : t ≠ 0) :
    (cubic₂ c t t - cubic₂ c t (-t) - cubic₂ c (-t) t + cubic₂ c (-t) (-t)) /
      (4 * t ^ 2) = c 4 := by
  unfold cubic₂
  field_simp
  ring

private theorem report_plus_remainder {v f p ν ρ : ℝ}
    (hv : |v - f| ≤ ν) (hf : |f - p| ≤ ρ) : |v - p| ≤ ν + ρ :=
  (abs_sub_le v f p).trans (add_le_add hv hf)

/-- Mixed-derivative arithmetic accounting.  The remainder bound `M*t^4/6`
is supplied at each point; in a Taylor application it is `M*‖(t,t)‖^4/24`.
No assertion about the existence of those Taylor expansions is implicit. -/
theorem mixed_second_difference_error (c : Fin 10 → ℝ) (t M ν : ℝ)
    (fPP fPM fMP fMM vPP vPM vMP vMM : ℝ) (ht : 0 < t)
    (hfPP : |fPP - cubic₂ c t t| ≤ M * t ^ 4 / 6)
    (hfPM : |fPM - cubic₂ c t (-t)| ≤ M * t ^ 4 / 6)
    (hfMP : |fMP - cubic₂ c (-t) t| ≤ M * t ^ 4 / 6)
    (hfMM : |fMM - cubic₂ c (-t) (-t)| ≤ M * t ^ 4 / 6)
    (hvPP : |vPP - fPP| ≤ ν) (hvPM : |vPM - fPM| ≤ ν)
    (hvMP : |vMP - fMP| ≤ ν) (hvMM : |vMM - fMM| ≤ ν) :
    |(vPP - vPM - vMP + vMM) / (4 * t ^ 2) - c 4| ≤
      M * t ^ 2 / 6 + ν / t ^ 2 := by
  have h := mixed_stencil_report_error
    (cubic₂ c t t) (cubic₂ c t (-t)) (cubic₂ c (-t) t) (cubic₂ c (-t) (-t))
    vPP vPM vMP vMM t (ν + M * t ^ 4 / 6) ht
    (report_plus_remainder hvPP hfPP) (report_plus_remainder hvPM hfPM)
    (report_plus_remainder hvMP hfMP) (report_plus_remainder hvMM hfMM)
  rw [cubic₂_mixed_stencil c t (ne_of_gt ht)] at h
  have he : (ν + M * t ^ 4 / 6) / t ^ 2 = M * t ^ 2 / 6 + ν / t ^ 2 := by
    field_simp
    ring
  rwa [he] at h

end KSFiniteDifference
end MatrixSpencer
