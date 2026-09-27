import MatrixSpencer.KSControllerParameters

/-!
# A conservative Taylor budget compatible with the analytic curve interval

Once a true joint derivative cap B is supplied, the envelope formula gives
an outer cap. Enlarging it by an explicit scalar term also puts the actual
movement inside the same radius δ/16 used by the Hessian queries. The
analytic assertion that B bounds the KS objective is a separate obligation.
-/

noncomputable section
namespace MatrixSpencer.KSTaylorBudget

open KSControllerParameters

def envelopeCap (B θ : ℝ) : ℝ :=
  (B + 3 * B ^ 2 / (θ / 2)) * (1 + B / (θ / 2)) ^ 4

def budget (N : ℕ) (δ θ B : ℝ) : ℝ :=
  max (envelopeCap B θ) (256 * curvatureTolerance N δ / δ ^ 2) + 1

theorem envelopeCap_nonneg {B θ : ℝ} (hB : 0 ≤ B) (hθ : 0 < θ) :
    0 ≤ envelopeCap B θ := by unfold envelopeCap; positivity

theorem budget_pos (N : ℕ) {δ θ B : ℝ} (hB : 0 ≤ B) (hθ : 0 < θ) :
    0 < budget N δ θ B := by
  have h := (envelopeCap_nonneg hB hθ).trans
    (le_max_left (envelopeCap B θ) (256 * curvatureTolerance N δ / δ ^ 2))
  unfold budget
  linarith

theorem envelopeCap_le_budget (N : ℕ) (δ θ B : ℝ) :
    envelopeCap B θ ≤ budget N δ θ B := by
  have h := le_max_left (envelopeCap B θ) (256 * curvatureTolerance N δ / δ ^ 2)
  unfold budget
  linarith

/-- This arithmetic condition ensures the pre-existing numerical controller
uses movements no longer than its legal Hessian-query radius. -/
theorem movementStep_le_hessianRadius_of_budget (N : ℕ) {δ M : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M)
    (hcap : 256 * curvatureTolerance N δ / δ ^ 2 ≤ M) :
    movementStep N δ M ≤ hessianRadius δ := by
  have hd : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hden : 0 < M + 1 := by linarith
  have hcap' := (div_le_iff₀ hd).mp hcap
  have hsq : curvatureTolerance N δ / (M + 1) ≤ (δ / 16) ^ 2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [sq_nonneg δ]
  have hs : Real.sqrt (curvatureTolerance N δ / (M + 1)) ≤ δ / 16 :=
    (Real.sqrt_le_iff).mpr ⟨by positivity, hsq⟩
  exact (min_le_right _ _).trans hs

theorem movementStep_le_hessianRadius (N : ℕ) {δ θ B : ℝ}
    (hδ : 0 < δ) (hB : 0 ≤ B) (hθ : 0 < θ) :
    movementStep N δ (budget N δ θ B) ≤ hessianRadius δ := by
  apply movementStep_le_hessianRadius_of_budget N hδ (budget_pos N hB hθ).le
  have h := le_max_right (envelopeCap B θ) (256 * curvatureTolerance N δ / δ ^ 2)
  unfold budget
  linarith

end MatrixSpencer.KSTaylorBudget
