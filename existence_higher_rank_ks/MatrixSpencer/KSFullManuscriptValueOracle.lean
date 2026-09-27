import MatrixSpencer.KSFullManuscriptOracleGeometry
import MatrixSpencer.KSFullManuscriptWeakOptimization



open Matrix
open scoped BigOperators InnerProductSpace MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSFullManuscriptValueOracle

open KSFullManuscriptAffineData KSFullManuscriptAffineObjective
open KSFullManuscriptCenterData KSFullManuscriptOracleGeometry
open KSFullManuscriptRegularizationBias
variable {d : ℕ} {ι : Type*} [Fintype ι]

def fallback (a : Fin d) : Space a :=
  unit a ⟨0, Nat.lt_trans Nat.zero_lt_one (dimension_gt_one a)⟩

theorem fallback_ne_zero (a : Fin d) : fallback a ≠ 0 := by
  intro hz
  let i : Fin (dimension a) := ⟨0, Nat.lt_trans Nat.zero_lt_one (dimension_gt_one a)⟩
  have hh := congrArg (fun x : Space a => x i) hz
  change (Pi.single i (1 : ℝ) : Fin (dimension a) → ℝ) i = 0 at hh
  simp only [Pi.single_eq_same, one_ne_zero] at hh

def tolerance (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (B : ι → Matrix (Fin d) (Fin d) ℂ) (θ lam ω : ℝ) : ℝ :=
  min (ω / 4) (L a H θ * R a B lam / 2)

def initialInterval (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (B : ι → Matrix (Fin d) (Fin d) ℂ) (hd : 0 < d) (θ lam : ℝ) : KSFullManuscriptBisection.Interval :=
  ⟨offset H θ (densityCenter hd) (rootCenter hd) - L a H θ * R a B lam,
   offset H θ (densityCenter hd) (rootCenter hd) + L a H θ * R a B lam⟩

/-- The actual finite report for the source-regularized SDP. -/
def regularizedReport (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (B : ι → Matrix (Fin d) (Fin d) ℂ) (hd : 0 < d) (θ lam ω : ℝ) : ℝ :=
  KSFullManuscriptWeakOptimization.report (centerData a B hd lam) (coefficient a H θ)
    (fallback a) (offset H θ (densityCenter hd) (rootCenter hd))
    (R a B lam) (r a B hd lam) (L a H θ) (tolerance a H B θ lam ω) ω
    (initialInterval a H B hd θ lam)

theorem regularizedReport_accuracy (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (B : ι → Matrix (Fin d) (Fin d) ℂ) (hd : 0 < d)
    {θ lam ω : ℝ} (hθ : 0 ≤ θ) (hlam : 0 < lam) (hω : 0 < ω) :
    |regularizedReport a H B hd θ lam ω - KSFullManuscriptRegularizedSDP.potential H B θ lam| ≤ ω := by
  have htr : realTrace (densityCenter hd : Matrix (Fin d) (Fin d) ℂ) = 1 :=
    KSFullManuscriptStrictFeasible.density_trace hd
  obtain ⟨x,hx,hvalue,hmax⟩ := KSFullManuscriptAffineObjective.exists_maximizer a H B
    (densityCenter hd) (rootCenter hd) htr hθ hlam
  have hR := R_pos a B lam
  have hL := L_pos a H θ
  have hτ : 0 < tolerance a H B θ lam ω := by
    apply lt_min <;> positivity
  have hτcap : tolerance a H B θ lam ω ≤ L a H θ * R a B lam := by
    apply (min_le_right _ _).trans
    nlinarith [mul_pos hL hR]
  have hτω : tolerance a H B θ lam ω ≤ ω / 4 := min_le_left _ _
  have hxR : ‖x‖ ≤ R a B lam := by simpa using actual_outer_ball a B hd lam hx
  have hc := coefficient_norm_le a H θ
  have hi : |⟪coefficient a H θ, x⟫_ℝ| ≤ L a H θ * R a B lam :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul hc hxR (norm_nonneg _) hL.le)
  have hinterval : KSFullManuscriptBisection.Contains (initialInterval a H B hd θ lam)
      (offset H θ (densityCenter hd) (rootCenter hd) + ⟪coefficient a H θ, x⟫_ℝ) := by
    exact ⟨by dsimp [KSFullManuscriptBisection.Contains, initialInterval]; linarith [(abs_le.mp hi).1],
      by dsimp [KSFullManuscriptBisection.Contains, initialInterval]; linarith [(abs_le.mp hi).2]⟩
  have hcorrect := KSFullManuscriptWeakOptimization.report_accuracy
    (centerData a B hd lam) (coefficient a H θ) (fallback a) 0 x
    (dimension_gt_one a) (fallback_ne_zero a) hR (r_pos a B hd hlam) hL hτ hτcap
    (r_le_R a B hd lam) hc (actual_outer_ball a B hd lam) (actual_inner_ball a B hd hlam)
    hx hmax hω hτω hinterval
  change |regularizedReport a H B hd θ lam ω -
    (offset H θ (densityCenter hd) (rootCenter hd) + ⟪coefficient a H θ, x⟫_ℝ)| ≤ ω at hcorrect
  rwa [hvalue] at hcorrect

/-- The source regularization and final accuracy split are exactly (O9). -/
def report (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (B : ι → Matrix (Fin d) (Fin d) ℂ) (hd : 0 < d) (θ ν : ℝ) : ℝ :=
  regularizedReport a H B hd θ (regularization d ν) (ν / 2)

/-- Primitive-input value accuracy for the actual full density potential. -/
theorem report_accuracy (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (B : ι → Matrix (Fin d) (Fin d) ℂ) (hd : 0 < d)
    {θ ν : ℝ} (hθ : 0 ≤ θ) (hν : 0 < ν) :
    |report a H B hd θ ν - densityPotential H B θ| ≤ ν := by
  letI : Nonempty (Fin d) := ⟨a⟩
  have hreport := regularizedReport_accuracy a H B hd hθ (regularization_pos hd hν)
    (div_pos hν (by norm_num : (0 : ℝ) < 2))
  have hb := KSFullManuscriptRegularizedSDP.potential_precision H B θ hν
  simp only [Fintype.card_fin] at hb
  change |report a H B hd θ ν - KSFullManuscriptRegularizedSDP.potential H B θ (regularization d ν)| ≤ ν / 2 at hreport
  calc
    |report a H B hd θ ν - densityPotential H B θ| ≤
      |report a H B hd θ ν - KSFullManuscriptRegularizedSDP.potential H B θ (regularization d ν)| +
      |KSFullManuscriptRegularizedSDP.potential H B θ (regularization d ν) - densityPotential H B θ| :=
        abs_sub_le _ _ _
    _ ≤ ν := by linarith

end MatrixSpencer.KSFullManuscriptValueOracle
