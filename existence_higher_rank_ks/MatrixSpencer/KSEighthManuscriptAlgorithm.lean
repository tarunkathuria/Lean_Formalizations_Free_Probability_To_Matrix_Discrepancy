import MatrixSpencer.KSEighthManuscriptAcceptance
import MatrixSpencer.KSEighthManuscriptRetry



open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSEighthManuscriptAlgorithm
open KSEighthManuscriptRun
variable {N d : ℕ}

def delta (ε : ℝ) := Real.sqrt ε
def theta (ε : ℝ) (d : ℕ) := ksRegularizerScale ε (Fin d)

theorem delta_pos {ε : ℝ} (hε : 0 < ε) : 0 < delta ε := Real.sqrt_pos.mpr hε

theorem theta_pos {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) : 0 < theta ε d := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  exact ksRegularizerScale_pos hε

def controller (v : Fin N → Fin d → ℂ) (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) : Controller N :=
  KSEighthManuscriptParameters.controller v hN (delta_pos hε) (theta_pos hε hd) hd

def cutoff (v : Fin N → Fin d → ℂ) (ε : ℝ) :=
  KSEighthManuscriptBudgets.cutoff v (delta ε) (theta ε d)

def trial (v : Fin N → Fin d → ℂ) (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) :=
  let C := controller v hN hε hd
  run C (cutoff v ε) (initialState C)

abbrev Leaves (v : Fin N → Fin d → ℂ) (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) :=
  (trial v hN hε hd).Leaves

def leafAccepts (v : Fin N → Fin d → ℂ) (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d)
    (l : Leaves v hN hε hd) : Bool :=
  KSEighthManuscriptAcceptance.accepts v (delta ε) (theta ε d) hd (controller v hN hε hd)
    ((trial v hN hε hd).leafState l)

def leafSigning (v : Fin N → Fin d → ℂ) (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d)
    (l : Leaves v hN hε hd) : Fin N → ℝ :=
  KSEighthWalkRun.signing ((trial v hN hε hd).leafState l)

abbrev Draws (v : Fin N → Fin d → ℂ) (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) (r : ℕ) :=
  KSEighthManuscriptRetry.Draws (Leaves v hN hε hd) r

def output (v : Fin N → Fin d → ℂ) (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) (r : ℕ)
    (z : Draws v hN hε hd r) : Option (Fin N → ℝ) :=
  KSEighthManuscriptRetry.firstAccepted (leafSigning v hN hε hd) (leafAccepts v hN hε hd) r z

def drawWeight (v : Fin N → Fin d → ℂ) (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) (r : ℕ)
    (z : Draws v hN hε hd r) : ℝ :=
  KSEighthManuscriptRetry.weight (trial v hN hε hd).leafWeight r z

theorem drawWeight_nonneg (v : Fin N → Fin d → ℂ) (hN : 0 < N) {ε : ℝ} (hε : 0 < ε)
    (hd : 0 < d) (r : ℕ) (z : Draws v hN hε hd r) : 0 ≤ drawWeight v hN hε hd r z :=
  KSEighthManuscriptRetry.weight_nonneg _ (fun l => ((trial v hN hε hd).leafWeight_pos l).le) r z

theorem drawWeight_sum (v : Fin N → Fin d → ℂ) (hN : 0 < N) {ε : ℝ} (hε : 0 < ε)
    (hd : 0 < d) (r : ℕ) : (∑z : Draws v hN hε hd r, drawWeight v hN hε hd r z) = 1 :=
  KSEighthManuscriptRetry.weight_sum _ (trial v hN hε hd).leafWeight_sum r

theorem leaf_sound (v : Fin N → Fin d → ℂ) (hN : 0 < N) {ε : ℝ} (hε : 0 < ε)
    (hd : 0 < d) (l : Leaves v hN hε hd) (ha : leafAccepts v hN hε hd l = true) :
    (∀i, IsSign (leafSigning v hN hε hd l i)) ∧
      ‖∑i, leafSigning v hN hε hd l i • KSRankOne.atom (v i)‖ ≤ 512*Real.sqrt ε := by
  apply KSEighthManuscriptAcceptance.output_sound v (delta_pos hε) (theta_pos hε hd) hd
    (controller v hN hε hd) ((trial v hN hε hd).leafState l) (leafSigning v hN hε hd l)
  change (if leafAccepts v hN hε hd l then some (leafSigning v hN hε hd l) else none) = _
  simp only [ha,↓reduceIte]

/-- Every returned result has all original signs and the manuscript512√ε bound. -/
theorem output_sound (v : Fin N → Fin d → ℂ) (hN : 0 < N) {ε : ℝ} (hε : 0 < ε)
    (hd : 0 < d) (r : ℕ) (z : Draws v hN hε hd r) (σ : Fin N → ℝ)
    (hout : output v hN hε hd r z = some σ) :
    (∀i, IsSign (σ i)) ∧ ‖∑i, σ i • KSRankOne.atom (v i)‖ ≤ 512*Real.sqrt ε :=
  KSEighthManuscriptRetry.firstAccepted_sound _ _
    (fun σ => (∀i, IsSign (σ i)) ∧ ‖∑i, σ i • KSRankOne.atom (v i)‖ ≤ 512*Real.sqrt ε)
    (leaf_sound v hN hε hd) r z σ hout

/-- Probability of literal `some` outputs of independent actual LDL walk trials. -/
theorem output_event_probability_ge (v : Fin N → Fin d → ℂ) (hN : 0 < N) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hd : 0 < d)
    (hparseval : (∑i, KSRankOne.atom (v i)) = 1)
    (hsize : ∀i, ‖KSRankOne.atom (v i)‖ ≤ ε) (r : ℕ) :
    1-((1 : ℝ)/2)^r ≤ ∑z : Draws v hN hε hd r, drawWeight v hN hε hd r z *
      (if (output v hN hε hd r z).isSome then 1 else 0) := by
  have ht := KSEighthManuscriptAcceptance.probability_ge_half v hN hε hε1 hd hparseval hsize
  exact KSEighthManuscriptRetry.successProbability_ge_half (trial v hN hε hd).leafWeight
    (fun l => ((trial v hN hε hd).leafWeight_pos l).le) (trial v hN hε hd).leafWeight_sum
    (leafSigning v hN hε hd) (leafAccepts v hN hε hd) ht r

end MatrixSpencer.KSEighthManuscriptAlgorithm
