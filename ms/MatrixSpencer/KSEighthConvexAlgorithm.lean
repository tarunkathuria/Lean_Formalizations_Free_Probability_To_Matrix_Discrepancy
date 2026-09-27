import MatrixSpencer.KSEighthConvexAcceptance
import MatrixSpencer.KSEighthManuscriptRetry


open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSEighthConvexAlgorithm
open KSEighthManuscriptRun
variable {N d : ℕ}
set_option maxHeartbeats 1600000

def delta (ε : ℝ) := Real.sqrt ε
def theta (ε : ℝ) (d : ℕ) := ksRegularizerScale ε (Fin d)

theorem delta_pos {ε : ℝ} (hε : 0 < ε) : 0 < delta ε := Real.sqrt_pos.mpr hε

theorem theta_pos {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) : 0 < theta ε d := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  exact ksRegularizerScale_pos hε

def controller (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) : Controller N :=
  KSEighthConvexController.controller O v hN (delta_pos hε) (theta_pos hε hd) hd

def cutoff (v : Fin N → Fin d → ℂ) (ε : ℝ) :=
  KSEighthManuscriptBudgets.cutoff v (delta ε) (theta ε d)

def trial (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) :=
  let C := controller O v hN hε hd
  run C (cutoff v ε) (initialState C)

abbrev Leaves (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) :=
  (trial O v hN hε hd).Leaves

def leafAccepts (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d)
    (l : Leaves O v hN hε hd) : Bool :=
  KSEighthConvexAcceptance.accepts O v (delta ε) (theta ε d) hd (controller O v hN hε hd)
    ((trial O v hN hε hd).leafState l)

def leafSigning (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d)
    (l : Leaves O v hN hε hd) : Fin N → ℝ :=
  KSEighthWalkRun.signing ((trial O v hN hε hd).leafState l)

abbrev Draws (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) (r : ℕ) :=
  KSEighthManuscriptRetry.Draws (Leaves O v hN hε hd) r

def output (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) (r : ℕ)
    (z : Draws O v hN hε hd r) : Option (Fin N → ℝ) :=
  KSEighthManuscriptRetry.firstAccepted (leafSigning O v hN hε hd) (leafAccepts O v hN hε hd) r z

def drawWeight (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) (r : ℕ)
    (z : Draws O v hN hε hd r) : ℝ :=
  KSEighthManuscriptRetry.weight (trial O v hN hε hd).leafWeight r z

theorem drawWeight_nonneg (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (hN : 0 < N) {ε : ℝ} (hε : 0 < ε)
    (hd : 0 < d) (r : ℕ) (z : Draws O v hN hε hd r) : 0 ≤ drawWeight O v hN hε hd r z :=
  KSEighthManuscriptRetry.weight_nonneg _ (fun l => ((trial O v hN hε hd).leafWeight_pos l).le) r z

theorem drawWeight_sum (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (hN : 0 < N) {ε : ℝ} (hε : 0 < ε)
    (hd : 0 < d) (r : ℕ) : (∑z : Draws O v hN hε hd r, drawWeight O v hN hε hd r z) = 1 :=
  KSEighthManuscriptRetry.weight_sum _ (trial O v hN hε hd).leafWeight_sum r

theorem leaf_sound (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (hN : 0 < N) {ε : ℝ} (hε : 0 < ε)
    (hd : 0 < d) (l : Leaves O v hN hε hd) (ha : leafAccepts O v hN hε hd l = true) :
    (∀i, IsSign (leafSigning O v hN hε hd l i)) ∧
      ‖∑i, leafSigning O v hN hε hd l i • KSRankOne.atom (v i)‖ ≤ 512*Real.sqrt ε := by
  apply KSEighthConvexAcceptance.output_sound O v (delta_pos hε) (theta_pos hε hd) hd
    (controller O v hN hε hd) ((trial O v hN hε hd).leafState l) (leafSigning O v hN hε hd l)
  change (if leafAccepts O v hN hε hd l then some (leafSigning O v hN hε hd l) else none) = _
  simp only [ha,↓reduceIte]

/-- Every returned result has all original signs and the manuscript512√ε bound. -/
theorem output_sound (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (hN : 0 < N) {ε : ℝ} (hε : 0 < ε)
    (hd : 0 < d) (r : ℕ) (z : Draws O v hN hε hd r) (σ : Fin N → ℝ)
    (hout : output O v hN hε hd r z = some σ) :
    (∀i, IsSign (σ i)) ∧ ‖∑i, σ i • KSRankOne.atom (v i)‖ ≤ 512*Real.sqrt ε :=
  KSEighthManuscriptRetry.firstAccepted_sound _ _
    (fun σ => (∀i, IsSign (σ i)) ∧ ‖∑i, σ i • KSRankOne.atom (v i)‖ ≤ 512*Real.sqrt ε)
    (leaf_sound O v hN hε hd) r z σ hout

/-- Probability of literal `some` outputs of independent actual LDL walk trials. -/
theorem output_event_probability_ge (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (hN : 0 < N) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hd : 0 < d)
    (hparseval : (∑i, KSRankOne.atom (v i)) = 1)
    (hsize : ∀i, ‖KSRankOne.atom (v i)‖ ≤ ε) (r : ℕ) :
    1-((1 : ℝ)/2)^r ≤ ∑z : Draws O v hN hε hd r, drawWeight O v hN hε hd r z *
      (if (output O v hN hε hd r z).isSome then 1 else 0) := by
  have ht := KSEighthConvexAcceptance.probability_ge_half O v hN hε hε1 hd hparseval hsize
  exact KSEighthManuscriptRetry.successProbability_ge_half (trial O v hN hε hd).leafWeight
    (fun l => ((trial O v hN hε hd).leafWeight_pos l).le) (trial O v hN hε hd).leafWeight_sum
    (leafSigning O v hN hε hd) (leafAccepts O v hN hε hd) ht r

end MatrixSpencer.KSEighthConvexAlgorithm
