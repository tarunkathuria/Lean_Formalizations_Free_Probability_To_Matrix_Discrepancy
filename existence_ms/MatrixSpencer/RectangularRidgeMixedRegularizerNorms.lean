import MatrixSpencer.RectangularRidgeMixedRegularizerJets
import MatrixSpencer.RectangularRidgeLineDerivativeBridge
import MatrixSpencer.KSFrobeniusTangent
import MatrixSpencer.KSObjectiveUpper

/-!
# Genuine mixed-regularizer Fréchet norms in physical and density coordinates

The inputs are only explicit positive-density floors and scalar parameter
bounds. The actual second, third and fourth derivatives are controlled by
proved line jets and proved polarization. Contractive affine coordinates
preserve the same budget, including the trace-zero Frobenius chart.
-/
open Matrix Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.RectangularRidgeMixedRegularizerNorms
open RectangularRidgeActualRootJets RectangularRidgeMixedRegularizerJets
open RectangularRidgeDerivativePolarization
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local instance ridgeMixedRegularizerNormsCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance ridgeMixedRegularizerNormsRealSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance ridgeMixedRegularizerNormsTwo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance ridgeMixedRegularizerNormsTwoSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance ridgeMixedRegularizerNormsThree {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance ridgeMixedRegularizerNormsThreeSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance ridgeMixedRegularizerNormsFour {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance ridgeMixedRegularizerNormsCoordinatesGroup : NormedAddCommGroup (KSFrobeniusTangent.Coordinates n) := inferInstance
local instance ridgeMixedRegularizerNormsCoordinatesSpace : NormedSpace ℝ (KSFrobeniusTangent.Coordinates n) := inferInstance
local instance ridgeMixedRegularizerNormsJointGroup : NormedAddCommGroup (ℝ × KSFrobeniusTangent.Coordinates n) := inferInstance
local instance ridgeMixedRegularizerNormsJointSpace : NormedSpace ℝ (ℝ × KSFrobeniusTangent.Coordinates n) := inferInstance

/-- A common full derivative budget, including polarization. -/
def budget (m : ℕ) (θ κ μ : ℝ) : ℝ :=
  256 * (2 * (θ + κ) * (Fintype.card n : ℝ) * ((2 ^ m : ℝ) ^ 4 * (120 / μ) ^ 4))

omit [DecidableEq n] in
lemma budget_nonneg (m : ℕ) {θ κ μ : ℝ} (hθ : 0 ≤ θ) (hκ : 0 ≤ κ) :
    0 ≤ budget (n := n) m θ κ μ := by unfold budget; positivity

/-- The full actual second, third and fourth derivative norms at a positive density. -/
theorem physical_norm_bounds (m : ℕ) (hm : 1 ≤ m) {θ κ : ℝ} (hθ : 0 ≤ θ) (hκ : 0 ≤ κ)
    (S : Herm (n := n)) (hS : (S : Matrix n n ℂ).PosDef) (hS1 : (S : Matrix n n ℂ) ≤ 1)
    {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hfloor : μ • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ)) :
    ‖second (regularizer m θ κ) S‖ ≤ budget (n := n) m θ κ μ ∧
    ‖third (regularizer m θ κ) S‖ ≤ budget (n := n) m θ κ μ ∧
    ‖fourth (regularizer m θ κ) S‖ ≤ budget (n := n) m θ κ μ := by
  let C := 2 * (θ + κ) * (Fintype.card n : ℝ) * ((2 ^ m : ℝ) ^ 4 * (120 / μ) ^ 4)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hc := (contDiffAt_regularizer m θ κ S hS).of_le
    (WithTop.coe_le_coe.mpr (show (4 : ℕ∞) ≤ ⊤ from le_top))
  have hl (r : ℕ) (hr1 : 1 ≤ r) (hr4 : r ≤ 4) : ∀ X, ‖X‖ ≤ 1 →
      |iteratedDeriv r (fun t : ℝ => regularizer m θ κ (S + t • X)) 0| ≤ C := by
    intro X hX
    exact regularizer_jet_abs_le m hm hθ hκ S X hS hS1 hμ hμ1 hfloor hX r hr1 hr4
  have h2 := RectangularRidgeLineDerivativeBridge.second_norm_le_unit hc hC (hl 2 (by omega) (by omega))
  have h3 := RectangularRidgeLineDerivativeBridge.third_norm_le_unit hc hC (hl 3 (by omega) (by omega))
  have h4 := RectangularRidgeLineDerivativeBridge.fourth_norm_le_unit hc hC (hl 4 (by omega) (by omega))
  change _ ≤ 256 * C ∧ _ ≤ 256 * C ∧ _ ≤ 256 * C
  exact ⟨h2.trans (by nlinarith), h3.trans (by nlinarith), h4⟩

section Affine
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Contractive affine coordinates preserve the explicit actual derivative budget. -/
theorem affine_norm_bounds (L : E →L[ℝ] Herm (n := n)) (hL : ∀ u, ‖L u‖ ≤ ‖u‖)
    (S₀ : Herm (n := n)) (x : E) (m : ℕ) (hm : 1 ≤ m)
    {θ κ : ℝ} (hθ : 0 ≤ θ) (hκ : 0 ≤ κ)
    (hS : ((S₀ + L x : Herm (n := n)) : Matrix n n ℂ).PosDef)
    (hS1 : ((S₀ + L x : Herm (n := n)) : Matrix n n ℂ) ≤ 1)
    {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hfloor : μ • (1 : Matrix n n ℂ) ≤ ((S₀ + L x : Herm (n := n)) : Matrix n n ℂ)) :
    let F := fun y => regularizer m θ κ (S₀ + L y)
    ‖second F x‖ ≤ budget (n := n) m θ κ μ ∧
    ‖third F x‖ ≤ budget (n := n) m θ κ μ ∧
    ‖fourth F x‖ ≤ budget (n := n) m θ κ μ := by
  dsimp only
  let C := 2 * (θ + κ) * (Fintype.card n : ℝ) * ((2 ^ m : ℝ) ^ 4 * (120 / μ) ^ 4)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have ha : ContDiff ℝ ∞ (fun y => S₀ + L y) := contDiff_const.add L.contDiff
  have hc := ((contDiffAt_regularizer m θ κ (S₀ + L x) hS).comp x ha.contDiffAt).of_le
    (WithTop.coe_le_coe.mpr (show (4 : ℕ∞) ≤ ⊤ from le_top))
  have hl (r : ℕ) (hr1 : 1 ≤ r) (hr4 : r ≤ 4) : ∀ u, ‖u‖ ≤ 1 →
      |iteratedDeriv r (fun t : ℝ => regularizer m θ κ (S₀ + L (x + t • u))) 0| ≤ C := by
    intro u hu
    have he : (fun t : ℝ => regularizer m θ κ (S₀ + L (x + t • u))) =
        (fun t : ℝ => regularizer m θ κ (line (S₀ + L x) (L u) t)) := by
      funext t
      congr 1
      simp only [map_add, map_smul, line, add_assoc]
    rw [he]
    exact regularizer_jet_abs_le m hm hθ hκ (S₀ + L x) (L u) hS hS1 hμ hμ1 hfloor
      ((hL u).trans hu) r hr1 hr4
  have h2 := RectangularRidgeLineDerivativeBridge.second_norm_le_unit hc hC (hl 2 (by omega) (by omega))
  have h3 := RectangularRidgeLineDerivativeBridge.third_norm_le_unit hc hC (hl 3 (by omega) (by omega))
  have h4 := RectangularRidgeLineDerivativeBridge.fourth_norm_le_unit hc hC (hl 4 (by omega) (by omega))
  change _ ≤ 256 * C ∧ _ ≤ 256 * C ∧ _ ≤ 256 * C
  exact ⟨h2.trans (by nlinarith), h3.trans (by nlinarith), h4⟩
end Affine

omit [Nonempty n] in
/-- Frobenius trace-zero coordinates are contractive in physical operator norm. -/
lemma embedding_norm_le (u : KSFrobeniusTangent.Coordinates n) :
    ‖KSFrobeniusTangent.embedding n u‖ ≤ ‖u‖ := by
  have h := KSObjectiveUpper.norm_sq_le_trace_square (KSFrobeniusTangent.embedding n u).property
  rw [KSFrobeniusTangent.embedding_trace_square] at h
  change ‖KSFrobeniusTangent.embedding n u‖ ^ 2 ≤ ‖u‖ ^ 2 at h
  nlinarith [norm_nonneg (KSFrobeniusTangent.embedding n u), norm_nonneg u]

/-- The actual regularizer in the full trace-zero Frobenius density chart. -/
theorem chart_norm_bounds (m : ℕ) (hm : 1 ≤ m) {θ κ : ℝ} (hθ : 0 ≤ θ) (hκ : 0 ≤ κ)
    (x : KSFrobeniusTangent.Coordinates n)
    (hS : (KSFrobeniusTangent.chart n x : Matrix n n ℂ).PosDef)
    (hS1 : (KSFrobeniusTangent.chart n x : Matrix n n ℂ) ≤ 1)
    {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hfloor : μ • (1 : Matrix n n ℂ) ≤ (KSFrobeniusTangent.chart n x : Matrix n n ℂ)) :
    let F := fun y => regularizer m θ κ (KSFrobeniusTangent.chart n y)
    ‖second F x‖ ≤ budget (n := n) m θ κ μ ∧
    ‖third F x‖ ≤ budget (n := n) m θ κ μ ∧
    ‖fourth F x‖ ≤ budget (n := n) m θ κ μ :=
  affine_norm_bounds (KSFrobeniusTangent.embedding n) embedding_norm_le
    (KSFrobeniusTangent.center n) x m hm hθ hκ hS hS1 hμ hμ1 hfloor

/-- Adding the real walk parameter keeps the usual product maximum norm. -/
theorem joint_chart_norm_bounds (m : ℕ) (hm : 1 ≤ m) {θ κ : ℝ} (hθ : 0 ≤ θ) (hκ : 0 ≤ κ)
    (x : ℝ × KSFrobeniusTangent.Coordinates n)
    (hS : (KSFrobeniusTangent.chart n x.2 : Matrix n n ℂ).PosDef)
    (hS1 : (KSFrobeniusTangent.chart n x.2 : Matrix n n ℂ) ≤ 1)
    {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hfloor : μ • (1 : Matrix n n ℂ) ≤ (KSFrobeniusTangent.chart n x.2 : Matrix n n ℂ)) :
    let F := fun y : ℝ × KSFrobeniusTangent.Coordinates n =>
      regularizer m θ κ (KSFrobeniusTangent.chart n y.2)
    ‖second F x‖ ≤ budget (n := n) m θ κ μ ∧
    ‖third F x‖ ≤ budget (n := n) m θ κ μ ∧
    ‖fourth F x‖ ≤ budget (n := n) m θ κ μ := by
  let L := (KSFrobeniusTangent.embedding n).comp
    (ContinuousLinearMap.snd ℝ ℝ (KSFrobeniusTangent.Coordinates n))
  have hL (u : ℝ × KSFrobeniusTangent.Coordinates n) : ‖L u‖ ≤ ‖u‖ :=
    (embedding_norm_le u.2).trans (norm_snd_le u)
  exact affine_norm_bounds L hL (KSFrobeniusTangent.center n) x m hm hθ hκ hS hS1 hμ hμ1 hfloor

end MatrixSpencer.RectangularRidgeMixedRegularizerNorms
