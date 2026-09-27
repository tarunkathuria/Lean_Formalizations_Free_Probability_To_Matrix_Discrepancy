import HigherRankKSRuntime.StateCharts
import HigherRankKSRuntime.RuntimeStateBounds
import MatrixSpencer.KSFirstDifference

/-! Actual forward value scans imply actual envelope-derivative bounds.
The scalar Taylor remainder is derived here, rather than supplied as a
successful preparation certificate. -/
noncomputable section
open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace HigherRankKSRuntime.PreparationAnalysis
open AugmentedHigherRankKS ActiveEnumeration RuntimeParameters
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

theorem prepareOwner_zero (a : ℝ) (z : EpochState (Fin N)) (i : Fin N) :
    prepareOwner a z i 0 = z := by
  apply Prod.ext
  · rfl
  · apply Prod.ext <;> funext j <;>
      simp [prepareOwner,preparation,position,spent,reserve]

theorem forward_slope_bound (f : ℝ → ℝ) {t M : ℝ} (ht : 0 < t)
    (hf : ContDiffOn ℝ 2 f (Icc 0 t)) (hd : DifferentiableAt ℝ f 0)
    (hM : ∀ u ∈ Ioo 0 t, |iteratedDeriv 2 f u| ≤ M) :
    |(f t-f 0)/t-deriv f 0| ≤ M*t/2 := by
  have hh := KSFirstDifference.positive_remainder f ht hf hd hM
  have he : (f t-f 0)/t-deriv f 0 = (f t-f 0-t*deriv f 0)/t := by
    field_simp
  rw [he,abs_div,abs_of_pos ht]
  calc _ ≤ (M*t^2/2)/t := div_le_div_of_nonneg_right hh ht.le
       _ = M*t/2 := by field_simp

theorem rejected_state_derivatives (p : Dimensions) (hp : p ∈ Domain)
    (query : EpochState (Fin N) → Counted ℝ) (E : EpochState (Fin N) → ℝ)
    {z : EpochState (Fin N)} (hz : z ∈ epochDomain (a p) 4)
    (hc : NextEvent.Clean z (rho p) (zeta p))
    (hquery : ∀ y, (∀ i, 0 ≤ reserve y i) → |(query y).value-E y| ≤ accuracy p)
    (hregular : ∀ i ∈ labels z,
      ContDiffOn ℝ 2 (fun s => E (prepareOwner (a p) z i s)) (Icc 0 (prep p)) ∧
      DifferentiableAt ℝ (fun s => E (prepareOwner (a p) z i s)) 0 ∧
      ∀ s ∈ Ioo 0 (prep p),
        |iteratedDeriv 2 (fun t => E (prepareOwner (a p) z i t)) s| ≤ M p)
    (hreject : NextEvent.Rejected query (a p) (prep p) (p0 p) z) :
    ∀ i ∈ labels z,
      -(p0 p/(2*a p)) < deriv (fun t => E (prepareOwner (a p) z i t)) 0 := by
  have hprep := prep_poly.positive p hp
  have ha := a_poly.positive p hp
  have hzeta := theta_poly.positive p hp
  apply PreparationScan.rejected_actual_derivative
    (fun i => query (prepareOwner (a p) z i (prep p))) (query z).value (E z)
    (fun i => E (prepareOwner (a p) z i (prep p)))
    (fun i => deriv (fun t => E (prepareOwner (a p) z i t)) 0) (labels z)
    hprep ha (p0_poly.positive p hp).le
  · exact hquery z (fun i => (hz i).2.2.2.2.1)
  · intro i hi
    have hci := (hc i ((mem_labels z i).mp hi)).2
    have hfeas := prepareOwner_feasible hz ha i hprep.le
      ((prep_le_zeta p).trans (by linarith))
    exact hquery _ (fun j => (hfeas j).2.2.2.2.1)
  · intro i hi
    obtain ⟨hf,hd,hM⟩ := hregular i hi
    have hh := forward_slope_bound (fun t => E (prepareOwner (a p) z i t)) hprep hf hd hM
    simpa only [prepareOwner_zero] using hh
  · exact accuracy_le_prep p
  · exact prep_product p hp
  · exact hreject

theorem accepted_state_descent (p : Dimensions) (hp : p ∈ Domain)
    (query : EpochState (Fin N) → Counted ℝ) (E : EpochState (Fin N) → ℝ)
    {z : EpochState (Fin N)} (hz : z ∈ epochDomain (a p) 4)
    (hc : NextEvent.Clean z (rho p) (zeta p))
    (hquery : ∀ y, (∀ i, 0 ≤ reserve y i) → |(query y).value-E y| ≤ accuracy p)
    (i : Fin N) (hi : i ∈ labels z)
    (haccept : (query (prepareOwner (a p) z i (prep p))).value-(query z).value ≤
      -(prep p*p0 p/(4*a p))) :
    E (prepareOwner (a p) z i (prep p)) ≤ E z := by
  have ha := a_poly.positive p hp
  have hstep := prep_poly.positive p hp
  have hzeta := theta_poly.positive p hp
  have hci := (hc i ((mem_labels z i).mp hi)).2
  have hfeas := prepareOwner_feasible hz ha i hstep.le
    ((prep_le_zeta p).trans (by linarith))
  have hb := hquery z (fun i => (hz i).2.2.2.2.1)
  have he := hquery _ (fun i => (hfeas i).2.2.2.2.1)
  have hν : accuracy p ≤ (prep p*p0 p/a p)/64 := by
    convert accuracy_le_prep p using 1 <;> ring
  have haccept' : (query (prepareOwner (a p) z i (prep p))).value-(query z).value ≤
      -(prep p*p0 p/a p)/4 := by convert haccept using 1 <;> ring
  have hh := preparation_accepted_descent (reported_difference_error hb he) hν haccept'
  have hp0 := p0_poly.positive p hp
  have hscale : 0 ≤ prep p*p0 p/a p := by positivity
  linarith

theorem rejected_active_derivatives (p : Dimensions) (hp : p ∈ Domain)
    (A : Fin N → Matrix n n ℂ) (β θ : ℝ) (x₀ : Fin N → ℝ)
    (query : EpochState (Fin N) → Counted ℝ)
    {z : EpochState (Fin N)} (hz : z ∈ epochDomain (a p) 4)
    (hc : NextEvent.Clean z (rho p) (zeta p))
    (hquery : ∀ y, (∀ i, 0 ≤ reserve y i) →
      |(query y).value-epochPotential A β θ x₀ y| ≤ accuracy p)
    (hregular : ∀ i ∈ labels z,
      ContDiffOn ℝ 2 (fun s => epochPotential A β θ x₀ (prepareOwner (a p) z i s))
        (Icc 0 (prep p)) ∧
      DifferentiableAt ℝ (fun s => epochPotential A β θ x₀ (prepareOwner (a p) z i s)) 0 ∧
      ∀ s ∈ Ioo 0 (prep p),
        |iteratedDeriv 2 (fun t => epochPotential A β θ x₀ (prepareOwner (a p) z i t)) s| ≤ M p)
    (hreject : NextEvent.Rejected query (a p) (prep p) (p0 p) z) :
    ∀ i, -(p0 p/(2*a p)) < deriv (RuntimeCurvature.prepCurve (center A x₀ z)
      (restrictedAtoms A z) β θ (a p) (restrictedReserve z) i) 0 := by
  intro i
  have hi := (mem_labels z (activeEquiv z i)).mpr (RuntimeStateBounds.active_positive z i)
  have hh := rejected_state_derivatives p hp query (epochPotential A β θ x₀)
    hz hc hquery hregular hreject (activeEquiv z i) hi
  have he : (fun t => epochPotential A β θ x₀ (prepareOwner (a p) z (activeEquiv z i) t)) =
      RuntimeCurvature.prepCurve (center A x₀ z) (restrictedAtoms A z) β θ (a p)
        (restrictedReserve z) i := funext (preparation_chart_eq A β θ x₀ hz i)
  rwa [he] at hh
end HigherRankKSRuntime.PreparationAnalysis
