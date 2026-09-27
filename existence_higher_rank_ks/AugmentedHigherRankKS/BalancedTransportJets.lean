import MatrixSpencer.TransportDerivative
import MatrixSpencer.KSArbitraryTransportContact
import MatrixSpencer.GeneralizedSylvester
import AugmentedHigherRankKS.BalancedFidelityRegularity
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Actual Taylor coefficients of the smooth transport optimizer. -/
open Matrix MatrixSpencer Filter
open scoped BigOperators Topology ContDiff MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace AugmentedHigherRankKS.BalancedTransportJets
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance jetsCStar : CStarAlgebra (Matrix n n ℂ) := {}

private theorem contDiffAt_deriv {f : ℝ → Matrix n n ℂ} {x : ℝ}
    {m k : WithTop ℕ∞} (hf : ContDiffAt ℝ k f x) (hm : m + 1 ≤ k) :
    ContDiffAt ℝ m (deriv f) x := by
  have h := (hf.fderiv_right hm).clm_apply (g := fun _ => (1 : ℝ)) contDiffAt_const
  simpa only [fderiv_deriv] using h

private theorem eventually_deriv_mul {f g : ℝ → Matrix n n ℂ} {x : ℝ}
    (hf : ContDiffAt ℝ 1 f x) (hg : ContDiffAt ℝ 1 g x) :
    deriv (fun t => f t * g t) =ᶠ[𝓝 x]
      (fun t => deriv f t * g t + f t * deriv g t) := by
  filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with t hft hgt
  rw [deriv_fun_mul (hft.differentiableAt (by norm_num)) (hgt.differentiableAt (by norm_num))]

/-- The ordinary second product derivative, retaining matrix order. -/
theorem deriv2_mul {f g : ℝ → Matrix n n ℂ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    deriv (deriv (fun t => f t * g t)) x =
      deriv (deriv f) x * g x + deriv f x * deriv g x +
        deriv f x * deriv g x + f x * deriv (deriv g) x := by
  have hf0 := hf.differentiableAt (by norm_num)
  have hg0 := hg.differentiableAt (by norm_num)
  have hf1 := (contDiffAt_deriv hf (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiableAt
    (by norm_num)
  have hg1 := (contDiffAt_deriv hg (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiableAt
    (by norm_num)
  rw [(eventually_deriv_mul (hf.of_le (by norm_num)) (hg.of_le (by norm_num))).deriv_eq]
  have hd := ((hf1.hasDerivAt.mul hg0.hasDerivAt).add
    (hf0.hasDerivAt.mul hg1.hasDerivAt)).deriv
  change deriv (deriv f * g + f * deriv g) x = _
  rw [hd]
  abel

/-- The third product derivative, retaining all six ordered mixed terms. -/
theorem deriv3_mul {f g : ℝ → Matrix n n ℂ} {x : ℝ}
    (hf : ContDiffAt ℝ 3 f x) (hg : ContDiffAt ℝ 3 g x) :
    deriv (deriv (deriv (fun t => f t * g t))) x =
      deriv (deriv (deriv f)) x * g x +
      (3 : ℝ) • (deriv (deriv f) x * deriv g x) +
      (3 : ℝ) • (deriv f x * deriv (deriv g) x) +
      f x * deriv (deriv (deriv g)) x := by
  have hf0 := hf.differentiableAt (by norm_num)
  have hg0 := hg.differentiableAt (by norm_num)
  have hf' : ContDiffAt ℝ 2 (deriv f) x := contDiffAt_deriv hf (by norm_num)
  have hg' : ContDiffAt ℝ 2 (deriv g) x := contDiffAt_deriv hg (by norm_num)
  have hf1 := hf'.differentiableAt (by norm_num)
  have hg1 := hg'.differentiableAt (by norm_num)
  have hf2 := (contDiffAt_deriv hf' (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiableAt
    (by norm_num)
  have hg2 := (contDiffAt_deriv hg' (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiableAt
    (by norm_num)
  have he : deriv (deriv (fun t => f t * g t)) =ᶠ[𝓝 x]
      (fun t => deriv (deriv f) t * g t + deriv f t * deriv g t +
        deriv f t * deriv g t + f t * deriv (deriv g) t) := by
    filter_upwards [(hf.of_le (show (2 : WithTop ℕ∞) ≤ 3 by norm_num)).eventually (by norm_num),
      (hg.of_le (show (2 : WithTop ℕ∞) ≤ 3 by norm_num)).eventually (by norm_num)] with t hft hgt
    exact deriv2_mul hft hgt
  rw [he.deriv_eq]
  have hd := ((((hf2.hasDerivAt.mul hg0.hasDerivAt).add
    (hf1.hasDerivAt.mul hg1.hasDerivAt)).add
    (hf1.hasDerivAt.mul hg1.hasDerivAt)).add
    (hf0.hasDerivAt.mul hg2.hasDerivAt)).deriv
  change deriv (deriv (deriv f) * g + deriv f * deriv g +
    deriv f * deriv g + f * deriv (deriv g)) x = _
  rw [hd]
  module

/-- Taylor coefficients are normalized actual iterated derivatives. -/
def jet (f : ℝ → Matrix n n ℂ) (j : ℕ) : Matrix n n ℂ :=
  ((j.factorial : ℝ)⁻¹) • iteratedDeriv j f 0

@[simp] theorem jet_zero (f : ℝ → Matrix n n ℂ) : jet f 0 = f 0 := by
  simp [jet]
@[simp] theorem jet_one (f : ℝ → Matrix n n ℂ) : jet f 1 = deriv f 0 := by
  simp [jet, iteratedDeriv_one]
@[simp] theorem jet_two (f : ℝ → Matrix n n ℂ) :
    jet f 2 = (1 / 2 : ℝ) • deriv (deriv f) 0 := by
  norm_num [jet, iteratedDeriv_succ, iteratedDeriv_one, Nat.factorial]
@[simp] theorem jet_three (f : ℝ → Matrix n n ℂ) :
    jet f 3 = (1 / 6 : ℝ) • deriv (deriv (deriv f)) 0 := by
  norm_num [jet, iteratedDeriv_succ, iteratedDeriv_one, Nat.factorial]

/-- First normalized product coefficient. -/
theorem jet_mul_one {f g : ℝ → Matrix n n ℂ}
    (hf : ContDiffAt ℝ 3 f 0) (hg : ContDiffAt ℝ 3 g 0) :
    jet (fun t => f t * g t) 1 = jet f 1 * jet g 0 + jet f 0 * jet g 1 := by
  simp only [jet_zero, jet_one]
  exact deriv_fun_mul (hf.differentiableAt (by norm_num))
    (hg.differentiableAt (by norm_num))

/-- Second normalized product coefficient. -/
theorem jet_mul_two {f g : ℝ → Matrix n n ℂ}
    (hf : ContDiffAt ℝ 3 f 0) (hg : ContDiffAt ℝ 3 g 0) :
    jet (fun t => f t * g t) 2 =
      jet f 2 * jet g 0 + jet f 1 * jet g 1 + jet f 0 * jet g 2 := by
  simp only [jet_zero, jet_one, jet_two]
  rw [deriv2_mul (hf.of_le (by norm_num)) (hg.of_le (by norm_num))]
  simp only [Matrix.smul_mul, Matrix.mul_smul]
  module

/-- Third normalized product coefficient. -/
theorem jet_mul_three {f g : ℝ → Matrix n n ℂ}
    (hf : ContDiffAt ℝ 3 f 0) (hg : ContDiffAt ℝ 3 g 0) :
    jet (fun t => f t * g t) 3 =
      jet f 3 * jet g 0 + jet f 2 * jet g 1 +
        jet f 1 * jet g 2 + jet f 0 * jet g 3 := by
  simp only [jet_zero, jet_one, jet_two, jet_three]
  rw [deriv3_mul hf hg]
  simp only [Matrix.smul_mul, Matrix.mul_smul]
  module

/-- Equal germs have the same actual Taylor coefficients. -/
theorem jet_congr {f g : ℝ → Matrix n n ℂ} (he : f =ᶠ[𝓝 0] g) (j : ℕ) :
    jet f j = jet g j := by
  unfold jet
  rw [he.iteratedDeriv_eq]

/-- The transport optimizer at a balanced pair is the identity. -/
theorem transportOptimizer_self {P : Matrix n n ℂ} (hP : P.PosDef) :
    transportOptimizer P P = 1 := by
  exact (KSArbitraryTransportContact.transport_unique hP hP (Matrix.PosDef.one) (by simp)).symm

/-- Coefficient equations extracted from a genuine local transport identity. -/
theorem transport_jet_equations {A B R : ℝ → Matrix n n ℂ} {P : Matrix n n ℂ}
    (hB : ContDiffAt ℝ 3 B 0) (hR : ContDiffAt ℝ 3 R 0)
    (hB0 : B 0 = P) (hR0 : R 0 = 1)
    (he : (fun t => R t * B t * R t) =ᶠ[𝓝 0] A) :
    sylvester P (jet R 1) = jet A 1 - jet B 1 ∧
    sylvester P (jet R 2) = jet A 2 - jet B 2 -
      jet R 1 * jet B 1 - jet B 1 * jet R 1 - jet R 1 * P * jet R 1 ∧
    sylvester P (jet R 3) = jet A 3 - jet B 3 -
      jet R 1 * jet B 2 - jet B 2 * jet R 1 -
      jet R 2 * jet B 1 - jet B 1 * jet R 2 -
      jet R 1 * jet B 1 * jet R 1 -
      jet R 1 * P * jet R 2 - jet R 2 * P * jet R 1 := by
  have h1 := jet_congr he 1
  have h2 := jet_congr he 2
  have h3 := jet_congr he 3
  rw [jet_mul_one (hR.mul hB) hR, jet_mul_one hR hB] at h1
  rw [jet_mul_two (hR.mul hB) hR, jet_mul_one hR hB, jet_mul_two hR hB] at h2
  rw [jet_mul_three (hR.mul hB) hR, jet_mul_one hR hB,
    jet_mul_two hR hB, jet_mul_three hR hB] at h3
  simp only [jet_zero, hB0, hR0, Matrix.one_mul, Matrix.mul_one] at h1 h2 h3
  simp only [sylvester_apply]
  constructor
  · rw [← h1]; noncomm_ring
  constructor
  · rw [← h2]; noncomm_ring
  · rw [← h3]; noncomm_ring

/-- The two faithful self-adjoint input curves determine an actual smooth
transport curve, rather than a formal solution of the transport equation. -/
def transportCurve (A B : ℝ → selfAdjoint (Matrix n n ℂ)) (t : ℝ) : Matrix n n ℂ :=
  transportOptimizer (A t) (B t)

theorem contDiffAt_transportCurve {A B : ℝ → selfAdjoint (Matrix n n ℂ)}
    (hA : ContDiffAt ℝ 3 A 0) (hB : ContDiffAt ℝ 3 B 0)
    (hA0 : (A 0 : Matrix n n ℂ).PosDef) (hB0 : (B 0 : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ 3 (transportCurve A B) 0 := by
  exact ((contDiffAt_jointTransportOptimizer (A 0) (B 0) hA0 hB0).of_le
    (WithTop.coe_le_coe.mpr (show (3 : ℕ∞) ≤ ⊤ from le_top))).comp 0 (hA.prodMk hB)

theorem actual_transport_jet_equations {A B : ℝ → selfAdjoint (Matrix n n ℂ)}
    {P : Matrix n n ℂ} (hP : P.PosDef)
    (hA : ContDiffAt ℝ 3 A 0) (hB : ContDiffAt ℝ 3 B 0)
    (hA0 : (A 0 : Matrix n n ℂ) = P) (hB0 : (B 0 : Matrix n n ℂ) = P) :
    let a := fun t => (A t : Matrix n n ℂ)
    let b := fun t => (B t : Matrix n n ℂ)
    let R := transportCurve A B
    sylvester P (jet R 1) = jet a 1 - jet b 1 ∧
    sylvester P (jet R 2) = jet a 2 - jet b 2 -
      jet R 1 * jet b 1 - jet b 1 * jet R 1 - jet R 1 * P * jet R 1 ∧
    sylvester P (jet R 3) = jet a 3 - jet b 3 -
      jet R 1 * jet b 2 - jet b 2 * jet R 1 -
      jet R 2 * jet b 1 - jet b 1 * jet R 2 -
      jet R 1 * jet b 1 * jet R 1 -
      jet R 1 * P * jet R 2 - jet R 2 * P * jet R 1 := by
  have hAP : (A 0 : Matrix n n ℂ).PosDef := hA0.symm ▸ hP
  have hBP : (B 0 : Matrix n n ℂ).PosDef := hB0.symm ▸ hP
  apply transport_jet_equations
    ((hermitianInclusion (n := n)).contDiff.contDiffAt.comp 0 hB)
    (contDiffAt_transportCurve hA hB hAP hBP) hB0
  · simp only [transportCurve, hA0, hB0, transportOptimizer_self hP]
  · have ha := hA.continuousAt.eventually (eventually_posDef_of_posDef (A 0) hAP)
    have hb := hB.continuousAt.eventually (eventually_posDef_of_posDef (B 0) hBP)
    filter_upwards [ha, hb] with t hat hbt
    exact transportOptimizer_solve hat hbt

/-- A continuous linear map commutes with the actual iterated derivative. -/
theorem iteratedDeriv_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F)
    {f : ℝ → E} (hf : ContDiffAt ℝ 3 f 0) {j : ℕ}
    (hj : (j : WithTop ℕ∞) ≤ 3) :
    iteratedDeriv j (fun t => L (f t)) 0 = L (iteratedDeriv j f 0) := by
  change iteratedFDeriv ℝ j (L ∘ f) 0 (fun _ => 1) = _
  rw [L.iteratedFDeriv_comp_left hf hj]
  rfl

/-- Scalar Taylor coefficients, normalized by the factorial. -/
def scalarJet (f : ℝ → ℝ) (j : ℕ) : ℝ :=
  ((j.factorial : ℝ)⁻¹) * iteratedDeriv j f 0

theorem scalarJet_trace {f : ℝ → Matrix n n ℂ}
    (hf : ContDiffAt ℝ 3 f 0) {j : ℕ} (hj : (j : WithTop ℕ∞) ≤ 3) :
    scalarJet (fun t => 2 * realTrace (f t)) j = 2 * realTrace (jet f j) := by
  have hh := iteratedDeriv_clm ((2 : ℝ) • realTraceCLM (n := n)) hf hj
  change iteratedDeriv j (fun t => 2 * realTrace (f t)) 0 =
    2 * realTrace (iteratedDeriv j f 0) at hh
  rw [scalarJet, hh, jet, realTrace_smul]
  ring

theorem transport_jet_isHermitian {A B : ℝ → selfAdjoint (Matrix n n ℂ)}
    (hA : ContDiffAt ℝ 3 A 0) (hB : ContDiffAt ℝ 3 B 0)
    (hA0 : (A 0 : Matrix n n ℂ).PosDef) (hB0 : (B 0 : Matrix n n ℂ).PosDef)
    {j : ℕ} (hj : (j : WithTop ℕ∞) ≤ 3) :
    (jet (transportCurve A B) j).IsHermitian := by
  let R : ℝ → selfAdjoint (Matrix n n ℂ) := fun t => jointHermitianTransport (A t, B t)
  have hc : ContDiffAt ℝ 3 (jointHermitianTransport (n := n)) (A 0, B 0) :=
    (contDiffAt_jointHermitianTransport (A 0) (B 0) hA0 hB0).of_le
      (WithTop.coe_le_coe.mpr (show (3 : ℕ∞) ≤ ⊤ from le_top))
  have hR : ContDiffAt ℝ 3 R 0 := by
    simpa only [Function.comp_def, R] using hc.comp 0 (hA.prodMk hB)
  have hh := iteratedDeriv_clm (hermitianInclusion (n := n)) hR hj
  change iteratedDeriv j (transportCurve A B) 0 =
    ((iteratedDeriv j R (0 : ℝ) : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) at hh
  unfold jet
  rw [hh]
  exact (IsSelfAdjoint.all ((j.factorial : ℝ)⁻¹)).smul
    ((iteratedDeriv j R (0 : ℝ)).property)

/-- The actual scalar fidelity coefficients at a balanced faithful pair. -/
theorem actual_fidelity_jet_equations {A B : ℝ → selfAdjoint (Matrix n n ℂ)}
    {P : Matrix n n ℂ} (hP : P.PosDef)
    (hA : ContDiffAt ℝ 3 A 0) (hB : ContDiffAt ℝ 3 B 0)
    (hA0 : (A 0 : Matrix n n ℂ) = P) (hB0 : (B 0 : Matrix n n ℂ) = P) :
    let b := fun t => (B t : Matrix n n ℂ)
    let R := transportCurve A B
    let F := fun t => 2 * fidelity (A t : Matrix n n ℂ) (B t : Matrix n n ℂ)
    scalarJet F 1 = 2 * realTrace (jet b 1 + P * jet R 1) ∧
    scalarJet F 2 = 2 * realTrace (jet b 2 + jet b 1 * jet R 1 + P * jet R 2) ∧
    scalarJet F 3 = 2 * realTrace
      (jet b 3 + jet b 2 * jet R 1 + jet b 1 * jet R 2 + P * jet R 3) := by
  have hAP : (A 0 : Matrix n n ℂ).PosDef := hA0.symm ▸ hP
  have hBP : (B 0 : Matrix n n ℂ).PosDef := hB0.symm ▸ hP
  let R := transportCurve A B
  let b := fun t => (B t : Matrix n n ℂ)
  have hb : ContDiffAt ℝ 3 b 0 :=
    (hermitianInclusion (n := n)).contDiff.contDiffAt.comp 0 hB
  have hr : ContDiffAt ℝ 3 R 0 := contDiffAt_transportCurve hA hB hAP hBP
  have hr0 : R 0 = 1 := by simp only [R, transportCurve, hA0, hB0, transportOptimizer_self hP]
  have he : (fun t => 2 * fidelity (A t : Matrix n n ℂ) (B t : Matrix n n ℂ)) =ᶠ[𝓝 0]
      (fun t => 2 * realTrace (b t * R t)) := by
    have ha := hA.continuousAt.eventually (eventually_posDef_of_posDef (A 0) hAP)
    have hb' := hB.continuousAt.eventually (eventually_posDef_of_posDef (B 0) hBP)
    filter_upwards [ha, hb'] with t hat hbt
    rw [← trace_transportOptimizer_eq_fidelity hat hbt]
    rfl
  have hjet (j : ℕ) (hj : (j : WithTop ℕ∞) ≤ 3) :
      scalarJet (fun t => 2 * fidelity (A t : Matrix n n ℂ) (B t : Matrix n n ℂ)) j =
        2 * realTrace (jet (fun t => b t * R t) j) := by
    rw [scalarJet, he.iteratedDeriv_eq]
    exact scalarJet_trace (hb.mul hr) hj
  dsimp only
  constructor
  · rw [hjet 1 (by norm_num), jet_mul_one hb hr]
    simp only [jet_zero, hr0, Matrix.mul_one, b, hB0, R]
  constructor
  · rw [hjet 2 (by norm_num), jet_mul_two hb hr]
    simp only [jet_zero, hr0, Matrix.mul_one, b, hB0, R]
  · rw [hjet 3 (by norm_num), jet_mul_three hb hr]
    simp only [jet_zero, hr0, Matrix.mul_one, b, hB0, R]

/-- A quantitative estimate for the actual fidelity coefficients. Its assumptions
are bounds on the two input curves, not on an implicitly chosen transport. -/
theorem actual_fidelity_jet_bounds {A B : ℝ → selfAdjoint (Matrix n n ℂ)}
    {P : Matrix n n ℂ} (hP : P.PosDef)
    (hA : ContDiffAt ℝ 3 A 0) (hB : ContDiffAt ℝ 3 B 0)
    (hA0 : (A 0 : Matrix n n ℂ) = P) (hB0 : (B 0 : Matrix n n ℂ) = P)
    {d L : ℝ} (hd : 1 ≤ d) (hL : 0 ≤ L)
    (hAj : ∀ j : ℕ, 1 ≤ j → j ≤ 3 →
      BalancedRegularity.frob (BalancedRegularity.relative P
        (jet (fun t => (A t : Matrix n n ℂ)) j)) ≤ d * L^j)
    (hBj : ∀ j : ℕ, 1 ≤ j → j ≤ 3 →
      BalancedRegularity.frob (BalancedRegularity.relative P
        (jet (fun t => (B t : Matrix n n ℂ)) j)) ≤ d * L^j) :
    ∀ j : ℕ, 1 ≤ j → j ≤ 3 →
      |scalarJet (fun t => 2 * fidelity (A t : Matrix n n ℂ) (B t : Matrix n n ℂ)) j| ≤
        2 * realTrace P * (100*d*L)^j := by
  have hAP : (A 0 : Matrix n n ℂ).PosDef := hA0.symm ▸ hP
  have hBP : (B 0 : Matrix n n ℂ).PosDef := hB0.symm ▸ hP
  have he := actual_transport_jet_equations hP hA hB hA0 hB0
  have hf := actual_fidelity_jet_equations hP hA hB hA0 hB0
  have hb := BalancedRegularity.fidelity_jet_bounds hP
    (transport_jet_isHermitian hA hB hAP hBP (j := 1) (by norm_num))
    (transport_jet_isHermitian hA hB hAP hBP (j := 2) (by norm_num))
    (transport_jet_isHermitian hA hB hAP hBP (j := 3) (by norm_num))
    he.1 he.2.1 he.2.2 hd hL
    (by simpa using hAj 1 (by omega) (by omega))
    (by simpa using hBj 1 (by omega) (by omega))
    (hAj 2 (by omega) (by omega)) (hBj 2 (by omega) (by omega))
    (hAj 3 (by omega) (by omega)) (hBj 3 (by omega) (by omega))
  intro j hj1 hj3
  interval_cases j
  · rw [hf.1]; simpa using hb.1
  · rw [hf.2.1]; exact hb.2.1
  · rw [hf.2.2]; exact hb.2.2

/-- Translate the normalized bound to an ordinary derivative bound. -/
theorem scalarJet_bound_to_iteratedDeriv {f : ℝ → ℝ} {j : ℕ} {B : ℝ}
    (h : |scalarJet f j| ≤ B) :
    |iteratedDeriv j f 0| ≤ (j.factorial : ℝ) * B := by
  have hp : 0 < (j.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos j)
  rw [scalarJet, abs_mul, abs_of_pos (inv_pos.mpr hp)] at h
  calc
    |iteratedDeriv j f 0| = (j.factorial : ℝ) *
        ((j.factorial : ℝ)⁻¹ * |iteratedDeriv j f 0|) := by
      rw [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
    _ ≤ (j.factorial : ℝ) * B := mul_le_mul_of_nonneg_left h hp.le

end AugmentedHigherRankKS.BalancedTransportJets
