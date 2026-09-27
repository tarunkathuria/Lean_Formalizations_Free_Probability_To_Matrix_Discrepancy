import MatrixSpencer.KSManuscriptInputBudgetBounds
import MatrixSpencer.KSFullManuscriptTaylor
import MatrixSpencer.KSEighthManuscriptParameters

/-!
# Polynomial size of the actual KS Taylor budgets

The bounds use the arithmetic constants already used by the numerical walks.
They do not replace a Taylor certificate or introduce an accuracy hypothesis.
The deliberately coarse fixed power is uniform over Parseval inputs.
-/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSManuscriptPolynomialTaylorBounds
open KSManuscriptInputBudgetBounds KSManuscriptScaleBounds
set_option maxHeartbeats 1600000

def sizeBase (N d : ℕ) : ℝ := 100000 * ((N : ℝ) + (d : ℝ) + 1)

theorem sizeBase_ge (N d : ℕ) : 100000 ≤ sizeBase N d := by
  unfold sizeBase
  have hN := Nat.cast_nonneg (α := ℝ) N
  have hd := Nat.cast_nonneg (α := ℝ) d
  linarith

theorem sizeBase_pos (N d : ℕ) : 0 < sizeBase N d := by
  have := sizeBase_ge N d
  linarith

private lemma denominator_le {n : Type*} [Fintype n] {B R κ θ : ℝ}
    (hB : 100000 ≤ B) (hR : 0 ≤ R) (hRb : R ≤ B^2) (hκ : κ ≤ B^2)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hd : (Fintype.card n : ℝ) ≤ B) :
    KSOptimizerFloor.inputDenominator (n := n) R κ θ ≤ B^3 := by
  have hB1 : 1 ≤ B := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hB2 : B ≤ B^2 := by nlinarith
  have hs : Real.sqrt κ ≤ B := (Real.sqrt_le_iff).mpr ⟨hB0,hκ⟩
  have hd' : Real.sqrt (Fintype.card n : ℝ) ≤ B :=
    (Real.sqrt_le_iff).mpr ⟨hB0,hd.trans hB2⟩
  have hm : θ * Real.sqrt (Fintype.card n : ℝ) ≤ B := by
    calc _ ≤ 1 * B := mul_le_mul hθ1 hd' (Real.sqrt_nonneg _) (by norm_num)
      _ = _ := one_mul _
  unfold KSOptimizerFloor.inputDenominator
  calc _ ≤ 2*B^2+4*B := by linarith
    _ ≤ 6*B^2 := by nlinarith
    _ ≤ B^3 := by nlinarith [sq_nonneg B]

private lemma floor_inv_le {n : Type*} [Fintype n] {B R κ θ : ℝ}
    (hB : 100000 ≤ B) (hR : 0 ≤ R) (hRb : R ≤ B^2) (hκ : κ ≤ B^2)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hθi : θ⁻¹ ≤ B)
    (hd : (Fintype.card n : ℝ) ≤ B) :
    ((θ / KSOptimizerFloor.inputDenominator (n := n) R κ θ)^2)⁻¹ ≤ B^8 := by
  have hb := denominator_le hB hR hRb hκ hθ.le hθ1 hd
  have hn : 0 ≤ KSOptimizerFloor.inputDenominator (n := n) R κ θ := by
    unfold KSOptimizerFloor.inputDenominator
    positivity
  rw [← inv_pow,inv_div,div_eq_mul_inv]
  calc _ ≤ (B^3*B)^2 := by gcongr
    _ = B^8 := by ring

private lemma radius_inv_le {B μ ρ : ℝ} (hB : 100000 ≤ B)
    (hμ : 0 < μ) (hρ : 0 < ρ) (hμb : μ⁻¹ ≤ B^8) (hρb : ρ⁻¹ ≤ B^8) :
    (KSComplexPerturbationRadius.radius μ ρ)⁻¹ ≤ B^9 := by
  have hB1 : 1 ≤ B := by linarith
  have hpow : 1 ≤ B^8 := one_le_pow₀ hB1
  have hm : (min 1 (min μ ρ))⁻¹ ≤ B^8 := by
    rcases le_total 1 (min μ ρ) with h | h
    · simpa only [min_eq_left h,inv_one] using hpow
    · rw [min_eq_right h]
      rcases le_total μ ρ with h' | h'
      · simpa only [min_eq_left h'] using hμb
      · simpa only [min_eq_right h'] using hρb
  unfold KSComplexPerturbationRadius.radius
  rw [inv_div,div_eq_mul_inv]
  calc _ ≤ 1000*B^8 := by gcongr
    _ ≤ B*B^8 := by gcongr; linarith
    _ = B^9 := by ring

private lemma value_le (D : ℕ) {B R κ θ : ℝ} (hB : 100000 ≤ B)
    (hR : 0 ≤ R) (hRb : R ≤ 2*B^2) (hκ : κ ≤ B^2)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hd : (D : ℝ) ≤ B) :
    1 + KSComplexObjectiveBound.valueCap D R 2 κ θ ≤ B^4 := by
  have hB0 : 0 ≤ B := by linarith
  have hB1 : 1 ≤ B := by linarith
  have hB2 : B ≤ B^2 := by nlinarith
  have hB3 : B^2 ≤ B^3 := by nlinarith [sq_nonneg B]
  have hs : Real.sqrt (2*κ) ≤ 2*B := (Real.sqrt_le_iff).mpr ⟨by positivity,by nlinarith⟩
  have hs2 : Real.sqrt (2:ℝ) ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by norm_num⟩
  unfold KSComplexObjectiveBound.valueCap
  calc _ ≤ 1+(B*(2*B^2)*2+2*B*(2*B)+2*1*B*2) := by gcongr
    _ ≤ 13*B^3 := by nlinarith
    _ ≤ B^4 := by nlinarith [pow_nonneg hB0 3]

private lemma joint_le {B V r : ℝ} (hB : 100000 ≤ B) (hV : 0 ≤ V)
    (hVb : V ≤ B^4) (hr : 0 < r) (hri : r⁻¹ ≤ B^9) :
    V*(10/r)^4 ≤ B^44 := by
  have hB0 : 0 ≤ B := by linarith
  have hq : 10/r ≤ B^10 := by
    rw [div_eq_mul_inv]
    calc _ ≤ B*B^9 := by gcongr; linarith
      _ = B^10 := by ring
  calc _ ≤ B^4*(B^10)^4 := by gcongr
    _ = B^44 := by ring

private lemma envelope_le {B X θ : ℝ} (hB : 100000 ≤ B) (hX : 0 ≤ X)
    (hXb : X ≤ B^44) (hθ : 0 < θ) (hθi : θ⁻¹ ≤ B) :
    KSTaylorBudget.envelopeCap X θ ≤ B^274 := by
  have hB0 : 0 ≤ B := by linarith
  have hB1 : 1 ≤ B := by linarith
  have hi : (θ/2)⁻¹ ≤ 2*B := by rw [inv_div,div_eq_mul_inv]; gcongr
  have hx89 : B^44 ≤ B^89 := pow_le_pow_right₀ hB1 (by norm_num)
  have ha : X+3*X^2/(θ/2) ≤ B^90 := by
    calc _ ≤ B^44+3*(B^44)^2*(2*B) := by
          rw [div_eq_mul_inv]
          gcongr
      _ ≤ 7*B^89 := by nlinarith
      _ ≤ B^90 := by nlinarith [pow_nonneg hB0 89]
  have hc : 1+X/(θ/2) ≤ B^46 := by
    have h45 : 1 ≤ B^45 := one_le_pow₀ hB1
    calc _ ≤ 1+B^44*(2*B) := by rw [div_eq_mul_inv]; gcongr
      _ ≤ 3*B^45 := by nlinarith
      _ ≤ B^46 := by nlinarith [pow_nonneg hB0 45]
  unfold KSTaylorBudget.envelopeCap
  calc _ ≤ B^90*(B^46)^4 := by gcongr
    _ = B^274 := by ring

variable {N d : ℕ}

private lemma base_linear_bounds (N d : ℕ) :
    2*(N:ℝ) ≤ sizeBase N d ∧ 2*(d:ℝ) ≤ sizeBase N d ∧
    6+10*(N:ℝ) ≤ sizeBase N d ∧ 3+9*(N:ℝ) ≤ sizeBase N d ∧
    2+6*(N:ℝ) ≤ sizeBase N d ∧ 4+4*(N:ℝ) ≤ sizeBase N d ∧
    1+1152*(N:ℝ) ≤ sizeBase N d := by
  have hN := Nat.cast_nonneg (α := ℝ) N
  have hd := Nat.cast_nonneg (α := ℝ) d
  unfold sizeBase
  constructor <;> [linarith; skip]
  constructor <;> [linarith; skip]
  constructor <;> [linarith; skip]
  constructor <;> [linarith; skip]
  constructor <;> [linarith; skip]
  constructor <;> linarith

private lemma base_source_bound (N d : ℕ) :
    1+23040*(d:ℝ)*N ≤ (sizeBase N d)^2 := by
  have hN := Nat.cast_nonneg (α := ℝ) N
  have hd := Nat.cast_nonneg (α := ℝ) d
  unfold sizeBase
  nlinarith [sq_nonneg (N:ℝ),sq_nonneg (d:ℝ),mul_nonneg hN hd]

private lemma actual_scales (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) :
    let δ := Real.sqrt (KSEighthManuscriptPreprocess.epsilon v)
    let θ := ksRegularizerScale (KSEighthManuscriptPreprocess.epsilon v) (Fin d)
    0<δ ∧ δ≤1 ∧ 0<θ ∧ θ≤1 ∧ θ⁻¹≤sizeBase N d ∧ δ⁻¹≤sizeBase N d := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  dsimp only
  have he := KSEighthManuscriptPreprocess.epsilon_pos v hd hp
  have hδ := Real.sqrt_pos.mpr he
  have hδ1 : Real.sqrt (KSEighthManuscriptPreprocess.epsilon v)≤1 := by
    simpa using Real.sqrt_le_sqrt (KSEighthManuscriptPreprocess.epsilon_le_one v hd hp)
  have hθ := ksRegularizerScale_pos (n := Fin d) he
  have hD : 1≤Real.sqrt (Fintype.card (Fin d ⊕ Fin d):ℝ) := by
    have hc : (1:ℝ)≤Fintype.card (Fin d ⊕ Fin d) := by
      simp only [Fintype.card_sum,Fintype.card_fin,Nat.cast_add]
      have : (1:ℝ)≤d := by exact_mod_cast hd
      linarith
    simpa using Real.sqrt_le_sqrt hc
  have hθ1 : ksRegularizerScale (KSEighthManuscriptPreprocess.epsilon v) (Fin d)≤1 := by
    unfold ksRegularizerScale
    exact (div_le_one (by linarith : 0<Real.sqrt (Fintype.card (Fin d ⊕ Fin d):ℝ))).mpr (hδ1.trans hD)
  refine ⟨hδ,hδ1,hθ,hθ1,(inverse_regularizer_le v hd hp).trans (base_linear_bounds N d).1,?_⟩
  exact (inverse_delta_le v hd hp).trans (by
    have h := (base_linear_bounds N d).1
    have hn := Nat.cast_nonneg (α := ℝ) N
    linarith)

/-- Polynomial bound for the actual eighth-cube fourth-derivative budget,
at the regularizer computed from the original Parseval input. -/
theorem eighth_fourthBudget_le (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) :
    KSEighthInputTaylorBound.fourthBudget v
      (ksRegularizerScale (KSEighthManuscriptPreprocess.epsilon v) (Fin d)) ≤
      (sizeBase N d)^274 := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  let B := sizeBase N d
  let θ := ksRegularizerScale (KSEighthManuscriptPreprocess.epsilon v) (Fin d)
  let R := KSEighthInputTaylorBound.centerCap v
  let S := KSEighthInputTaylorBound.directionCap v
  let κ := KSEighthInputTaylorBound.sourceCap v
  have hB : 100000≤B := sizeBase_ge N d
  have hB0 : 0≤B := by linarith
  have hB2 : B≤B^2 := by nlinarith
  obtain ⟨hδ,hδ1,hθ,hθ1,hθi,hδi⟩ := actual_scales v hd hp
  have hslope := KSEighthInputTaylorBound.slopeBudget_pos v
  have hR0 : 0≤R := by unfold R KSEighthInputTaylorBound.centerCap; positivity
  have hS0 : 0≤S := by unfold S KSEighthInputTaylorBound.directionCap; positivity
  have hR : R≤B^2 := ((eighth_centerCap_le v hp).trans (base_linear_bounds N d).2.2.2.1).trans hB2
  have hS : S≤B^2 := ((eighth_directionCap_le v hp).trans (base_linear_bounds N d).2.2.2.2.1).trans hB2
  have hκ : κ≤B^2 := by
    have h := eighth_sourceCap_le v hp
    have hprod := mul_nonneg (Nat.cast_nonneg (α := ℝ) d) (Nat.cast_nonneg (α := ℝ) N)
    exact h.trans (by nlinarith [base_source_bound N d])
  have hdim : (Fintype.card (Fin d ⊕ Fin d):ℝ)≤B := by
    simpa only [Fintype.card_sum,Fintype.card_fin,Nat.cast_add,two_mul] using (base_linear_bounds N d).2.1
  have hfloor := floor_inv_le (n := Fin d ⊕ Fin d) hB hR0 hR hκ hθ hθ1 hθi hdim
  have hfpos := KSEighthJointBoundPoint.floor_pos (n := Fin d) (κ := κ) hR0 hθ
  have hri := radius_inv_le hB hfpos (show (0:ℝ)<1/2 by norm_num) hfloor
    (show ((1:ℝ)/2)⁻¹≤B^8 by
      have hh : B≤B^8 := by simpa using pow_le_pow_right₀ (show 1≤B by linarith) (show 1≤8 by norm_num)
      norm_num
      linarith)
  have hr := KSEighthJointBoundPoint.radius_pos (n := Fin d) (κ := κ) hR0 hθ
  have hv := value_le (Fintype.card (Fin d ⊕ Fin d)) hB (add_nonneg hR0 hS0)
    (show R+S≤2*B^2 by linarith) hκ hθ.le hθ1 hdim
  have hv0 := (KSEighthJointBoundPoint.valueCap_pos (n := Fin d) (κ := κ) hR0 hS0 hθ.le).le
  have hj := joint_le hB hv0 hv hr hri
  have hj0 := (KSEighthInputTaylorBound.jointBudget_pos v hθ).le
  exact envelope_le hB hj0 hj hθ hθi


theorem full_budget_le (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) :
    KSFullManuscriptTaylor.budget v
      (Real.sqrt (KSEighthManuscriptPreprocess.epsilon v))
      (Real.sqrt (KSEighthManuscriptPreprocess.epsilon v)/(N:ℝ))
      (ksRegularizerScale (KSEighthManuscriptPreprocess.epsilon v) (Fin d)) ≤
      (sizeBase N d)^275 := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  let B := sizeBase N d
  let δ := Real.sqrt (KSEighthManuscriptPreprocess.epsilon v)
  let η := δ/(N:ℝ)
  let θ := ksRegularizerScale (KSEighthManuscriptPreprocess.epsilon v) (Fin d)
  have hB : 100000≤B := sizeBase_ge N d
  have hB0 : 0≤B := by linarith
  have hB1 : 1≤B := by linarith
  have hB2 : B≤B^2 := by nlinarith
  obtain ⟨hδ,hδ1,hθ,hθ1,hθi,hδi⟩ := actual_scales v hd hp
  have hη : 0≤η := by unfold η; positivity
  have hR0 := (KSDebitUniformFloor.centerRadius_pos v hδ.le hη).le
  have hR : KSDebitUniformFloor.centerRadius v δ η≤B^2 :=
    ((actual_centerRadius_le v hd hp).trans (base_linear_bounds N d).2.2.2.2.2.1).trans hB2
  have hspin : KSDebitUniformFloor.spinBudget v≤B^2 :=
    ((spinBudget_le v hp).trans (base_linear_bounds N d).2.2.2.2.2.2).trans hB2
  have hdim : (Fintype.card (Fin d ⊕ Fin d):ℝ)≤B := by
    simpa only [Fintype.card_sum,Fintype.card_fin,Nat.cast_add,two_mul] using (base_linear_bounds N d).2.1
  have hfloor := floor_inv_le (n := Fin d ⊕ Fin d) hB hR0 hR hspin hθ hθ1 hθi hdim
  have hfpos := KSDebitUniformFloor.uniformFloor_pos v hδ.le hη hθ
  have hmargin : (δ/2)⁻¹≤B^8 := by
    rw [inv_div,div_eq_mul_inv]
    calc _ ≤ 2*B := by gcongr
      _ ≤ B^2 := by nlinarith
      _ ≤ B^8 := pow_le_pow_right₀ hB1 (by norm_num)
  have hri := radius_inv_le hB hfpos (show 0<δ/2 by positivity) hfloor hmargin
  have hr := KSJointBoundParameters.radius_pos v hδ hη hθ
  have hc0 := (KSJointBoundParameters.centerCap_pos v hδ.le hη).le
  have hc : KSJointBoundParameters.centerCap v δ η≤B^2 :=
    ((actual_full_centerCap_le v hd hp).trans (base_linear_bounds N d).2.2.1).trans hB2
  have hs : KSComplexPolynomialBounds.sourceBudget v≤B^2 :=
    (sourceBudget_le v hp).trans (base_source_bound N d)
  have hv := value_le (Fintype.card (Fin d ⊕ Fin d)) hB hc0
    (show KSJointBoundParameters.centerCap v δ η≤2*B^2 by nlinarith) hs hθ.le hθ1 hdim
  have hv0 := (KSJointBoundParameters.objectiveCap_pos v hδ.le hη hθ.le).le
  have hj := joint_le hB hv0 hv hr hri
  have hj0 := (KSJointBoundParameters.jointCap_pos v hδ hη hθ).le
  have he := envelope_le hB hj0 hj hθ hθi
  have hn : (1:ℝ)≤N := by
    have hn' := (KSEighthManuscriptPreprocess.count_pos v hd hp).trans_le
      (KSEighthManuscriptPreprocess.count_le v)
    exact_mod_cast hn'
  have hcurv : KSFullManuscriptParameters.curvatureTolerance N δ≤1 := by
    unfold KSFullManuscriptParameters.curvatureTolerance
    apply (div_le_one (by linarith : (0:ℝ)<100*N)).mpr
    linarith
  have hcscalar : 6144*KSFullManuscriptParameters.curvatureTolerance N δ/δ^2≤B^274 := by
    rw [div_eq_mul_inv,←inv_pow]
    calc _ ≤ 6144*1*B^2 := by gcongr
      _ ≤ B^3 := by nlinarith [sq_nonneg B]
      _ ≤ B^274 := pow_le_pow_right₀ hB1 (by norm_num)
  have hmax := max_le he hcscalar
  have hp274 : 1≤B^274 := one_le_pow₀ hB1
  change max (KSTaylorBudget.envelopeCap (KSJointBoundParameters.jointCap v δ η θ) θ)
    (6144*KSFullManuscriptParameters.curvatureTolerance N δ/δ^2)+1≤B^275
  calc _ ≤ B^274+1 := add_le_add_right hmax 1
    _ ≤ B^275 := by nlinarith [pow_nonneg hB0 274]

/-- One common universal polynomial cap for the two concrete controllers. -/
def taylorCap (N d : ℕ) : ℝ := (sizeBase N d)^275

theorem taylorCap_ge_one (N d : ℕ) : 1≤taylorCap N d :=
  one_le_pow₀ (by have := sizeBase_ge N d; linarith)

theorem eighth_fourthBudget_le_taylorCap (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) :
    KSEighthInputTaylorBound.fourthBudget v
      (ksRegularizerScale (KSEighthManuscriptPreprocess.epsilon v) (Fin d)) ≤
      taylorCap N d :=
  (eighth_fourthBudget_le v hd hp).trans
    (pow_le_pow_right₀ (by have := sizeBase_ge N d; linarith) (by norm_num))

/-- The implemented eighth controller adds one to the raw fourth budget;
the same common polynomial cap also bounds that exact implemented constant. -/
theorem eighth_fourthCap_le_taylorCap (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) :
    KSEighthManuscriptParameters.fourthCap v
      (ksRegularizerScale (KSEighthManuscriptPreprocess.epsilon v) (Fin d)) ≤
      taylorCap N d := by
  have h := eighth_fourthBudget_le v hd hp
  have hB := sizeBase_ge N d
  have hB0 := (sizeBase_pos N d).le
  have hp274 : 1≤(sizeBase N d)^274 := one_le_pow₀ (by linarith)
  unfold KSEighthManuscriptParameters.fourthCap taylorCap
  calc _ ≤ 1+(sizeBase N d)^274 := add_le_add_left h 1
    _ ≤ (sizeBase N d)^275 := by nlinarith [pow_nonneg hB0 274]

/-- The actual complex-objective cap used by the full-cube query proof has
a low-degree polynomial bound; reports can add their proved absolute error. -/
theorem full_objectiveCap_le (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) :
    KSJointBoundParameters.objectiveCap v
      (Real.sqrt (KSEighthManuscriptPreprocess.epsilon v))
      (Real.sqrt (KSEighthManuscriptPreprocess.epsilon v)/(N:ℝ))
      (ksRegularizerScale (KSEighthManuscriptPreprocess.epsilon v) (Fin d)) ≤
      (sizeBase N d)^4 := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  let B := sizeBase N d
  have hB : 100000≤B := sizeBase_ge N d
  have hB2 : B≤B^2 := by nlinarith
  obtain ⟨hδ,hδ1,hθ,hθ1,hθi,hδi⟩ := actual_scales v hd hp
  have hη : 0≤Real.sqrt (KSEighthManuscriptPreprocess.epsilon v)/(N:ℝ) := by positivity
  have hc0 := (KSJointBoundParameters.centerCap_pos v hδ.le hη).le
  have hc := ((actual_full_centerCap_le v hd hp).trans (base_linear_bounds N d).2.2.1).trans hB2
  have hs := (sourceBudget_le v hp).trans (base_source_bound N d)
  have hdim : (Fintype.card (Fin d ⊕ Fin d):ℝ)≤B := by
    simpa only [Fintype.card_sum,Fintype.card_fin,Nat.cast_add,two_mul] using (base_linear_bounds N d).2.1
  exact value_le _ hB hc0 (by linarith) hs hθ.le hθ1 hdim

/-- The actual eighth-cube complex-objective cap on its retained-face
query neighborhood is polynomially bounded by the same input size. -/
theorem eighth_valueCap_le (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) :
    KSEighthJointBoundPoint.valueCap (n := Fin d)
      (KSEighthInputTaylorBound.centerCap v) (KSEighthInputTaylorBound.directionCap v)
      (KSEighthInputTaylorBound.sourceCap v)
      (ksRegularizerScale (KSEighthManuscriptPreprocess.epsilon v) (Fin d)) ≤
      (sizeBase N d)^4 := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  let B := sizeBase N d
  have hB : 100000≤B := sizeBase_ge N d
  have hB2 : B≤B^2 := by nlinarith
  obtain ⟨hδ,hδ1,hθ,hθ1,hθi,hδi⟩ := actual_scales v hd hp
  have hslope := KSEighthInputTaylorBound.slopeBudget_pos v
  have hR0 : 0≤KSEighthInputTaylorBound.centerCap v := by unfold KSEighthInputTaylorBound.centerCap; positivity
  have hS0 : 0≤KSEighthInputTaylorBound.directionCap v := by unfold KSEighthInputTaylorBound.directionCap; positivity
  have hR := ((eighth_centerCap_le v hp).trans (base_linear_bounds N d).2.2.2.1).trans hB2
  have hS := ((eighth_directionCap_le v hp).trans (base_linear_bounds N d).2.2.2.2.1).trans hB2
  have hκ : KSEighthInputTaylorBound.sourceCap v≤B^2 := by
    have h := eighth_sourceCap_le v hp
    have hprod := mul_nonneg (Nat.cast_nonneg (α := ℝ) d) (Nat.cast_nonneg (α := ℝ) N)
    exact h.trans (by nlinarith [base_source_bound N d])
  have hdim : (Fintype.card (Fin d ⊕ Fin d):ℝ)≤B := by
    simpa only [Fintype.card_sum,Fintype.card_fin,Nat.cast_add,two_mul] using (base_linear_bounds N d).2.1
  exact value_le _ hB (add_nonneg hR0 hS0) (by linarith) hκ hθ.le hθ1 hdim

end MatrixSpencer.KSManuscriptPolynomialTaylorBounds
