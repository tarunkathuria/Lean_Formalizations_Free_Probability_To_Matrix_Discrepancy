import MatrixSpencer.KSJacobiPolynomialBounds
import MatrixSpencer.KSPolynomialConvexSolver

/-! Uniform natural size and accuracy budgets for every KS convex-value
query at original-input tuning. These supply the solver's permitted runtime
contract from Parseval inputs; no tolerance or horizon bound is assumed. -/

open Matrix
noncomputable section
namespace MatrixSpencer.KSConvexQueryBudgets
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
open KSEighthManuscriptPreprocess KSJacobiPolynomialBounds
open KSManuscriptInputPolynomialParameters KSManuscriptPolynomialTaylorBounds
variable {N d : ℕ}

def programSize (d : ℕ) : ℕ := 6400*d^4+16*d^2+2
def fullValue (N d : ℕ) : ℕ := 1600*N^3*fullQuery N d
def eighthValue (N d : ℕ) : ℕ := 4000000*N^5*eighthQuery N d
def valuePrecision (N d : ℕ) : ℕ := 800*N^2+fullValue N d+eighthValue N d+1
def fullHorizon (N d : ℕ) : ℕ := 256*N^3+100*N^3*taylor N d+1
def eighthHorizon (N d : ℕ) : ℕ := 4000000*N*(N^5+taylor N d*N^4+1)+1

def solverWork (P : KSPolynomialConvexSolver.PolynomialSolver) (N d : ℕ) : ℕ :=
  P.coefficient*(programSize d+valuePrecision N d+1)^P.degree

theorem dataSize_le (a : Fin (d+d)) :
    KSPolynomialConvexSolver.dataSize
      (KSFullManuscriptAffineData.dimension a)
      (KSFullManuscriptAffineData.matrixSize (Fin (d+d))) ≤ programSize d := by
  have hdim : KSFullManuscriptAffineData.dimension a ≤ 4*(d+d)^2 := by
    rw [KSConvexValueOracle.variableCount]
    omega
  unfold KSPolynomialConvexSolver.dataSize
  rw [KSConvexValueOracle.pencilEntries a]
  calc
    _ ≤ 400*(d+d)^4+4*(d+d)^2+2 := by omega
    _ = programSize d := by unfold programSize; ring

theorem owner_solver_call_cost (P : KSPolynomialConvexSolver.PolynomialSolver)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : Fin (d+d)) (H : Matrix (Fin (d+d)) (Fin (d+d)) ℂ)
    (A : ι → Matrix (Fin (d+d)) (Fin (d+d)) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : Matrix ι ι ℝ) (hC : C.PosSemidef)
    (hd : 0 < d+d) (θ : ℝ) {ν : ℝ} (hν : 0 < ν)
    (hprecision : ν⁻¹ ≤ (valuePrecision N d : ℝ)) :
    (P.run (KSConvexValueOracle.ownerData a A hA C hC hd)
      (KSFullManuscriptAffineObjective.coefficient a H θ)
      (KSFullManuscriptAffineObjective.offset H θ
        (KSFullManuscriptCenterData.densityCenter hd) 0) ν).cost ≤ solverWork P N d :=
  P.run_cost_le _ _ _ hν (dataSize_le a) hprecision

private theorem scaled_inverse {δ : ℝ} (c : ℝ) :
    (δ/(N:ℝ)/c)⁻¹ = c*(N:ℝ)*δ⁻¹ := by
  simp only [div_eq_mul_inv, _root_.mul_inv_rev, inv_inv]
  ring

theorem full_state_inverse (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) :
    (Real.sqrt (epsilon v)/(N:ℝ)/8)⁻¹ ≤ (valuePrecision N d : ℝ) := by
  rw [scaled_inverse]
  have hi := KSManuscriptScaleBounds.inverse_delta_le v hd hp
  have hn := Nat.cast_nonneg (α := ℝ) N
  have h : 8*(N:ℝ)*(Real.sqrt (epsilon v))⁻¹ ≤ 800*(N:ℝ)^2 := by
    have hm := mul_le_mul_of_nonneg_left hi (show 0 ≤ 8*(N:ℝ) by positivity)
    nlinarith
  apply h.trans
  have hb : 800*N^2 ≤ valuePrecision N d := by unfold valuePrecision; omega
  exact_mod_cast hb

theorem eighth_state_inverse (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) :
    (KSEighthManuscriptParameters.rho N (Real.sqrt (epsilon v))/8)⁻¹ ≤
      (valuePrecision N d : ℝ) := by
  have hi := KSManuscriptPolynomialParameters.eighth_rho_inv_le
    (KSManuscriptScaleBounds.inverse_delta_le v hd hp)
  have h : (KSEighthManuscriptParameters.rho N (Real.sqrt (epsilon v))/8)⁻¹ ≤ 800*(N:ℝ)^2 := by
    simp only [div_eq_mul_inv, _root_.mul_inv_rev, inv_inv]
    nlinarith
  apply h.trans
  have hb : 800*N^2 ≤ valuePrecision N d := by unfold valuePrecision; omega
  exact_mod_cast hb

/-- The eighth-cube final acceptance report uses precision `δ/4`. -/
theorem acceptance_inverse (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) :
    (Real.sqrt (epsilon v)/4)⁻¹ ≤ (valuePrecision N d : ℝ) := by
  have hi := KSManuscriptScaleBounds.inverse_delta_le v hd hp
  have hN := labels_pos v hd hp
  have hn : (1:ℝ)≤N := Nat.one_le_cast.mpr hN
  have h : (Real.sqrt (epsilon v)/4)⁻¹ ≤ 800*(N:ℝ)^2 := by
    simp only [div_eq_mul_inv,_root_.mul_inv_rev,inv_inv]
    nlinarith
  apply h.trans
  have hb : 800*N^2 ≤ valuePrecision N d := by unfold valuePrecision; omega
  exact_mod_cast hb

theorem full_query_inverse (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) :
    (KSFullManuscriptParameters.valueTolerance N (Real.sqrt (epsilon v))
      (KSFullManuscriptAlgorithm.taylorBudget v (epsilon v)))⁻¹ ≤ (valuePrecision N d : ℝ) := by
  have hi : (KSFullManuscriptParameters.valueTolerance N (Real.sqrt (epsilon v))
      (KSFullManuscriptAlgorithm.taylorBudget v (epsilon v)))⁻¹ ≤ (fullValue N d : ℝ) := by
    simpa only [fullValue, fullQuery, Nat.cast_mul, Nat.cast_add, Nat.cast_pow,
      Nat.cast_ofNat, cast_taylor] using full_value_inv_le v hd hp
  apply hi.trans
  exact_mod_cast (show fullValue N d ≤ valuePrecision N d from by unfold valuePrecision; omega)

/-- This applies to the convex-solver variant retaining all original labels. -/
theorem eighth_query_inverse (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) (x : Fin N → ℝ)
    (hx : 0 < KSEighthLiveEnumeration.count x) :
    (KSEighthHessianQueries.queryTolerance v (ksRegularizerScale (epsilon v) (Fin d))
      (KSEighthManuscriptParameters.precision N (Real.sqrt (epsilon v))) x)⁻¹ ≤
      (valuePrecision N d : ℝ) := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hN := labels_pos v hd hp
  have hδ := Real.sqrt_pos.mpr (epsilon_pos v hd hp)
  have hθ := ksRegularizerScale_pos (n := Fin d) (epsilon_pos v hd hp)
  have hM := KSEighthManuscriptParameters.fourthCap_pos v hθ hd
  have hi := KSManuscriptPolynomialParameters.eighth_query_value_inv_le v hN hδ
    (KSManuscriptScaleBounds.inverse_delta_le v hd hp) hM
    (eighth_fourthCap_le_taylorCap v hd hp) x hx
  have he : (KSEighthHessianQueries.queryTolerance v (ksRegularizerScale (epsilon v) (Fin d))
      (KSEighthManuscriptParameters.precision N (Real.sqrt (epsilon v))) x)⁻¹ ≤
      (eighthValue N d : ℝ) := by
    simpa only [eighthValue, eighthQuery, Nat.cast_mul, Nat.cast_add, Nat.cast_pow,
      Nat.cast_ofNat, cast_taylor] using hi
  apply he.trans
  exact_mod_cast (show eighthValue N d ≤ valuePrecision N d from by unfold valuePrecision; omega)

theorem full_horizon (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) :
    KSFullManuscriptAlgorithm.horizon v (epsilon v) ≤ fullHorizon N d := by
  have h : (KSFullManuscriptAlgorithm.horizon v (epsilon v) : ℝ) ≤ (fullHorizon N d : ℝ) := by
    simpa only [fullHorizon, fullHorizonBound, Nat.cast_add, Nat.cast_mul,
      Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat, cast_taylor] using full_horizon_le v hd hp
  exact_mod_cast h

theorem eighth_horizon (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) :
    KSEighthManuscriptBudgets.cutoff v (Real.sqrt (epsilon v))
      (ksRegularizerScale (epsilon v) (Fin d)) ≤ eighthHorizon N d := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hθ := ksRegularizerScale_pos (n := Fin d) (epsilon_pos v hd hp)
  have h := KSManuscriptPolynomialParameters.eighth_cutoff_le v (labels_pos v hd hp)
    (Real.sqrt_pos.mpr (epsilon_pos v hd hp)) (KSManuscriptScaleBounds.inverse_delta_le v hd hp)
    (KSEighthManuscriptParameters.fourthCap_pos v hθ hd) (eighth_fourthCap_le_taylorCap v hd hp)
  apply (Nat.cast_le (α := ℝ)).mp
  simpa only [eighthHorizon, Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat, cast_taylor] using h

end MatrixSpencer.KSConvexQueryBudgets
