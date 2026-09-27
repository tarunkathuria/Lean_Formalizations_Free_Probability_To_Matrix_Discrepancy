import MatrixSpencer.RectangularRidgeSolverPreparation
import MatrixSpencer.KSJacobiPolynomialBounds

/-! Polynomial magnitude and Jacobi budgets for the literal finite value
response. The proof bounds actual value queries before division by the fixed
inverse-polynomial spacing, so it assumes no Gram norm or derivative bound. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeResponseMagnitude
open RectangularRidgePotential RectangularRidgePrimitiveParameters
open RectangularRidgeNumericalOptimizerFloor RectangularRidgeNumericalParameters
open RectangularRidgePreparationData MSManuscriptSupportedOwner
variable {N k d : ℕ} [Nonempty (Fin d)]
local instance ridgeResponseMagnitudeCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
attribute [local irreducible] RectangularRidgePotential.optimizer
set_option maxHeartbeats 700000

theorem potential_abs_le {ι : Type*} [Fintype ι]
    (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (B : ι→Matrix (Fin d) (Fin d) ℂ) (hN : 1≤N) (hND : N≤d)
    (hHn : ‖H‖≤N)
    (hb : (∑i,(B i)ᴴ*B i)≤(N:ℝ)^2 • (1:Matrix (Fin d) (Fin d) ℂ)) :
    |RectangularRidgePotential.potential H B (RectangularRidgeTuning.depth N d hN)
      (weight N d hN) (1/d)|≤100*size d N := by
  let m:=RectangularRidgeTuning.depth N d hN
  let θ:=weight N d hN
  let κ:ℝ:=1/d
  let S:=optimizer H B m θ κ
  have hS : S∈densitySet := optimizer_mem _ _ _ _ _
  have hm:=RectangularRidgeTuning.depth_positive N d hN
  have hθ : 0<θ := weight_positive hN hND
  have hκ : 0≤κ := by dsimp [κ];positivity
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hd : (1:ℝ)≤d := by exact_mod_cast (hN.trans hND)
  have hp:=RectangularRidgeOptimizerFloor.objective_le_input_bound H hH B m hm hθ.le hκ hHn hb hS
  have hq : 1/(2^m:ℝ)=exponent N d hN := by simp [m,exponent,RectangularRidgeTuning.order]
  rw [Real.sqrt_sq (Nat.cast_nonneg N),hq] at hp
  have hr:=regularizer_budget_le hN hND
  have hk:=RectangularRidgeParameters.ridge_overhead_le_two hd
  have hneg: - (N:ℝ)≤realTrace (H*S) := by
    have hh:=realTrace_mul_density_le_norm hH.neg hS
    simp only [Matrix.neg_mul,realTrace_neg,norm_neg] at hh
    linarith
  have hf:=fidelity_nonneg S (krausChannel B S)
  have hdy:=dyadicTsallisRegularizer_nonneg hm hθ.le hS.1
  have hs:=mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hκ)
    (realTrace_nonneg (CFC.sqrt_nonneg S).posSemidef)
  rw [potential_eq_optimizer,abs_le]
  change -(100*size d N)≤objective H B m θ κ S ∧ objective H B m θ κ S≤100*size d N
  have hobj: -(N:ℝ)≤objective H B m θ κ S := by
    unfold objective dyadicDensityObjective
    linarith
  change θ*(d:ℝ)^exponent N d hN/(1-exponent N d hN)≤81*RectangularRidgeParameters.size d N at hr
  change 2*κ*Real.sqrt d≤2 at hk
  simp only [Fintype.card_fin] at hp
  dsimp [size,RectangularRidgeParameters.size] at *
  constructor <;> linarith

theorem stored_potential_abs_le (P : Parameters N d) (hP : P.Valid)
    (U : Matrix (Fin N) (Fin k) ℝ) {C : Matrix (Fin k) (Fin k) ℝ}
    (hC : C.PosSemidef) (hphysical : covarianceLift U C≤1) :
    |RectangularRidgePotential.potential (P.center : Matrix (Fin d) (Fin d) ℂ)
      (covarianceKraus (mixFamily P.atoms U) C) (depth P) (theta P) (ridge P)|≤100*size d N :=
  potential_abs_le (P.center : Matrix (Fin d) (Fin d) ℂ) P.center.property
    (covarianceKraus (mixFamily P.atoms U) C) P.count_pos P.rectangular hP.2.2.1
    (mixed_covariance_budget P.atoms hP.1 hP.2.1 U hC hphysical)


theorem value_abs_le (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (U : Matrix (Fin N) (Fin k) ℝ)
    (C : selfAdjoint (Matrix (Fin k) (Fin k) ℝ))
    (hC : (C:Matrix (Fin k) (Fin k) ℝ).PosSemidef) (hphysical : covarianceLift U C≤1) :
    |RectangularRidgeSymmetricQueries.report solver (depth P)
      (RectangularRidgeTuning.depth_positive N d P.count_pos) a P.center
      (mixFamily P.atoms U) (mixFamily_isHermitian _ _ hP.1) C (theta P) (ridge P)
      (valueAccuracy (size d N))|≤101*size d N := by
  have he:=RectangularRidgeSymmetricQueries.report_accuracy solver (depth P)
    (RectangularRidgeTuning.depth_positive N d P.count_pos) a P.center
    (mixFamily P.atoms U) (mixFamily_isHermitian _ _ hP.1) C hC
    (weight_positive P.count_pos P.rectangular) (show 0≤ridge P by dsimp [ridge];positivity)
    (small_pos (by linarith [size_one_le P]) 346 64)
  have hv:=stored_potential_abs_le P hP U hC hphysical
  have hn:=small_le_one (size_one_le P) 346 64
  rcases abs_le.mp he with ⟨hl,hu⟩
  rcases abs_le.mp hv with ⟨hvl,hvu⟩
  apply abs_le.mpr
  dsimp only [theta,valueAccuracy] at *
  constructor <;> linarith [size_one_le P]

theorem probe_abs_le (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (U : Matrix (Fin N) (Fin k) ℝ)
    (C : selfAdjoint (Matrix (Fin k) (Fin k) ℝ))
    (hfloor : floor • (1:Matrix (Fin k) (Fin k) ℝ)≤C)
    (hphysical : covarianceLift U C≤1)
    (u : EuclideanSpace ℝ (Fin k)) (hu : ‖u‖=1) :
    |RectangularRidgeSolverGamma.probe solver (depth P)
      (RectangularRidgeTuning.depth_positive N d P.count_pos) a P.center
      (mixFamily P.atoms U) (mixFamily_isHermitian _ _ hP.1) C (theta P) (ridge P)
      (differenceStep (size d N)) (valueAccuracy (size d N)) u|≤big (size d N) 331 63 := by
  let s:=differenceStep (size d N)
  have hs : 0<s := small_pos (by linarith [size_one_le P]) 322 62
  have hsδ : s<floor := by
    have h:=differenceStep_le_floor (size_one_le P)
    change s≤(1/8192:ℝ)/8 at h
    norm_num [floor] at *
    linarith
  have hC:=MSManuscriptGammaSmoothness.posDef_of_floor (by norm_num [floor]) hfloor
  have hCs:=MSManuscriptGammaSmoothness.query_posDef hfloor hs.le hsδ u hu
  have hcut : (C:Matrix (Fin k) (Fin k) ℝ)-s • realRankOne (WithLp.ofLp u)≤C :=
    sub_le_self _ ((realRankOne_posSemidef (WithLp.ofLp u)).smul hs.le).nonneg
  have h0:=value_abs_le solver a P hP U C hC.posSemidef hphysical
  have h1:=value_abs_le solver a P hP U (C-s • hermitianRankOne (WithLp.ofLp u)) hCs.posSemidef
    ((covarianceLift_mono U hcut).trans hphysical)
  unfold RectangularRidgeSolverGamma.probe MSManuscriptGammaDifference.negativeSlope
    RectangularRidgeSolverGamma.valueCurve
  simp only [zero_smul,sub_zero]
  rw [abs_div,abs_of_pos hs,div_eq_mul_inv]
  apply (mul_le_mul_of_nonneg_right ((abs_sub _ _).trans
    (add_le_add h0 h1)) (inv_nonneg.mpr hs.le)).trans
  have he : s⁻¹=big (size d N) 322 62 := inv_inv _
  rw [he]
  have hsmall : 101*size d N+101*size d N≤big (size d N) 9 1 := by
    dsimp [big]
    norm_num
    linarith [size_one_le P]
  exact (mul_le_mul_of_nonneg_right hsmall (big_pos (by linarith [size_one_le P]) 322 62).le).trans_eq
    (big_mul (size d N) 9 1 322 62)

def entryBudget (N d : ℕ) : ℕ := 2^332*(d+N+2)^63
def topBudget (N d : ℕ) : ℕ := KSJacobiPolynomialBounds.jacobi N (entryBudget N d) (64*(d+N+2))

theorem cast_entryBudget (N d : ℕ) : (entryBudget N d:ℝ)=big (size d N) 332 63 := by
  simp only [entryBudget,big,size,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add]

theorem reported_entries (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (U : Matrix (Fin N) (Fin k) ℝ)
    (C : selfAdjoint (Matrix (Fin k) (Fin k) ℝ))
    (hfloor : floor • (1:Matrix (Fin k) (Fin k) ℝ)≤C)
    (hphysical : covarianceLift U C≤1) :
    ∀i j,|RectangularRidgeSolverGamma.report solver a P.center P.atoms hP.1 U P.count_pos C i j|≤
      (entryBudget N d:ℝ) := by
  have he:=MSManuscriptGammaMatrix.reconstruct_entry_error (0:Matrix (Fin k) (Fin k) ℝ)
    (by simp [Matrix.IsSymm]) _ (big_pos (by linarith [size_one_le P]) 331 63).le
    (by simpa only [KSRayleighAccuracy.realRayleigh,map_zero,ContinuousLinearMap.zero_apply,
      inner_zero_right,sub_zero] using probe_abs_le solver a P hP U C hfloor hphysical)
  intro i j
  have h:=he i j
  simp only [Matrix.zero_apply,zero_sub,abs_neg] at h
  apply h.trans_eq
  rw [cast_entryBudget]
  have hh:=big_mul (size d N) 1 0 331 63
  norm_num only [big,pow_one,pow_zero,mul_one,Nat.add_zero,Nat.reduceAdd] at hh
  exact hh

theorem state_reported_entries (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) (hO : State O) :
    ∀i j,|RectangularRidgeSolverPreparation.value solver a P hP O i j|≤(entryBudget N d:ℝ) := by
  have he:=RectangularRidgeSolverPreparation.coefficients_eq O hO
  exact reported_entries solver a P hP O.frame (RectangularRidgeSolverPreparation.coefficients O)
    (by rw [he];exact hO.1.2) (by rw [he];exact hO.2.1)

theorem state_report_norm (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) (hO : State O) :
    ‖Matrix.toEuclideanCLM (𝕜:=ℝ) (RectangularRidgeSolverPreparation.value solver a P hP O)‖≤
      (N:ℝ)*entryBudget N d := by
  have hh:=KSMatrixEntryAccuracy.operatorNorm_le_card_mul _ (Nat.cast_nonneg (entryBudget N d))
    (state_reported_entries solver a P hP O hO)
  exact hh.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hO.2.2) (Nat.cast_nonneg _))

theorem top_ceiling_input_le (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) (hO : State O) :
    KSJacobiIteration.denominator O.dim*KSJacobiStep.offDiagonalEnergy
      (-RectangularRidgeSolverPreparation.value solver a P hP O)/(P.threshold/64)^2≤(topBudget N d:ℝ) := by
  have hi : P.threshold⁻¹≤size d N := by
    have hh:=inv_anti₀ (one_div_pos.mpr (by linarith [size_one_le P])) hP.2.2.2
    simpa only [one_div,inv_inv] using hh
  apply KSJacobiPolynomialBounds.ceiling_input_le _ hO.2.2
    (by simpa only [Matrix.neg_apply,abs_neg] using state_reported_entries solver a P hP O hO)
    (by have hh:=threshold_pos P hP;positivity)
  rw [inv_div,div_eq_mul_inv]
  have hh:=mul_le_mul_of_nonneg_left hi (by norm_num : (0:ℝ)≤64)
  simpa only [size,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add] using hh

end MatrixSpencer.RectangularRidgeResponseMagnitude
