import FaithfulMS.RectangularDirectMagnitude

/-! Uniform polynomial magnitude of an exact rectangular Gram report. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularDirectEntryBound
open FaithfulMS.DirectDensity RectangularRidgePreparationData MSManuscriptSupportedOwner
open RectangularDirectMagnitude
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma entry_le_trace {G : Matrix ι ι ℝ} (hG : G.PosSemidef) (i j : ι) :
    |G i j| ≤ realTrace G := by
  have hdiag (a : ι) : 0 ≤ G a a := by simpa using hG.2 (Pi.single a 1)
  have htr (a : ι) : G a a ≤ realTrace G :=
    Finset.single_le_sum (fun b _ => hdiag b) (Finset.mem_univ a)
  have hp := hG.2 (Pi.single i 1 + Pi.single j 1)
  have hn := hG.2 (Pi.single i 1 - Pi.single j 1)
  simp only [star_trivial, Matrix.mulVec_add, Matrix.mulVec_sub,
    add_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_sub,
    single_dotProduct, Matrix.mulVec_single_one, one_mul] at hp hn
  have hsym : G j i = G i j := by
    have hh := congrFun (congrFun hG.isHermitian.eq i) j
    simpa using hh
  simp only [Matrix.col, Matrix.transpose_apply] at hp hn
  rw [hsym] at hp hn
  exact abs_le.mpr ⟨by linarith [htr i, htr j], by linarith [htr i, htr j]⟩

variable {N d : ℕ} [Nonempty (Fin d)]
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}

lemma solution_posDef (solver : RectangularDirectSolver.Service) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) (hO : State O) :
    (RectangularDirectSolver.solution solver a P hP O hO).density.PosDef := by
  rw [RectangularSolution.density_eq_optimizer _
    (RectangularRidgeTuning.depth_positive N d P.count_pos)
    (RectangularRidgePrimitiveParameters.weight_positive P.count_pos P.rectangular)
    (show 0 ≤ ridge P by dsimp [ridge]; positivity)]
  exact RectangularRidgePotential.optimizer_posDef _ _
    (RectangularRidgeTuning.depth_positive N d P.count_pos)
    (RectangularRidgePrimitiveParameters.weight_positive P.count_pos P.rectangular)
    (show 0 ≤ ridge P by dsimp [ridge]; positivity)

lemma trace_le (solver : RectangularDirectSolver.Service) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) (hO : State O) :
    realTrace (RectangularDirectSolver.value solver a P hP O) ≤ 8192 * N := by
  let S := (RectangularDirectSolver.solution solver a P hP O hO).density
  have hS : S.PosDef := solution_posDef solver a P hP O hO
  have hSmem : S ∈ densitySet := (RectangularDirectSolver.solution solver a P hP O hO).feasible
  let A := mixFamily P.atoms O.frame
  have hA : ∀ i, (A i).IsHermitian := mixFamily_isHermitian _ _ hP.1
  have hC := hO.1.matrix_posSemidef O (by norm_num [floor])
  have hΓ : (gamma A O.matrix S).PosSemidef := gamma_posSemidef A hA O.matrix hS
  have hfloor := realTrace_mul_mono hΓ hO.1.2
  rw [Matrix.mul_smul, Matrix.mul_one, realTrace_smul,
    realTrace_mul_comm (gamma A O.matrix S) O.matrix,
    trace_covariance_gram A hA hC hS] at hfloor
  have hf := fidelity_le_sqrt_trace_mul hSmem.1 (krausChannel_posSemidef (covarianceKraus A O.matrix) hSmem.1)
  rw [hSmem.2, one_mul] at hf
  have hb := RectangularRidgeNumericalOptimizerFloor.mixed_covariance_budget P.atoms hP.1 hP.2.1 O.frame hC hO.2.1
  have ht := KSOptimizerFloor.kraus_trace_le_of_budget (covarianceKraus A O.matrix) hb hSmem
  have hu := hf.trans (Real.sqrt_le_sqrt ht)
  rw [Real.sqrt_sq (Nat.cast_nonneg N)] at hu
  change floor * realTrace (gamma A O.matrix S) ≤ _ at hfloor
  have he : RectangularDirectSolver.value solver a P hP O = gamma A O.matrix S := by
    rw [RectangularDirectSolver.value, dif_pos hO]
  rw [he]
  norm_num only [floor] at hfloor
  linarith

lemma entries (solver : RectangularDirectSolver.Service) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) (hO : State O) :
    ∀ i j, |RectangularDirectSolver.value solver a P hP O i j| ≤ (8192 * N : ℕ) := by
  have hΓ : (RectangularDirectSolver.value solver a P hP O).PosSemidef := by
    rw [RectangularDirectSolver.value, dif_pos hO]
    exact gamma_posSemidef _ (mixFamily_isHermitian _ _ hP.1) _
      (solution_posDef solver a P hP O hO)
  intro i j
  exact (entry_le_trace hΓ i j).trans (by simpa using trace_le solver a P hP O hO)

def topBudget (N d : ℕ) : ℕ := KSJacobiPolynomialBounds.jacobi N (8192 * N) (64 * (d + N + 2))

theorem top_ceiling_input_le (solver : RectangularDirectSolver.Service) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) (hO : State O) :
    KSJacobiIteration.denominator O.dim * KSJacobiStep.offDiagonalEnergy
      (-RectangularDirectSolver.value solver a P hP O) / (P.threshold / 64)^2 ≤ topBudget N d := by
  have hi : P.threshold⁻¹ ≤ RectangularRidgeNumericalOptimizerFloor.size d N := by
    have hh := inv_anti₀ (one_div_pos.mpr (by linarith [size_one_le P])) hP.2.2.2
    simpa only [one_div, inv_inv] using hh
  apply KSJacobiPolynomialBounds.ceiling_input_le _ hO.2.2
    (by simpa only [Matrix.neg_apply, abs_neg] using entries solver a P hP O hO)
    (by have hh := threshold_pos P hP; positivity)
  rw [inv_div, div_eq_mul_inv]
  have hh := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 64)
  simpa only [RectangularRidgeNumericalOptimizerFloor.size, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_add] using hh

end MatrixSpencer.RectangularDirectEntryBound
