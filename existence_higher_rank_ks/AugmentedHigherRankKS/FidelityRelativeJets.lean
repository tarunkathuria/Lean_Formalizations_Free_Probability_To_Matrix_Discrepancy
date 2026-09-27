import AugmentedHigherRankKS.BalancedTransportJets
import AugmentedHigherRankKS.BalancedFidelityCongruence
import HigherRankKS.SourceSmoothness

/-! Relative derivative bounds for actual, possibly unbalanced fidelity inputs. -/
open Matrix MatrixSpencer HigherRankKS Filter
open scoped BigOperators Topology ContDiff MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace AugmentedHigherRankKS
open BalancedTransportJets BalancedRegularity
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance relativeJetsCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))

theorem jet_selfAdjoint (A : ℝ → selfAdjoint (Matrix n n ℂ))
    (hA : ContDiffAt ℝ 3 A 0) {j : ℕ} (hj : (j : WithTop ℕ∞) ≤ 3) :
    (jet (fun t => (A t : Matrix n n ℂ)) j).IsHermitian := by
  have hh := iteratedDeriv_clm (hermitianInclusion (n := n)) hA hj
  change iteratedDeriv j (fun t => (A t : Matrix n n ℂ)) 0 =
    ((iteratedDeriv j A (0 : ℝ) : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) at hh
  unfold jet
  rw [hh]
  exact (IsSelfAdjoint.all ((j.factorial : ℝ)⁻¹)).smul
    ((iteratedDeriv j A (0 : ℝ)).property)

def congruenceCurve (T : Matrix n n ℂ) (hT : T.PosDef)
    (A : ℝ → selfAdjoint (Matrix n n ℂ)) : ℝ → selfAdjoint (Matrix n n ℂ) :=
  fun t => hermitianCongruenceEquiv T hT (A t)

theorem contDiffAt_congruenceCurve {T : Matrix n n ℂ} (hT : T.PosDef)
    {A : ℝ → selfAdjoint (Matrix n n ℂ)} (hA : ContDiffAt ℝ 3 A 0) :
    ContDiffAt ℝ 3 (congruenceCurve T hT A) 0 := by
  exact (hermitianCongruenceEquiv T hT).toLinearMap.toContinuousLinearMap.contDiff.contDiffAt.comp 0 hA

theorem jet_congruenceCurve {T : Matrix n n ℂ} (hT : T.PosDef)
    {A : ℝ → selfAdjoint (Matrix n n ℂ)} (hA : ContDiffAt ℝ 3 A 0)
    {j : ℕ} (hj : (j : WithTop ℕ∞) ≤ 3) :
    jet (fun t => (congruenceCurve T hT A t : Matrix n n ℂ)) j =
      T * jet (fun t => (A t : Matrix n n ℂ)) j * T := by
  have hd := (hermitianInclusion (n := n)).contDiff.contDiffAt.comp 0 hA
  let L := matrixExtensionCLM T
  have hh := iteratedDeriv_clm L hd hj
  change iteratedDeriv j (fun t => T * (A t : Matrix n n ℂ) * Tᴴ) 0 =
    T * iteratedDeriv j (fun t => (A t : Matrix n n ℂ)) 0 * Tᴴ at hh
  simp only [hT.isHermitian.eq] at hh
  change ((j.factorial : ℝ)⁻¹) •
    iteratedDeriv j (fun t => T * (A t : Matrix n n ℂ) * T) 0 = _
  rw [hh]
  simp only [jet, Matrix.mul_smul, Matrix.smul_mul]

/-- Bounds on both actual input jets imply bounds on the actual fidelity jets.
The constant does not depend on the smallest eigenvalue of either input. -/
theorem fidelity_jet_le_of_order {A B : ℝ → selfAdjoint (Matrix n n ℂ)}
    (hA : ContDiffAt ℝ 3 A 0) (hB : ContDiffAt ℝ 3 B 0)
    (hA0 : (A 0 : Matrix n n ℂ).PosDef) (hB0 : (B 0 : Matrix n n ℂ).PosDef)
    {d L : ℝ} (hd : 1 ≤ d) (hdn : Real.sqrt (Fintype.card n : ℝ) ≤ d) (hL : 0 ≤ L)
    (ha : ∀ j : ℕ, 1 ≤ j → j ≤ 3 →
      -(L^j) • (A 0 : Matrix n n ℂ) ≤ jet (fun t => (A t : Matrix n n ℂ)) j ∧
      jet (fun t => (A t : Matrix n n ℂ)) j ≤ L^j • (A 0 : Matrix n n ℂ))
    (hb : ∀ j : ℕ, 1 ≤ j → j ≤ 3 →
      -(L^j) • (B 0 : Matrix n n ℂ) ≤ jet (fun t => (B t : Matrix n n ℂ)) j ∧
      jet (fun t => (B t : Matrix n n ℂ)) j ≤ L^j • (B 0 : Matrix n n ℂ)) :
    ∀ j : ℕ, 1 ≤ j → j ≤ 3 →
      |scalarJet (fun t => 2*fidelity (A t : Matrix n n ℂ) (B t : Matrix n n ℂ)) j| ≤
        2*fidelity (A 0 : Matrix n n ℂ) (B 0 : Matrix n n ℂ)*(100*d*L)^j := by
  let Z := transportOptimizer (A 0 : Matrix n n ℂ) (B 0 : Matrix n n ℂ)
  have hZ : Z.PosDef := transportOptimizer_posDef hA0 hB0
  let T := CFC.sqrt Z
  have hT : T.PosDef := hZ.posDef_sqrt
  let P := T⁻¹ * (A 0 : Matrix n n ℂ) * T⁻¹
  have hP : P.PosDef := posDef_congruence hT.inv hA0
  let A' := congruenceCurve T⁻¹ hT.inv A
  let B' := congruenceCurve T hT B
  have hA' : ContDiffAt ℝ 3 A' 0 := contDiffAt_congruenceCurve hT.inv hA
  have hB' : ContDiffAt ℝ 3 B' 0 := contDiffAt_congruenceCurve hT hB
  have hA'0 : (A' 0 : Matrix n n ℂ) = P := rfl
  have hB'0 : (B' 0 : Matrix n n ℂ) = P := by
    exact (balancedDensity_eq_source_congruence hZ (transportOptimizer_solve hA0 hB0)).symm
  have hcoeff (C : ℝ → selfAdjoint (Matrix n n ℂ)) (hC : ContDiffAt ℝ 3 C 0)
      (Q : Matrix n n ℂ) (hQ : Q.PosDef)
      (he : Q * (C 0 : Matrix n n ℂ) * Q = P)
      (hc : ∀ j : ℕ, 1 ≤ j → j ≤ 3 →
        -(L^j) • (C 0 : Matrix n n ℂ) ≤ jet (fun t => (C t : Matrix n n ℂ)) j ∧
        jet (fun t => (C t : Matrix n n ℂ)) j ≤ L^j • (C 0 : Matrix n n ℂ)) :
      ∀ j : ℕ, 1 ≤ j → j ≤ 3 →
        frob (relative P (jet (fun t =>
          (congruenceCurve Q hQ C t : Matrix n n ℂ)) j)) ≤ d*L^j := by
    intro j hj1 hj3
    have hj : (j : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hj3
    have hlo := hQ.isHermitian.isSelfAdjoint.conjugate_le_conjugate (hc j hj1 hj3).1
    have hhi := hQ.isHermitian.isSelfAdjoint.conjugate_le_conjugate (hc j hj1 hj3).2
    change Q * (-(L^j) • (C 0 : Matrix n n ℂ)) * Q ≤
      Q * jet (fun t => (C t : Matrix n n ℂ)) j * Q at hlo
    change Q * jet (fun t => (C t : Matrix n n ℂ)) j * Q ≤
      Q * (L^j • (C 0 : Matrix n n ℂ)) * Q at hhi
    simp only [Matrix.mul_smul, Matrix.smul_mul, he] at hlo hhi
    rw [jet_congruenceCurve hQ hC hj]
    have hx : (Q * jet (fun t => (C t : Matrix n n ℂ)) j * Q).IsHermitian := by
      simpa only [hQ.isHermitian.eq] using Matrix.isHermitian_conjTranspose_mul_mul Q
        (jet_selfAdjoint C hC hj)
    exact (relative_frob_le hP hx (pow_nonneg hL j) hlo hhi).trans
      (mul_le_mul_of_nonneg_right hdn (pow_nonneg hL j))
  have hh := actual_fidelity_jet_bounds hP hA' hB' hA'0 hB'0 hd hL
    (hcoeff A hA T⁻¹ hT.inv rfl ha) (hcoeff B hB T hT hB'0 hb)
  have he : (fun t => 2*fidelity (A' t : Matrix n n ℂ) (B' t : Matrix n n ℂ)) =ᶠ[𝓝 0]
      (fun t => 2*fidelity (A t : Matrix n n ℂ) (B t : Matrix n n ℂ)) := by
    filter_upwards [hA.continuousAt.eventually (eventually_posDef_of_posDef (A 0) hA0),
      hB.continuousAt.eventually (eventually_posDef_of_posDef (B 0) hB0)] with t hat hbt
    exact congrArg (fun z : ℝ => 2*z) (fidelity_opposite_congruence hT hat hbt)
  have htr : realTrace P = fidelity (A 0 : Matrix n n ℂ) (B 0 : Matrix n n ℂ) := by
    have hbase := fidelity_opposite_congruence hT hA0 hB0
    change fidelity P (B' 0 : Matrix n n ℂ) = _ at hbase
    rw [hB'0] at hbase
    rw [← trace_transportOptimizer_eq_fidelity hP hP, transportOptimizer_self hP,
      Matrix.mul_one] at hbase
    exact hbase
  intro j hj1 hj3
  have hj := hh j hj1 hj3
  simpa only [scalarJet, he.iteratedDeriv_eq j, htr] using hj

end AugmentedHigherRankKS
