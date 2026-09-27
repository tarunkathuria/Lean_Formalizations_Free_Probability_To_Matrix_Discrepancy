import FaithfulMS.DirectSDPArithmetic
import FaithfulMS.DirectSDPPolynomialCost
import FaithfulMS.DirectGammaArithmetic
import FaithfulMS.RectangularDirectPrograms
import MatrixSpencer.RectangularRidgeResponseScalars
import MatrixSpencer.RealRAMMSOwnerReport

/-! Concrete primal-SDP and spectral implementation of the rectangular
preparation report. Validity proofs are supplied by the walk invariant;
the off-domain branch merely totalizes the mathematical function.
-/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularDirectConcreteResponse
open FaithfulMS RealRAM
open RealRAM.JacobiIteration (Counted)
open RectangularRidgePreparationData MSManuscriptSupportedOwner
variable {N d : ℕ} [Nonempty (Fin d)]
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 400000

def validResponse (S : DirectSDP.PolynomialService) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) (hO : State O) :
    Counted (Matrix (Fin O.dim) (Fin O.dim) ℝ) := by
  let fam := MSOwnerReport.family P.atoms O.frame
  have hfam : ∀ i, (fam.value i).IsHermitian := by
    rw [MSOwnerReport.family_value]
    exact mixFamily_isHermitian _ _ hP.1
  let t := RectangularRidgeResponseScalars.compute N d
  have hm : 1 ≤ depth P := RectangularRidgeTuning.depth_positive N d P.count_pos
  have hθ : 0 < theta P := RectangularRidgePrimitiveParameters.weight_positive P.count_pos P.rectangular
  have hC := hO.1.matrix_posSemidef O (show (0 : ℝ) ≤ floor by norm_num [floor])
  have hd : 0 < d := Fin.pos_iff_nonempty.mpr inferInstance
  let q := DirectSDPArithmetic.rectangular S (depth P) hm P.center fam.value hfam
    O.matrix hC hd (theta P)
  have hρ : q.value.density.PosDef := by
    rw [DirectSDPArithmetic.rectangular_density S _ hm _ _ hfam _ hC hd _ hθ]
    rw [DirectDensity.RectangularSolution.density_eq_optimizer _ hm hθ (by positivity)]
    exact RectangularRidgePotential.optimizer_posDef _ _ hm hθ (by positivity)
  let g := DirectGammaArithmetic.compute fam.value hfam O.matrix hC q.value.density hρ
  exact ⟨g.value,fam.cost+t.cost+q.cost+g.cost+5⟩

def response (S : DirectSDP.PolynomialService) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) : Counted (Matrix (Fin O.dim) (Fin O.dim) ℝ) :=
  if hO : State O then validResponse S a P hP O hO else ⟨0,0⟩

theorem validResponse_value (S : DirectSDP.PolynomialService) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) (hO : State O) :
    (validResponse S a P hP O hO).value = RectangularDirectSolver.value S.service a P hP O := by
  simp only [validResponse, DirectGammaArithmetic.compute_value, MSOwnerReport.family_value]
  rw [DirectSDPArithmetic.rectangular_density S (depth P) _ P.center (mixFamily P.atoms O.frame) _ O.matrix _ _ (theta P)
    (RectangularRidgePrimitiveParameters.weight_positive P.count_pos P.rectangular)]
  rw [RectangularDirectSolver.value,dif_pos hO]
  rfl

theorem response_value (S : DirectSDP.PolynomialService) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) (hO : State O) :
    (response S a P hP O).value = RectangularDirectSolver.value S.service a P hP O := by
  rw [response,dif_pos hO]
  exact validResponse_value S a P hP O hO

theorem rectangularCost_mono (S : DirectSDP.PolynomialService) {r m R M d : ℕ}
    (hr : r ≤ R) (hm : m ≤ M) :
    DirectSDPArithmetic.rectangularCost S r m d ≤ DirectSDPArithmetic.rectangularCost S R M d := by
  unfold DirectSDPArithmetic.rectangularCost DirectSDPArithmetic.rectangularSize
  gcongr

def queryBudget (S : DirectSDP.PolynomialService) (N d : ℕ) :=
  DirectSDPArithmetic.rectangularCost S N (d+1) d

def budget (S : DirectSDP.PolynomialService) (N d : ℕ) :=
  N*d*d*(8*N+4)+8*d+906+queryBudget S N d+20000*(N+d+1)^6

theorem response_cost (S : DirectSDP.PolynomialService) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) (hO : State O) :
    (response S a P hP O).cost ≤ budget S N d := by
  rw [response,dif_pos hO]
  unfold validResponse
  dsimp only
  have hk := hO.2.2
  have hm := RectangularRidgeTuning.depth_le N d P.count_pos
  have hf := MSOwnerReport.family_cost P.atoms O.frame
  have ht := RectangularRidgeResponseScalars.compute_cost (d:=d) P.count_pos
  have hq : ∀ (m : ℕ) (hm : 1 ≤ m) (H : Matrix (Fin d) (Fin d) ℂ)
      (A : Fin O.dim → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
      (C : Matrix (Fin O.dim) (Fin O.dim) ℝ) (hC : C.PosSemidef) (hd : 0 < d) (θ : ℝ),
      m ≤ d+1 → (DirectSDPArithmetic.rectangular S m hm H A hA C hC hd θ).cost ≤ queryBudget S N d := by
    intro m hm H A hA C hC hd θ hmle
    apply (DirectSDPArithmetic.rectangular_cost_le S m hm H A hA C hC hd θ).trans
    exact rectangularCost_mono S (by simpa using hk) hmle
  calc
    _ ≤ (O.dim*d*d*(8*N+4)+1)+(8*d+900)+queryBudget S N d+
        20000*(N+d+1)^6+5 := by
      apply Nat.add_le_add_right
      apply Nat.add_le_add
      · apply Nat.add_le_add
        · exact Nat.add_le_add hf.le ht
        · apply hq
          exact hm
      · apply (DirectGammaArithmetic.compute_cost _ _ _ _ _ _).trans
        exact (DirectGammaArithmetic.arithmeticBudget_polynomial O.dim d).trans (by gcongr)
    _ ≤ budget S N d := by
      have hm : O.dim*d*d*(8*N+4) ≤ N*d*d*(8*N+4) := by gcongr
      unfold budget
      omega

theorem queryBudget_polynomial (S : DirectSDP.PolynomialService) :
    NatPolynomialBound.Bounded (fun N d _ => queryBudget S N d) := by
  let e := 11+6*S.degree
  let c := 1000100+S.coefficient*1000^S.degree
  refine ⟨c*2^e,e,?_⟩
  intro N d k
  calc
    queryBudget S N d ≤ c*(N+(d+1)+d+1)^e :=
      DirectSDPArithmetic.rectangularCost_polynomial S N (d+1) d
    _ ≤ c*(2*(N+d+k+2))^e := by gcongr; omega
    _ = c*2^e*(N+d+k+2)^e := by rw [mul_pow]; ring

theorem budget_polynomial (S : DirectSDP.PolynomialService) :
    NatPolynomialBound.Bounded (fun N d _ => budget S N d) := by
  obtain ⟨c,e,h⟩ := queryBudget_polynomial S
  refine ⟨c+30000,e+6,?_⟩
  intro N d k
  let t := N+d+k+2
  have ht : 1 ≤ t := by dsimp [t]; omega
  have hN : N ≤ t := by dsimp [t]; omega
  have hd : d ≤ t := by dsimp [t]; omega
  have hNd : N+d+1 ≤ t := by dsimp [t]; omega
  have h0 : 1 ≤ t^6 := one_le_pow₀ ht
  have h1 : t ≤ t^6 := by simpa using Nat.pow_le_pow_right ht (show 1≤6 by omega)
  have h3 : t^3 ≤ t^6 := Nat.pow_le_pow_right ht (by omega)
  have h4 : t^4 ≤ t^6 := Nat.pow_le_pow_right ht (by omega)
  have hother : N*d*d*(8*N+4)+8*d+906+20000*(N+d+1)^6 ≤ 30000*t^6 := by
    calc
      _ ≤ t*t*t*(8*t+4)+8*t+906+20000*t^6 := by gcongr
      _ ≤ _ := by ring_nf; omega
  have he : t^e ≤ t^(e+6) := Nat.pow_le_pow_right ht (by omega)
  have h6 : t^6 ≤ t^(e+6) := Nat.pow_le_pow_right ht (by omega)
  have ha := Nat.mul_le_mul_left c he
  have hb := Nat.mul_le_mul_left 30000 h6
  have hq : queryBudget S N d ≤ c*t^e := h N d k
  change budget S N d ≤ (c+30000)*t^(e+6)
  unfold budget
  rw [Nat.add_mul]
  omega

end MatrixSpencer.RectangularDirectConcreteResponse
