import MatrixSpencer.RectangularRidgeEpochSetup
import MatrixSpencer.RectangularRidgePreparationWork

/-! Fully instantiated polynomial execution of the actual stopped epoch.
The original center is recomputed by its entrywise arithmetic circuit at
each preparation. The concrete finite response/preparation, live bookkeeping,
LDL movement and scalar setup are all charged. There is no supplied numerical
controller, derivative bound, preparation-success or walk-cost hypothesis. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeCompiledEpoch
open RealRAM.JacobiIteration (Counted)
open RectangularRidgeEpochInput RectangularRidgeEpochRun
open MSCountedSampler
variable {N d : ℕ} [Nonempty (Fin d)]
local instance ridgeCompiledEpochCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
attribute [local irreducible] RectangularRidgePreparation.prepare RectangularRidgePreparationRun.run
  RectangularRidgePreparationWork.prepare RectangularRidgeEpochRun.prepare

def parameters (c : Config N d) (x : EuclideanSpace ℝ (Fin N)) :
    Counted (RectangularRidgePreparationData.Parameters N d) :=
  let H:=RealRAM.MSOwnerReport.center ((0 : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) : Matrix (Fin d) (Fin d) ℂ) c.atoms (WithLp.ofLp x)
  let hH : H.value.IsHermitian := by
    rw [RealRAM.MSOwnerReport.center_epoch 0 c.atoms c.hermitian x]
    exact (center c x).property
  ⟨{center:=⟨H.value,hH⟩,atoms:=c.atoms,threshold:=threshold c,
    count_pos:=c.count_pos,rectangular:=c.rectangular},H.cost+10⟩

theorem parameters_value (c : Config N d) (x : EuclideanSpace ℝ (Fin N)) :
    (parameters c x).value=params c x := by
  simp only [parameters,RealRAM.MSOwnerReport.center_epoch 0 c.atoms c.hermitian x]
  rfl

theorem parameters_cost (c : Config N d) (x : EuclideanSpace ℝ (Fin N)) :
    (parameters c x).cost=d*d*(8*N+8)+11 := by
  simp only [parameters,RealRAM.MSOwnerReport.center_cost]

def optionRun (S : RectangularRidgeConvexValue.PolynomialSolver) (a : Fin d)
    (c : Config N d) (s : Certified c) :
    Counted (Option (MSManuscriptSupportedOwner.Owner N×ℕ)) :=
  let P:=parameters c s.val.point
  let hP : P.value.Valid := by rw [parameters_value];exact params_valid c _ s.property.1.regular.1
  let q:=RectangularRidgePreparationWork.prepare S a P.value hP s.val.owner
  ⟨q.value,P.cost+q.cost+2⟩

theorem optionRun_value (S : RectangularRidgeConvexValue.PolynomialSolver) (a : Fin d)
    (c : Config N d) (s : Certified c) :
    (optionRun S a c s).value=some (preparationResult S.solver a c s) := by
  simp only [optionRun,parameters_value]
  rw [(RectangularRidgePreparationWork.prepare_correct S a (params c s.val.point)
    (params_valid c _ s.property.1.regular.1) s.val.owner
    ⟨s.property.1.owner_valid,s.property.1.owner_le_one,s.property.1.dim_le.trans (live_le c)⟩).1]
  exact preparationResult_eq S.solver a c s

theorem optionRun_cost (S : RectangularRidgeConvexValue.PolynomialSolver) (a : Fin d)
    (c : Config N d) (s : Certified c) :
    (optionRun S a c s).cost≤RectangularRidgePreparationWork.budget S N d+d*d*(8*N+8)+13 := by
  have hp:=(RectangularRidgePreparationWork.prepare_correct S a (params c s.val.point)
    (params_valid c _ s.property.1.regular.1) s.val.owner
    ⟨s.property.1.owner_valid,s.property.1.owner_le_one,s.property.1.dim_le.trans (live_le c)⟩).2
  simp only [optionRun,parameters_value,parameters_cost]
  omega

private def extract {α : Type*} (q : Counted (Option α)) (hq : q.value.isSome=true) : Counted α :=
  ⟨q.value.get hq,q.cost+1⟩
private theorem extract_value {α : Type*} (q : Counted (Option α)) (hq : q.value.isSome=true)
    (y : α) (he : q.value=some y) : (extract q hq).value=y := by
  simp only [extract,he,Option.get_some]
private theorem extract_cost {α : Type*} (q : Counted (Option α)) (hq : q.value.isSome=true) :
    (extract q hq).cost=q.cost+1 := rfl

def pairRun (S : RectangularRidgeConvexValue.PolynomialSolver) (a : Fin d)
    (c : Config N d) (s : Certified c) : Counted (MSManuscriptSupportedOwner.Owner N×ℕ) :=
  extract (optionRun S a c s) (by rw [optionRun_value];rfl)

theorem pairRun_value (S : RectangularRidgeConvexValue.PolynomialSolver) (a : Fin d)
    (c : Config N d) (s : Certified c) :
    (pairRun S a c s).value=preparationResult S.solver a c s :=
  extract_value (optionRun S a c s) _ _ (optionRun_value S a c s)

theorem pairRun_cost (S : RectangularRidgeConvexValue.PolynomialSolver) (a : Fin d)
    (c : Config N d) (s : Certified c) :
    (pairRun S a c s).cost=(optionRun S a c s).cost+1 := extract_cost _ _

private def attach (c : Config N d) (x : MSManuscriptNumericalEpochLedger.State N)
    (y : Certified c) (he : x=y.val) : Certified c := ⟨x,he ▸ y.property⟩

def preparation (S : RectangularRidgeConvexValue.PolynomialSolver) (a : Fin d)
    (c : Config N d) (s : Certified c) : Counted (Certified c) :=
  let p:=pairRun S a c s
  let y:=RectangularRidgeStateWork.afterPrepare (params c s.val.point) s.val p.value
  let he : y.value=(prepare S.solver a c s).val := by
    rw [RectangularRidgeStateWork.afterPrepare_value,pairRun_value]
    exact (prepare_val S.solver a c s).symm
  ⟨attach c y.value (prepare S.solver a c s) he,p.cost+y.cost+1⟩

theorem preparation_value (S : RectangularRidgeConvexValue.PolynomialSolver) (a : Fin d)
    (c : Config N d) (s : Certified c) :
    (preparation S a c s).value=prepare S.solver a c s := by
  apply Subtype.ext
  change (RectangularRidgeStateWork.afterPrepare (params c s.val.point) s.val
    (pairRun S a c s).value).value=_
  rw [RectangularRidgeStateWork.afterPrepare_value,pairRun_value]
  exact (prepare_val S.solver a c s).symm

def preparationBudget (S : RectangularRidgeConvexValue.PolynomialSolver) (N d : ℕ) : ℕ :=
  RectangularRidgePreparationWork.budget S N d+d*d*(8*N+8)+14000*(N+1)^3+15

theorem preparation_cost (S : RectangularRidgeConvexValue.PolynomialSolver) (a : Fin d)
    (c : Config N d) (s : Certified c) :
    (preparation S a c s).cost≤preparationBudget S N d := by
  have ho:=optionRun_cost S a c s
  have hy:=RectangularRidgeStateWork.afterPrepare_cost (params c s.val.point) s.val
    (pairRun S a c s).value
  have hs:=s.property.1.dim_le.trans (live_le c)
  have hp : (pairRun S a c s).value.1.dim≤N := by
    rw [pairRun_value,←prepare_owner S.solver a c s]
    exact (prepare S.solver a c s).property.1.dim_le.trans (live_le c)
  have hpow : (N+s.val.owner.dim+(pairRun S a c s).value.1.dim+1)^3≤27*(N+1)^3 := by
    calc _≤(3*(N+1))^3 := Nat.pow_le_pow_left (by omega) _
      _=_ := by ring
  change (pairRun S a c s).cost+
    (RectangularRidgeStateWork.afterPrepare (params c s.val.point) s.val
      (pairRun S a c s).value).cost+1≤_
  rw [pairRun_cost]
  dsimp only [preparationBudget]
  omega

def routines (S : RectangularRidgeConvexValue.PolynomialSolver) (a : Fin d) (c : Config N d) :
    RectangularRidgeEpochWork.Routines S.solver a c where
  prepare:=preparation S a c
  prepare_value:=preparation_value S a c
  movement:=RectangularRidgeMovementWork.implementation c

def budget (S : RectangularRidgeConvexValue.PolynomialSolver) (N d : ℕ) : ℕ :=
  (2^1080*(d+N+2)^208+1)*
    (RectangularRidgeEpochWork.stepBudget N (preparationBudget S N d) (200000*(N+1)^5)+2)+
      120*(N+1)^3+10*d+30005

def implementation (S : RectangularRidgeConvexValue.PolynomialSolver) (a : Fin d)
    (c : Config N d) : Implementation (output S.solver a c) :=
  overhead (RectangularRidgeEpochWork.output S.solver a c (routines S a c))
    ((RectangularRidgeEpochSetup.setup c).cost+2)

/-- Every execution, including an unfavorable draw, obeys this fixed
polynomial bound and uses at most the literal movement-cap many random draws. -/
theorem implementation_bounded (S : RectangularRidgeConvexValue.PolynomialSolver) (a : Fin d)
    (c : Config N d) : Bounded (implementation S a c) (budget S N d)
      (2^1080*(d+N+2)^208+1) := by
  have hb:=RectangularRidgeEpochWork.output_bounded S.solver a c (routines S a c)
    (preparationBudget S N d) (200000*(N+1)^5) (preparation_cost S a c)
    (RectangularRidgeMovementWork.implementation_bounded c)
  have hh:=overhead_bounded _ ((RectangularRidgeEpochSetup.setup c).cost+2) hb
  have hs:=RectangularRidgeEpochSetup.setup_cost c
  rw [count_eq] at hh
  intro z out cost draws he
  have h:=hh z out cost draws he
  dsimp only [budget]
  constructor <;> omega

end MatrixSpencer.RectangularRidgeCompiledEpoch
