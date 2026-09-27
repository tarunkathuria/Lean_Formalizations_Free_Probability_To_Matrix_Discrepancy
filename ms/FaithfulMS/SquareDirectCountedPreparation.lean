import MatrixSpencer.RealRAMMSGammaTop
import FaithfulMS.SquareDirectPreparation
import FaithfulMS.SquareDirectCountedTop

/-! Counted stored-support preparation with concrete cleanup/top/paid routines.
The response evaluator is a separate counted direct-density implementation.
The bounds below are local assembly hypotheses discharged from original input
by the polynomial parameter and direct-SDP compiler modules. -/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
open MatrixSpencer
namespace FaithfulMS.SquareDirectCountedPreparation
open RealRAM
open RealRAM.JacobiIteration (Counted Mat)
open MSManuscriptSupportedOwner (Owner)
open MSManuscriptSupportedGamma (Parameters)
open MSManuscriptSupportedPreparation (State)
variable [SquareDirectOracle.Oracle]
variable {N d : ℕ}
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

structure Evaluator (P : Parameters N d) where
  response : (O : Owner N) → Counted (Mat O.dim)
  response_value : ∀O, State P O → (response O).value=SquareDirectGamma.response P O

structure Bounds (P : Parameters N d) (E : Evaluator P) (C J R : ℕ) : Prop where
  cleanup : ∀O, State P O →
    KSJacobiIteration.denominator O.dim*KSJacobiStep.offDiagonalEnergy O.matrix/
      (MSManuscriptCleanupParameters.tolerance O.dim P.floor)^2≤C
  response : ∀O, State P O → (E.response O).cost≤R

def direction (P : Parameters N d) (E : Evaluator P) (J : ℕ) (O : Owner N) :
    Counted (Option (EuclideanSpace ℝ (Fin O.dim))) :=
  if hk : 0<O.dim then
    let r:=E.response O
    let t:=SquareDirectCountedTop.compute r.value P.threshold hk
    ⟨t.value,r.cost+t.cost+3⟩
  else ⟨none,2⟩

theorem direction_value (P : Parameters N d) (E : Evaluator P) (J : ℕ) (O : Owner N)
    (hO : State P O) :
    (direction P E J O).value=SquareDirectGamma.direction P O := by
  by_cases hk : 0<O.dim
  · simp only [direction,dif_pos hk]
    rw [SquareDirectCountedTop.compute_value, E.response_value O hO]
    simp only [SquareDirectGamma.direction,dif_pos hk]
  · simp only [direction,SquareDirectGamma.direction,dif_neg hk]

theorem direction_cost (P : Parameters N d) (E : Evaluator P) (J R : ℕ) (O : Owner N)
    (hR : (E.response O).cost≤R) :
    (direction P E J O).cost≤R+700*(J+1)*(O.dim+1)^3+3 := by
  unfold direction
  split_ifs with hk
  · have h:=SquareDirectCountedTop.compute_cost (E.response O).value P.threshold hk
    dsimp only
    have hm : (O.dim+1)^3 ≤ (J+1)*(O.dim+1)^3 := by nlinarith
    nlinarith
  · simp only
    omega

/-- Paid size is stored input-only scalar data; the literal value is unchanged. -/
def run (P : Parameters N d) (E : Evaluator P) (C J : ℕ) :
    ℕ → Owner N → Counted (Option (Owner N×ℕ))
  | 0,_=>⟨none,1⟩
  | fuel+1,O=>
    let K:=MSCleanup.clean O P.floor C
    let t:=direction P E J K.value
    match t.value with
    | none=>⟨some (K.value,0),K.cost+t.cost+5⟩
    | some u=>
      let p:=MSGammaTop.paid K.value (MSManuscriptSupportedPaid.paidSize P) u
      let r:=run P E C J fuel p.value
      ⟨r.value.map (fun y=>(y.1,y.2+1)),K.cost+t.cost+p.cost+r.cost+6⟩

def roundBudget (N C J R : ℕ) : ℕ := 100000*(C+J+R+1)*(N+1)^5

theorem run_correct (P : Parameters N d) (hP : P.Valid) (E : Evaluator P)
    (C J R : ℕ) (hB : Bounds P E C J R) (fuel : ℕ)
    (O : Owner N) (hO : State P O) :
    (run P E C J fuel O).value=SquareDirectPreparation.run P fuel O ∧
    (run P E C J fuel O).cost≤fuel*roundBudget N C J R+1 := by
  induction fuel generalizing O with
  | zero=>simp [run,SquareDirectPreparation.run]
  | succ fuel ih=>
    let K:=MSCleanup.clean O P.floor C
    have hK : K.value=MSManuscriptSupportedOwner.clean O P.floor :=
      MSCleanup.clean_value O P.floor C (hB.cleanup O hO)
    obtain ⟨hKfloor,hKone,hKdim⟩:=MSManuscriptSupportedPreparation.clean_state P hP O hO
    have hKS : State P K.value := by
      rw [hK]
      exact ⟨MSManuscriptSupportedPaid.valid_mono _ hKfloor (by linarith [hP.2.2.2.1]),hKone,hKdim⟩
    have ht:=direction_value P E J K.value hKS
    have hc:=MSCleanup.clean_cost O P.floor C
    have hd:=direction_cost P E J R K.value (hB.response K.value hKS)
    have hkC : N+O.dim+1≤2*(N+1) := by have hh:=hO.2.2;omega
    have hkD : K.value.dim+1≤N+1 := by have hh:=hKS.2.2;omega
    have hc' : K.cost≤64000*(C+1)*(N+1)^5 := by
      calc _≤2000*(C+1)*(2*(N+1))^5 := hc.trans (by gcongr)
           _=_ := by ring
    have hd' : (direction P E J K.value).cost≤R+700*(J+1)*(N+1)^5+3 := by
      have hh : (K.value.dim+1)^3≤(N+1)^5 :=
        (Nat.pow_le_pow_left hkD 3).trans (Nat.pow_le_pow_right (by omega) (by omega))
      exact hd.trans (by gcongr)
    have h1 : 1≤(N+1)^5 := Nat.one_le_pow _ _ (by omega)
    have hs : K.cost+(direction P E J K.value).cost+100*(N+1)^5+10≤roundBudget N C J R := by
      unfold roundBudget
      nlinarith
    cases he : (direction P E J K.value).value with
    | none=>
      dsimp only [K] at he
      have ho : SquareDirectGamma.direction P (MSManuscriptSupportedOwner.clean O P.floor)=none := by
        rw [←hK,←ht,he]
      constructor
      · simp only [run,he,SquareDirectPreparation.run,ho]
        rw [hK]
      · simp only [run,he]
        change K.cost+(direction P E J K.value).cost+5≤_
        have hb : roundBudget N C J R≤(fuel+1)*roundBudget N C J R := by nlinarith
        omega
    | some u=>
      dsimp only [K] at he
      have hu : SquareDirectGamma.direction P K.value=some u := ht.symm.trans he
      have hnorm:‖u‖=1 := (SquareDirectGamma.direction_some P hP K.value hKS.1 hKS.2.1 hu).1
      have hKfloor' : K.value.Valid (2*P.floor) := by rw [hK];exact hKfloor
      have hnext:= (SquareDirectPreparation.continuation P hP K.value hKfloor' hKS.2.1 hKS.2.2 hu).1
      let p:=MSGammaTop.paid K.value (MSManuscriptSupportedPaid.paidSize P) u
      have hp:p.value=MSManuscriptSupportedOwner.paid K.value (MSManuscriptSupportedPaid.paidSize P) (WithLp.ofLp u) :=
        MSGammaTop.paid_value _ _ _ hnorm
      have hpS : State P p.value := hp.symm ▸ hnext
      obtain ⟨hi,hcost⟩:=ih p.value hpS
      have hpc:=MSGammaTop.paid_cost K.value (MSManuscriptSupportedPaid.paidSize P) u
      have hside : N+K.value.dim+1≤2*(N+1) := by have hh:=hKS.2.2;omega
      have hpc' : p.cost≤100*(N+1)^5 := by
        calc _≤25*(2*(N+1))^2 := hpc.trans (by gcongr)
             _≤100*(N+1)^5 := by
               have hh : (N+1)^2≤(N+1)^5 := Nat.pow_le_pow_right (by omega) (by omega)
               nlinarith
      constructor
      · simp only [run,he]
        rw [hi,hp]
        rw [SquareDirectPreparation.run,←hK,hu]
      · simp only [run,he]
        change K.cost+(direction P E J K.value).cost+p.cost+(run P E C J fuel p.value).cost+6≤_
        nlinarith

def output (P : Parameters N d) (E : Evaluator P) (C J : ℕ) : Owner N → Counted (Option (Owner N×ℕ)) :=
  run P E C J (MSManuscriptSupportedPreparation.budget P)

theorem output_correct (P : Parameters N d) (hP : P.Valid) (E : Evaluator P)
    (C J R : ℕ) (hB : Bounds P E C J R) (O : Owner N) (hO : State P O) :
    (output P E C J O).value=SquareDirectPreparation.output P O ∧
    (output P E C J O).cost≤MSManuscriptSupportedPreparation.budget P*roundBudget N C J R+1 :=
  run_correct P hP E C J R hB _ O hO

end FaithfulMS.SquareDirectCountedPreparation
