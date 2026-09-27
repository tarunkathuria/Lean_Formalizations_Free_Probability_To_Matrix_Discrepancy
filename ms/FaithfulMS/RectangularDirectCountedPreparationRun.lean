import MatrixSpencer.RealRAMMSGammaTop
import FaithfulMS.RectangularDirectPreparation
import FaithfulMS.SquareDirectCountedTop

/-! Counted stored-support preparation with concrete cleanup/top/paid routines.
The response evaluator is the counted direct-density transport implementation.
The bounds below are local assembly hypotheses discharged from original input
by the polynomial parameter and direct-SDP compiler modules. -/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularDirectCountedPreparationRun
open RealRAM
open RealRAM.JacobiIteration (Counted Mat)
open MSManuscriptSupportedOwner (Owner)
open RectangularRidgePreparationData
variable {N d : ℕ} [Nonempty (Fin d)]
local instance ridgeCountedPreparationRunCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

structure Evaluator (P : Parameters N d) (R : Report P) where
  response : (O : Owner N) → Counted (Mat O.dim)
  response_value : ∀O : Owner N, State O → (response O).value=R.value O

structure Bounds (P : Parameters N d) (R : Report P) (E : Evaluator P R) (C J B : ℕ) : Prop where
  cleanup : ∀O : Owner N, State O →
    KSJacobiIteration.denominator O.dim*KSJacobiStep.offDiagonalEnergy O.matrix/
      (MSManuscriptCleanupParameters.tolerance O.dim floor)^2≤C
  response : ∀O : Owner N, State O → (E.response O).cost≤B

def direction (P : Parameters N d) (R : Report P) (E : Evaluator P R) (_J : ℕ) (O : Owner N) :
    Counted (Option (EuclideanSpace ℝ (Fin O.dim))) :=
  if hk : 0<O.dim then
    let r := E.response O
    let t := FaithfulMS.SquareDirectCountedTop.compute r.value (15*P.threshold/16) hk
    ⟨t.value, r.cost+t.cost+7⟩
  else ⟨none,2⟩

theorem direction_value (P : Parameters N d) (R : Report P) (E : Evaluator P R) (J : ℕ) (O : Owner N)
    (hO : State O) :
    (direction P R E J O).value=RectangularDirectPreparationRun.direction P R O := by
  by_cases hk : 0<O.dim
  · simp only [direction, dif_pos hk]
    rw [FaithfulMS.SquareDirectCountedTop.compute_value, E.response_value O hO]
    simp only [RectangularDirectPreparationRun.direction, dif_pos hk]
  · simp only [direction, RectangularDirectPreparationRun.direction, dif_neg hk]

theorem direction_cost (P : Parameters N d) (R : Report P) (E : Evaluator P R) (J B : ℕ) (O : Owner N)
    (hR : (E.response O).cost≤B) :
    (direction P R E J O).cost≤B+700*(J+1)*(O.dim+1)^3+3 := by
  unfold direction
  split_ifs with hk
  · have h := FaithfulMS.SquareDirectCountedTop.compute_cost (E.response O).value (15*P.threshold/16) hk
    have hpos : 1 ≤ (O.dim+1)^3 := Nat.one_le_pow _ _ (by omega)
    dsimp only
    nlinarith
  · simp only
    omega

/-- Paid size is stored input-only scalar data; the literal value is unchanged. -/
def run (P : Parameters N d) (R : Report P) (E : Evaluator P R) (C J : ℕ) (α : ℝ) :
    ℕ → Owner N → Counted (Option (Owner N×ℕ))
  | 0,_=>⟨none,1⟩
  | fuel+1,O=>
    let K:=MSCleanup.clean O floor C
    let t:=direction P R E J K.value
    match t.value with
    | none=>⟨some (K.value,0),K.cost+t.cost+5⟩
    | some u=>
      let p:=MSGammaTop.paid K.value α u
      let r:=run P R E C J α fuel p.value
      ⟨r.value.map (fun y=>(y.1,y.2+1)),K.cost+t.cost+p.cost+r.cost+6⟩

def roundBudget (N C J B : ℕ) : ℕ := 100000*(C+J+B+1)*(N+1)^5

theorem run_correct (P : Parameters N d) (hP : P.Valid) (R : Report P) (E : Evaluator P R)
    (C J B : ℕ) (hB : Bounds P R E C J B) (α : ℝ) (hα : α=paidSize P) (fuel : ℕ)
    (O : Owner N) (hO : State O) :
    (run P R E C J α fuel O).value=RectangularDirectPreparationRun.run P R fuel O ∧
    (run P R E C J α fuel O).cost≤fuel*roundBudget N C J B+1 := by
  subst α
  induction fuel generalizing O with
  | zero=>simp [run,RectangularDirectPreparationRun.run]
  | succ fuel ih=>
    let K:=MSCleanup.clean O floor C
    have hK : K.value=MSManuscriptSupportedOwner.clean O floor :=
      MSCleanup.clean_value O floor C (hB.cleanup O hO)
    obtain ⟨hKfloor,hKone,hKdim⟩:=RectangularRidgePreparationData.clean_state O hO
    have hKS : State K.value := by
      rw [hK]
      exact ⟨valid_mono _ hKfloor (by norm_num [floor]),hKone,hKdim⟩
    have ht:=direction_value P R E J K.value hKS 
    have hc:=MSCleanup.clean_cost O floor C
    have hd:=direction_cost P R E J B K.value (hB.response K.value hKS)
    have hkC : N+O.dim+1≤2*(N+1) := by have hh:=hO.2.2;omega
    have hkD : K.value.dim+1≤N+1 := by have hh:=hKS.2.2;omega
    have hc' : K.cost≤64000*(C+1)*(N+1)^5 := by
      calc _≤2000*(C+1)*(2*(N+1))^5 := hc.trans (by gcongr)
           _=_ := by ring
    have hd' : (direction P R E J K.value).cost≤B+700*(J+1)*(N+1)^5+3 := by
      have hh : (K.value.dim+1)^3≤(N+1)^5 :=
        (Nat.pow_le_pow_left hkD 3).trans (Nat.pow_le_pow_right (by omega) (by omega))
      exact hd.trans (by gcongr)
    have h1 : 1≤(N+1)^5 := Nat.one_le_pow _ _ (by omega)
    have hs : K.cost+(direction P R E J K.value).cost+100*(N+1)^5+10≤roundBudget N C J B := by
      unfold roundBudget
      nlinarith
    cases he : (direction P R E J K.value).value with
    | none=>
      dsimp only [K] at he
      have ho : RectangularDirectPreparationRun.direction P R (MSManuscriptSupportedOwner.clean O floor)=none := by
        rw [←hK,←ht,he]
      constructor
      · simp only [run,he,RectangularDirectPreparationRun.run,ho]
        rw [hK]
      · simp only [run,he]
        change K.cost+(direction P R E J K.value).cost+5≤_
        have hb : roundBudget N C J B≤(fuel+1)*roundBudget N C J B := by nlinarith
        omega
    | some u=>
      dsimp only [K] at he
      have hu : RectangularDirectPreparationRun.direction P R K.value=some u := ht.symm.trans he
      have hnorm:‖u‖=1 := (RectangularDirectPreparationRun.direction_some P hP R K.value hKS hu).1
      have hKfloor' : K.value.Valid (2*floor) := by rw [hK];exact hKfloor
      have hnext:= (RectangularDirectPreparationRun.continuation P hP R K.value hKfloor' hKS.2.1 hKS.2.2 hu).1
      let p:=MSGammaTop.paid K.value (paidSize P) u
      have hp:p.value=MSManuscriptSupportedOwner.paid K.value (paidSize P) (WithLp.ofLp u) :=
        MSGammaTop.paid_value _ _ _ hnorm
      have hpS : State p.value := hp.symm ▸ hnext
      obtain ⟨hi,hcost⟩:=ih p.value hpS
      have hpc:=MSGammaTop.paid_cost K.value (paidSize P) u
      have hside : N+K.value.dim+1≤2*(N+1) := by have hh:=hKS.2.2;omega
      have hpc' : p.cost≤100*(N+1)^5 := by
        calc _≤25*(2*(N+1))^2 := hpc.trans (by gcongr)
             _≤100*(N+1)^5 := by
               have hh : (N+1)^2≤(N+1)^5 := Nat.pow_le_pow_right (by omega) (by omega)
               nlinarith
      constructor
      · simp only [run,he]
        rw [hi,hp]
        rw [RectangularDirectPreparationRun.run,←hK,hu]
      · simp only [run,he]
        change K.cost+(direction P R E J K.value).cost+p.cost+(run P R E C J (paidSize P) fuel p.value).cost+6≤_
        nlinarith

def output (P : Parameters N d) (R : Report P) (E : Evaluator P R) (C J : ℕ) (α : ℝ) : Owner N → Counted (Option (Owner N×ℕ)) :=
  run P R E C J α (RectangularDirectPreparationRun.budget P)

theorem output_correct (P : Parameters N d) (hP : P.Valid) (R : Report P) (E : Evaluator P R)
    (C J B : ℕ) (hB : Bounds P R E C J B) (α : ℝ) (hα : α=paidSize P) (O : Owner N) (hO : State O) :
    (output P R E C J α O).value=RectangularDirectPreparationRun.output P R O ∧
    (output P R E C J α O).cost≤RectangularDirectPreparationRun.budget P*roundBudget N C J B+1 :=
  run_correct P hP R E C J B hB α hα _ O hO

end MatrixSpencer.RectangularDirectCountedPreparationRun
