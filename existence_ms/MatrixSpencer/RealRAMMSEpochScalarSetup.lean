import MatrixSpencer.RealRAMMSScalarFormulas

/-! Counted scalar preprocessing for one actual square-MS epoch. Entry
arithmetic supplies the center bound, finite tables supply both derivative
budgets, and the fixed primitive circuit supplies the exact movement mesh,
paid-cut size, and the two real arguments for the integer loops. -/
open Matrix
noncomputable section
namespace MatrixSpencer.RealRAM.MSEpochScalarSetup
open JacobiIteration (Counted)
open MSManuscriptNumericalEpochRun
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
variable {m d : ℕ}

structure Data where
  center : ℝ
  curvature : ℝ
  fourth : ℝ
  scalar : Fin 14→ℝ

def setup (c : Config m d) (N : ℕ) : Counted Data :=
  let R:=MSParameterTables.center (c.offset:Matrix (Fin d) (Fin d) ℂ) m
  let C:=MSParameterTables.curvature R.value m d
  let F:=MSParameterTables.fourth R.value m d
  let s:=MSScalarFormulas.compute m 1 N d 0 C.value F.value
  ⟨⟨R.value,C.value,F.value,s.value⟩,R.cost+C.cost+F.cost+s.cost+29⟩

def costBound (m d : ℕ) := 20*(d+1)^2+4000022*(m+1)+100030

theorem setup_cost (c : Config m d) (N : ℕ) : (setup c N).cost≤costBound m d := by
  have hR := MSParameterTables.center_cost d
  have hC := MSParameterTables.curvature_cost
    (MSParameterTables.center (c.offset:Matrix (Fin d) (Fin d) ℂ) m).value m d
  have hF := MSParameterTables.fourth_cost
    (MSParameterTables.center (c.offset:Matrix (Fin d) (Fin d) ℂ) m).value m d
  have hs := MSScalarFormulas.compute_cost m 1 N d 0
    (MSParameterTables.curvature (MSParameterTables.center (c.offset:Matrix (Fin d) (Fin d) ℂ) m).value m d).value
    (MSParameterTables.fourth (MSParameterTables.center (c.offset:Matrix (Fin d) (Fin d) ℂ) m).value m d).value
  dsimp only [setup,costBound,MSParameterTables.center] at *
  omega

theorem center_value (c : Config m d) (N : ℕ) :
    (setup c N).value.center=MSManuscriptEpochInput.centerCap c.offset (N:=m) :=
  MSParameterTables.center_value _ m

theorem curvature_value (c : Config m d) (N : ℕ)
    (hθ : c.regularizer=1) (hδ : c.floor=1/8192)
    (s : MSManuscriptNumericalEpochLedger.State m) :
    (setup c N).value.curvature=MSManuscriptSupportedPaid.curvatureBudget (params c s) := by
  change (MSParameterTables.curvature _ m d).value=_
  rw [MSParameterTables.curvature_value,MSParameterTables.center_value]
  simp only [MSManuscriptSupportedPaid.curvatureBudget,params,MSManuscriptEpochInput.params,
    MSManuscriptEpochInput.centerCap,hθ,hδ]

theorem fourth_value (c : Config m d) (N : ℕ)
    (hθ : c.regularizer=1) (hδ : c.floor=1/8192) :
    (setup c N).value.fourth=MSManuscriptNumericalWalkBudget.fourthBudget c := by
  change (MSParameterTables.fourth _ m d).value=_
  rw [MSParameterTables.fourth_value,MSParameterTables.center_value]
  simp only [MSManuscriptNumericalWalkBudget.fourthBudget,MSManuscriptEpochInput.centerCap,hθ,hδ]

theorem paid_value (c : Config m d) (N : ℕ)
    (hθ : c.regularizer=1) (hδ : c.floor=1/8192)
    (ht : c.threshold=4096/Real.sqrt (m:ℝ))
    (s : MSManuscriptNumericalEpochLedger.State m) :
    (setup c N).value.scalar 5=MSManuscriptSupportedPaid.paidSize (params c s) := by
  change MSScalarFormulas.paid.eval _=_
  rw [MSScalarFormulas.paid_eval]
  change min ((1/8192)/4) ((4096/Real.sqrt (m:ℝ))/(4*(setup c N).value.curvature))=_
  rw [curvature_value c N hθ hδ s]
  simp only [MSManuscriptSupportedPaid.paidSize,params,MSManuscriptEpochInput.params,hδ,ht]

theorem mesh_value (c : Config m d) (N : ℕ)
    (hθ : c.regularizer=1) (hδ : c.floor=1/8192)
    (hmargin : c.margin=1/(1000*((N:ℝ)+1))) (hdrift : c.driftError=1/10000) :
    (setup c N).value.scalar 6=mesh c := by
  change MSScalarFormulas.mesh.eval _=_
  rw [MSScalarFormulas.mesh_eval]
  change min (min ((1/(1000*((N:ℝ)+1)))/Real.sqrt ((m:ℝ)+1))
    (min (1/2) (min (MSManuscriptMatchedInterval.radius (1/8192)/2)
      (Real.sqrt (24*(1/10000)/(setup c N).value.fourth)))))
      (Real.sqrt (MSManuscriptNumericalEpochLedger.timeLimit/2))=_
  rw [fourth_value c N hθ hδ]
  simp only [mesh,baseMesh,MSManuscriptEpochInput.mesh,MSManuscriptPreparedMovement.stepSize,
    MSManuscriptEpochInput.params,MSManuscriptNumericalWalkBudget.fourthBudget,hmargin,hdrift,hθ,hδ]

theorem preparationArgument_value (c : Config m d) (N : ℕ)
    (hθ : c.regularizer=1) (hδ : c.floor=1/8192)
    (ht : c.threshold=4096/Real.sqrt (m:ℝ))
    (s : MSManuscriptNumericalEpochLedger.State m) :
    (setup c N).value.scalar 7=(m:ℝ)/MSManuscriptSupportedPaid.paidSize (params c s) := by
  change MSScalarFormulas.preparationArgument.eval _=_
  change (m:ℝ)/(setup c N).value.scalar 5=_
  rw [paid_value c N hθ hδ ht s]

theorem movementArgument_value (c : Config m d) (N : ℕ)
    (hθ : c.regularizer=1) (hδ : c.floor=1/8192)
    (hmargin : c.margin=1/(1000*((N:ℝ)+1))) (hdrift : c.driftError=1/10000) :
    (setup c N).value.scalar 8=MSManuscriptNumericalEpochLedger.timeLimit/(mesh c)^2 := by
  change MSScalarFormulas.movementArgument.eval _=_
  simp only [MSScalarFormulas.movementArgument,MSScalarFormulas.div_eval,MSScalarFormulas.mul_eval,
    MSScalarFormulas.c_eval,MSScalarFormulas.sq_eval]
  norm_num only [Nat.cast_ofNat]
  change 1/(1539*((setup c N).value.scalar 6)^2)=_
  rw [mesh_value c N hθ hδ hmargin hdrift]
  unfold MSManuscriptNumericalEpochLedger.timeLimit
  ring

/-- Each nonconstant scalar subroutine has its actual safe primitive trace. -/
theorem scalar_execution (c : Config m d) (N : ℕ) (i : Fin 14) :
    Expr.Executes
      (MSScalarFormulas.input m 1 N d 0 (setup c N).value.curvature (setup c N).value.fourth)
      (MSScalarFormulas.circuit.output i) ((setup c N).value.scalar i)
      (MSScalarFormulas.circuit.output i).cost := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp c.dimension_pos
  have hR : 0≤(MSParameterTables.center (c.offset:Matrix (Fin d) (Fin d) ℂ) m).value := by
    rw [MSParameterTables.center_value]
    exact (add_pos_of_pos_of_nonneg (KSOwnerInputBounds.matrixBound_pos _) (Nat.cast_nonneg m)).le
  have hC : 0<(setup c N).value.curvature := by
    change 0<(MSParameterTables.curvature _ m d).value
    rw [MSParameterTables.curvature_value]
    have hsum : 0≤∑ k : Fin (m+1), MSManuscriptGammaInputBoundScaled.secondCap k d
        (MSParameterTables.center (c.offset:Matrix (Fin d) (Fin d) ℂ) m).value 1 (1/8192) m :=
      Finset.sum_nonneg (fun k _ => MSManuscriptGammaInputBoundScaled.secondCap_nonneg hR (by norm_num))
    linarith
  have hF : 0<(setup c N).value.fourth := by
    change 0<(MSParameterTables.fourth _ m d).value
    rw [MSParameterTables.fourth_value]
    exact MSManuscriptMovementDrift.uniformBudget_pos hR (by norm_num)
  exact MSScalarFormulas.execution m 1 N d 0 _ _ (by have h:=c.count_large; omega)
    (by decide) c.dimension_pos (by norm_num) hC hF i

end MatrixSpencer.RealRAM.MSEpochScalarSetup
