import MatrixSpencer.RealRAMMSEpochScalarSetup
import MatrixSpencer.RealRAMMSLoopCapSetup
import MatrixSpencer.RealRAMStrictCeiling
import MatrixSpencer.RealRAMJacobiRayleigh
import MatrixSpencer.MSManuscriptPolynomialQueryFactory
import MatrixSpencer.MSManuscriptFactoryPolynomialMesh

/-! The actual preparation ceiling and movement floor-plus-one are computed
by bounded comparison loops. Both scalar arguments and the polynomial loop
caps are themselves produced by primitive circuits. -/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RealRAM.MSEpochLoops
open JacobiIteration (Counted)
open MSManuscriptNumericalEpochRun
variable {m d : ℕ}
set_option maxHeartbeats 1800000
set_option maxRecDepth 6000

section Strict
attribute [local instance] Classical.propDecidable

def strictLoop (x : ℝ) : ℕ→ Counted ℕ
  | 0=>⟨0,3⟩
  | n+1=>let p:=strictLoop x n;⟨if (p.value:ℝ)≤x then p.value+1 else p.value,p.cost+8⟩

theorem strictLoop_value (x : ℝ) (hx : 0≤x) (n : ℕ) :
    (strictLoop x n).value=min n (⌊x⌋₊+1) := by
  induction n with
  | zero=>simp [strictLoop]
  | succ n ih=>
    simp only [strictLoop,ih]
    by_cases hn : ⌊x⌋₊+1≤n
    · rw [min_eq_right hn,min_eq_right (by omega : ⌊x⌋₊+1≤n+1),
        if_neg (by simpa only [Nat.cast_add,Nat.cast_one] using (not_le.mpr (Nat.lt_floor_add_one x)))]
    · have hle : n+1≤⌊x⌋₊+1 := by omega
      rw [min_eq_left (by omega : n≤⌊x⌋₊+1),min_eq_left hle,
        if_pos ((Nat.le_floor_iff hx).mp (by omega : n≤⌊x⌋₊))]

theorem strictLoop_exact (x : ℝ) (hx : 0≤x) (cap : ℕ) (hcap : x<cap) :
    (strictLoop x cap).value=⌊x⌋₊+1 := by
  rw [strictLoop_value x hx,min_eq_right (by have := (Nat.floor_lt hx).mpr hcap;omega)]

theorem strictLoop_cost (x : ℝ) (cap : ℕ) : (strictLoop x cap).cost=8*cap+3 := by
  induction cap with
  | zero=>rfl
  | succ n ih=>simp only [strictLoop,ih];omega

theorem strictLoop_program (x : ℝ) (hx : 0≤x) (cap : ℕ) :
    ((strictLoop x cap).value:ℝ)=
      (StrictCeiling.program cap).run (fun r=>match r with | .argument=>x | .counter=>0) .counter := by
  rw [strictLoop_value x hx]
  symm
  change (StrictCeiling.step.run)^[cap]
    (Function.update (fun r=>match r with | .argument=>x | .counter=>0)
      .counter ((0:ℚ):ℝ)) .counter=_
  have hz : (Function.update (fun r : Ceiling.Register=>match r with | .argument=>x | .counter=>0)
      .counter ((0:ℚ):ℝ)) .counter=0 := by simp
  simpa using StrictCeiling.iterate_counter cap _ hz (by simpa using hx)

end Strict

structure Data where
  scalar : MSEpochScalarSetup.Data
  preparation : ℕ
  movement : ℕ

def setup (c : Config m d) (N : ℕ) : Counted Data :=
  let scalar:=MSEpochScalarSetup.setup c N
  let caps:=MSLoopCapSetup.compute N d
  let prep:=JacobiRayleigh.ceilLoop (scalar.value.scalar 7) (caps.value .preparation)
  let moves:=strictLoop (scalar.value.scalar 8) (caps.value .movement)
  ⟨⟨scalar.value,prep.value+1,moves.value⟩,scalar.cost+caps.cost+prep.cost+moves.cost+5⟩

def costBound (m N d : ℕ) : ℕ :=
  MSEpochScalarSetup.costBound m d+1000000+
    8*MSManuscriptPolynomialQueryParameters.preparation N d+8*MSLoopCapSetup.movementCap N d+11

theorem setup_cost (c : Config m d) (N : ℕ) : (setup c N).cost≤costBound m N d := by
  have hs:=MSEpochScalarSetup.setup_cost c N
  have hc:=MSLoopCapSetup.compute_cost N d
  simp only [setup,MSLoopCapSetup.compute_value,MSLoopCapSetup.originalOutputs,
    JacobiRayleigh.ceilLoop_cost,strictLoop_cost,costBound]
  omega

theorem scalar_value (c : Config m d) (N : ℕ) :
    (setup c N).value.scalar=(MSEpochScalarSetup.setup c N).value := rfl

theorem preparation_value (c : Config m d) (N : ℕ)
    (hθ : c.regularizer=1) (hδ : c.floor=1/8192)
    (ht : c.threshold=4096/Real.sqrt (m:ℝ))
    (s : MSManuscriptNumericalEpochLedger.State m)
    (hcap : (m:ℝ)/MSManuscriptSupportedPaid.paidSize (params c s)≤
      MSManuscriptPolynomialQueryParameters.preparation N d) :
    (setup c N).value.preparation=MSManuscriptSupportedPreparation.budget (params c s) := by
  simp only [setup,MSLoopCapSetup.compute_value,MSLoopCapSetup.originalOutputs,
    MSEpochScalarSetup.preparationArgument_value c N hθ hδ ht s,
    JacobiRayleigh.ceilLoop_exact _ _ hcap]
  rfl

theorem movement_value (c : Config m d) (N : ℕ)
    (hθ : c.regularizer=1) (hδ : c.floor=1/8192)
    (hmargin : c.margin=1/(1000*((N:ℝ)+1))) (hdrift : c.driftError=1/10000)
    (hcap : MSManuscriptNumericalEpochLedger.timeLimit/(mesh c)^2<MSLoopCapSetup.movementCap N d) :
    (setup c N).value.movement=count c := by
  have hx : 0≤MSManuscriptNumericalEpochLedger.timeLimit/(mesh c)^2 := by
    exact div_nonneg (by norm_num [MSManuscriptNumericalEpochLedger.timeLimit]) (sq_nonneg _)
  simp only [setup,MSLoopCapSetup.compute_value,MSLoopCapSetup.originalOutputs,
    MSEpochScalarSetup.movementArgument_value c N hθ hδ hmargin hdrift,
    strictLoop_exact _ hx _ hcap]
  rfl

section Original
open PhaseRestriction MSManuscriptFactoryPolynomialMovementBounds
variable {ι n : Type*} [Fintype ι] [LinearOrder ι] [Fintype n] [DecidableEq n]
  [Nonempty (Fin d)]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
variable (e : Fin d ≃ n) (A : ι→Matrix n n ℂ)
  (hA : ∀i,(A i).IsHermitian) (hN : ∀i,‖A i‖≤1)
  (x : EuclideanSpace ℝ ι)
  (y : MSManuscriptPhase.Point (ι:=Live x) (signingEpsilon ι))
  (hl : 32≤Fintype.card (Live y.val)) (hd : 0<d)

abbrev originalConfig := MSManuscriptPolynomialQueryFactory.config e A hA hN x y hl hd

def original : Counted Data := setup (originalConfig e A hA hN x y hl hd) (Fintype.card ι)

theorem original_preparation
    (s : Certified (originalConfig e A hA hN x y hl hd)) :
    (original e A hA hN x y hl hd).value.preparation=
      MSManuscriptSupportedPreparation.budget (params (originalConfig e A hA hN x y hl hd) s.val) := by
  apply preparation_value _ _ rfl rfl rfl s.val
  have hb:=MSManuscriptPolynomialQueryFactory.preparation_budget_le e A hA hN x y hl hd s
  have hr:=(Nat.le_ceil ((Fintype.card (Live y.val):ℝ)/
    MSManuscriptSupportedPaid.paidSize (params (originalConfig e A hA hN x y hl hd) s.val)))
  have hb' : (MSManuscriptSupportedPreparation.budget
      (params (originalConfig e A hA hN x y hl hd) s.val):ℝ)≤
        (MSManuscriptPolynomialQueryParameters.preparation (Fintype.card ι) d:ℝ) := Nat.cast_le.mpr hb
  unfold MSManuscriptSupportedPreparation.budget MSManuscriptPreparationRun.budget at hb'
  push_cast at hb'
  linarith

theorem original_movement :
    (original e A hA hN x y hl hd).value.movement=count (originalConfig e A hA hN x y hl hd) := by
  apply movement_value _ _ rfl rfl rfl rfl
  have hi:=MSManuscriptFactoryPolynomialMesh.mesh_inverse_square_le e A hA hN x y hl hd
  have hc : MSManuscriptNumericalEpochLedger.timeLimit/(mesh (originalConfig e A hA hN x y hl hd))^2≤
      1/(mesh (originalConfig e A hA hN x y hl hd))^2 :=
    div_le_div_of_nonneg_right (by norm_num [MSManuscriptNumericalEpochLedger.timeLimit]) (sq_nonneg _)
  rw [MSLoopCapSetup.movementCap_cast]
  linarith

theorem original_mesh :
    (original e A hA hN x y hl hd).value.scalar.scalar 6=
      mesh (originalConfig e A hA hN x y hl hd) :=
  MSEpochScalarSetup.mesh_value _ _ rfl rfl rfl rfl

theorem original_paid (s : MSManuscriptNumericalEpochLedger.State (Fintype.card (Live y.val))) :
    (original e A hA hN x y hl hd).value.scalar.scalar 5=
      MSManuscriptSupportedPaid.paidSize (params (originalConfig e A hA hN x y hl hd) s) :=
  MSEpochScalarSetup.paid_value _ _ rfl rfl rfl s

theorem original_movement_le : count (originalConfig e A hA hN x y hl hd)≤
    MSLoopCapSetup.movementCap (Fintype.card ι) d := by
  have h:=MSManuscriptFactoryPolynomialMovementBounds.count_le e A hA hN x y hl hd
  rw [←MSLoopCapSetup.movementCap_cast] at h
  exact_mod_cast h

theorem original_preparation_le
    (s : Certified (originalConfig e A hA hN x y hl hd)) :
    MSManuscriptSupportedPreparation.budget (params (originalConfig e A hA hN x y hl hd) s.val)≤
      MSManuscriptPolynomialQueryParameters.preparation (Fintype.card ι) d :=
  MSManuscriptPolynomialQueryFactory.preparation_budget_le e A hA hN x y hl hd s

theorem original_cost :
    (original e A hA hN x y hl hd).cost≤costBound (Fintype.card ι) (Fintype.card ι) d := by
  have h:=setup_cost (originalConfig e A hA hN x y hl hd) (Fintype.card ι)
  have hm:=live_le_original x y
  unfold original
  apply h.trans
  unfold costBound MSEpochScalarSetup.costBound
  omega

end Original
end MatrixSpencer.RealRAM.MSEpochLoops
