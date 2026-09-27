import MatrixSpencer.RectangularRidgePreparationData

/-! The literal finite paid-preparation loop with finite stored-frame cleanup.
Its report is a supplied numerical algorithm satisfying a matrix error contract;
all covariance, stopping, trace debit and true-potential progress conclusions
are proved for its actual execution. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgePreparationRun
open MSManuscriptSupportedOwner RectangularRidgePreparationData
variable {N d : ℕ} [Nonempty (Fin d)]
local instance ridgePreparationRunCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2048
set_option maxRecDepth 4096
attribute [local irreducible] RectangularRidgePotential.optimizer
  RectangularRidgeCovarianceCalculus.ownerPotential regularizedOwnerPotential

def run (P : Parameters N d) (R : Report P) : ℕ → Owner N → Option (Owner N × ℕ)
  | 0,_ => none
  | fuel+1,O =>
    let K := clean O floor
    match direction P R K with
    | none => some (K,0)
    | some u => (run P R fuel (paid K (paidSize P) (WithLp.ofLp u))).map (fun y => (y.1,y.2+1))

/-- Number of cleanup/cap-test rounds on the same literal branch as `run`. -/
def tests (P : Parameters N d) (R : Report P) : ℕ → Owner N → ℕ
  | 0,_ => 0
  | fuel+1,O =>
    let K := clean O floor
    match direction P R K with
    | none => 1
    | some u => 1+tests P R fuel (paid K (paidSize P) (WithLp.ofLp u))

theorem tests_le_fuel (P : Parameters N d) (R : Report P) (fuel : ℕ) (O : Owner N) :
    tests P R fuel O≤fuel := by
  induction fuel generalizing O with
  | zero => rfl
  | succ fuel ih =>
    cases hc : direction P R (clean O floor) with
    | none => simp [tests,hc]
    | some u =>
      simp only [tests,hc]
      have hh := ih (paid (clean O floor) (paidSize P) (WithLp.ofLp u))
      omega

theorem tests_of_run_some (P : Parameters N d) (R : Report P) (fuel : ℕ)
    {O : Owner N} {y : Owner N × ℕ} (ho : run P R fuel O=some y) :
    tests P R fuel O=y.2+1 := by
  induction fuel generalizing O y with
  | zero => simp [run] at ho
  | succ fuel ih =>
    cases hc : direction P R (clean O floor) with
    | none =>
      simp only [run,hc,Option.some.injEq] at ho
      subst y
      simp [tests,hc]
    | some u =>
      simp only [run,hc] at ho
      obtain ⟨z,hz,hzy⟩ := Option.map_eq_some_iff.mp ho
      subst y
      simp only [tests,hc]
      have hh := ih hz
      omega

structure Certificate (P : Parameters N d) (initial : Owner N) (fuel : ℕ)
    (result : Owner N × ℕ) : Prop where
  valid : result.1.Valid (2*floor)
  below : result.1.physical≤ initial.physical
  dim_le : result.1.dim≤ initial.dim
  cap : Cap P result.1
  counter_le : result.2≤fuel
  trace_paid : realTrace result.1.physical+paidSize P*(result.2:ℝ)≤realTrace initial.physical
  trace_loss : realTrace initial.physical-realTrace result.1.physical≤
    paidSize P*(result.2:ℝ)+4*floor*(initial.dim-result.1.dim:ℕ)
  potential_paid : potential P result.1+paidGain P*(result.2:ℝ)≤potential P initial

private theorem trace_mono {C K : Matrix (Fin N) (Fin N) ℝ} (h : K≤C) : realTrace K≤realTrace C := by
  have ht := realTrace_nonneg (Matrix.le_iff.mp h)
  rw [realTrace_sub] at ht
  linarith

theorem run_sound (P : Parameters N d) (hP : P.Valid) (R : Report P) (fuel : ℕ)
    {O : Owner N} (hO : State O) {y : Owner N × ℕ} (ho : run P R fuel O=some y) :
    Certificate P O fuel y := by
  induction fuel generalizing O y with
  | zero => simp [run] at ho
  | succ fuel ih =>
    obtain ⟨hK,hK1,hKN⟩ := clean_state O hO
    have hKδ := valid_mono (clean O floor) hK (by linarith [(show 0<floor by norm_num [floor])])
    have hclean := clean_le O (show 0<floor by norm_num [floor]).le hO.1
    have hdim := clean_dim_le O floor
    have htrclean := trace_mono hclean
    have hvalclean := clean_potential_le P hP O hO.1
    have hloss := clean_trace_loss O (show 0<floor by norm_num [floor]) hO.1
    cases hc : direction P R (clean O floor) with
    | none =>
      simp only [run,hc,Option.some.injEq] at ho
      subst y
      refine ⟨hK,hclean,hdim,direction_none P hP R _ ⟨hKδ,hK1,hKN⟩ hc,by omega,?_,?_,?_⟩
      · simpa using htrclean
      · simpa using hloss
      · simpa using hvalclean
    | some u =>
      simp only [run,hc] at ho
      obtain ⟨z,hz,hzy⟩ := Option.map_eq_some_iff.mp ho
      subst y
      obtain ⟨hpaid,hune,hvalpaid⟩ := continuation P hP R _ hK hK1 hKN hc
      have hzcert := ih hpaid hz
      have htrpaid := paid_trace (clean O floor) hK.1 (paidSize P) (WithLp.ofLp u) hune
      have hpaidle := paid_le (clean O floor) (paidSize_pos P).le (WithLp.ofLp u)
      have hdimz : z.1.dim≤(clean O floor).dim := hzcert.dim_le
      have hdeq : O.dim-z.1.dim=(O.dim-(clean O floor).dim)+((clean O floor).dim-z.1.dim) := by omega
      refine ⟨hzcert.valid,hzcert.below.trans (hpaidle.trans hclean),hdimz.trans hdim,
        hzcert.cap,by have hh := hzcert.counter_le; dsimp; omega,?_,?_,?_⟩
      · have hh := hzcert.trace_paid
        dsimp
        push_cast
        linarith
      · have hh := hzcert.trace_loss
        change realTrace (paid (clean O floor) (paidSize P) (WithLp.ofLp u)).physical-
          realTrace z.1.physical≤paidSize P*(z.2:ℝ)+4*floor*((clean O floor).dim-z.1.dim:ℕ) at hh
        dsimp
        rw [hdeq]
        push_cast
        linarith
      · have hh := hzcert.potential_paid
        dsimp
        push_cast
        linarith

/-- Exhausting all cap tests would consume at least fuel times the fixed
positive paid size. This rules out exhaustion at the arithmetic trace budget. -/
theorem trace_lower_of_none (P : Parameters N d) (hP : P.Valid) (R : Report P) (fuel : ℕ)
    {O : Owner N} (hO : State O) (ho : run P R fuel O=none) :
    (fuel:ℝ)*paidSize P≤realTrace O.physical := by
  induction fuel generalizing O with
  | zero => simpa using realTrace_nonneg (hO.1.physical_posSemidef O (show 0<floor by norm_num [floor]).le)
  | succ fuel ih =>
    obtain ⟨hK,hK1,hKN⟩ := clean_state O hO
    cases hc : direction P R (clean O floor) with
    | none => simp [run,hc] at ho
    | some u =>
      have hn : run P R fuel (paid (clean O floor) (paidSize P) (WithLp.ofLp u))=none := by
        simpa only [run,hc,Option.map_eq_none_iff] using ho
      obtain ⟨hpaid,hune,_⟩ := continuation P hP R _ hK hK1 hKN hc
      have ht := ih hpaid hn
      have htr := paid_trace (clean O floor) hK.1 (paidSize P) (WithLp.ofLp u) hune
      have hclean := trace_mono (clean_le O (show 0<floor by norm_num [floor]).le hO.1)
      push_cast
      nlinarith

/-- A literal natural polynomial budget; no real ceiling or logarithm oracle
is involved in setting the number of cap tests. -/
def budget (_P : Parameters N d) : ℕ := 2^320*(d+N+2)^63+1

private theorem trace_scale {S : ℝ} (hS : 0<S) :
    (2^320*S^63)*RectangularRidgeNumericalParameters.paidStep S=S := by
  unfold RectangularRidgeNumericalParameters.paidStep
    RectangularRidgeNumericalParameters.small RectangularRidgeNumericalParameters.big
  field_simp

theorem budget_trace_lt (P : Parameters N d) : (N:ℝ)<(budget P:ℝ)*paidSize P := by
  let S := RectangularRidgeNumericalOptimizerFloor.size d N
  have hS0 : 0<S := by have := size_one_le P; dsimp [S]; linarith
  have hS : (N:ℝ)<S := by dsimp [S,RectangularRidgeNumericalOptimizerFloor.size]; have := Nat.cast_nonneg (α:=ℝ) d; linarith
  have he : (((2^320*(d+N+2)^63 : ℕ):ℝ))*paidSize P=S := by
    have hc : (((2^320*(d+N+2)^63 : ℕ):ℝ))=2^320*S^63 := by
      simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add,S,
        RectangularRidgeNumericalOptimizerFloor.size]
    rw [hc]
    exact trace_scale hS0
  have ha := paidSize_pos P
  change (N:ℝ)<(((2^320*(d+N+2)^63 : ℕ)+1:ℕ):ℝ)*paidSize P
  rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul,he]
  linarith

def output (P : Parameters N d) (R : Report P) (O : Owner N) := run P R (budget P) O

theorem output_isSome (P : Parameters N d) (hP : P.Valid) (R : Report P)
    (O : Owner N) (hO : State O) : (output P R O).isSome=true := by
  have htrace : realTrace O.physical≤N := by
    simpa only [realTrace,Matrix.trace_one,Fintype.card_fin] using trace_mono hO.2.1
  cases ho : output P R O with
  | some y => rfl
  | none =>
    have ht := trace_lower_of_none P hP R (budget P) hO ho
    have hb := budget_trace_lt P
    exfalso
    linarith

theorem output_sound (P : Parameters N d) (hP : P.Valid) (R : Report P) (O : Owner N)
    (hO : State O) {y : Owner N × ℕ} (ho : output P R O=some y) :
    Certificate P O (budget P) y := run_sound P hP R _ hO ho

theorem Certificate.state (P : Parameters N d) {O : Owner N}
    (hO : State O) {fuel : ℕ} {y : Owner N × ℕ} (hc : Certificate P O fuel y) : State y.1 :=
  ⟨valid_mono _ hc.valid (by norm_num [floor]),hc.below.trans hO.2.1,
    hc.dim_le.trans hO.2.2⟩

theorem output_paid_count (P : Parameters N d) (hP : P.Valid) (R : Report P)
    (O : Owner N) (hO : State O) {y : Owner N × ℕ} (ho : output P R O=some y) :
    (y.2:ℝ)≤(N:ℝ)/paidSize P := by
  have hc := output_sound P hP R O hO ho
  have hy := hc.state P hO
  have hnonneg := realTrace_nonneg (hy.1.physical_posSemidef y.1 (by norm_num [floor]))
  have htrace : realTrace O.physical≤N := by
    simpa only [realTrace,Matrix.trace_one,Fintype.card_fin] using trace_mono hO.2.1
  apply (le_div_iff₀ (paidSize_pos P)).mpr
  nlinarith [hc.trace_paid]

theorem output_unpaid_loss (P : Parameters N d) (hP : P.Valid) (R : Report P)
    (O : Owner N) (hO : State O) {y : Owner N × ℕ} (ho : output P R O=some y) :
    realTrace O.physical-realTrace y.1.physical-paidSize P*(y.2:ℝ)≤4*floor*N := by
  have hc := output_sound P hP R O hO ho
  have hdim : (O.dim-y.1.dim:ℕ)≤N := (Nat.sub_le _ _).trans hO.2.2
  have hcast : ((O.dim-y.1.dim:ℕ):ℝ)≤N := Nat.cast_le.mpr hdim
  have hm := mul_le_mul_of_nonneg_left hcast (by norm_num [floor] : (0:ℝ)≤4*floor)
  linarith [hc.trace_loss]

/-- Every coefficient-space constraint carried by the original owner survives
all cleanup and paid cuts, because the physical covariance range can only shrink. -/
theorem output_range_le (P : Parameters N d) (hP : P.Valid) (R : Report P)
    (O : Owner N) (hO : State O) {y : Owner N × ℕ} (ho : output P R O=some y) :
    LinearMap.range (Matrix.toEuclideanCLM (𝕜:=ℝ) y.1.physical).toLinearMap ≤
      LinearMap.range (Matrix.toEuclideanCLM (𝕜:=ℝ) O.physical).toLinearMap := by
  have hc := output_sound P hP R O hO ho
  exact posSemidef_range_le_of_le
    (hc.valid.physical_posSemidef y.1 (by norm_num [floor]))
    (hO.1.physical_posSemidef O (by norm_num [floor])) hc.below

def initial (C : Matrix (Fin N) (Fin N) ℝ) : Owner N where
  dim := N
  frame := 1
  matrix := C

theorem initial_state (C : Matrix (Fin N) (Fin N) ℝ)
    (hfloor : floor • (1 : Matrix (Fin N) (Fin N) ℝ)≤C) (hC1 : C≤1) : State (initial C) := by
  refine ⟨⟨by simp [initial],hfloor⟩,?_,le_rfl⟩
  simpa only [initial,Owner.physical,Matrix.transpose_one,Matrix.one_mul,Matrix.mul_one] using hC1

def prepareMatrix (P : Parameters N d) (R : Report P) (C : Matrix (Fin N) (Fin N) ℝ) :=
  output P R (initial C)

theorem prepareMatrix_isSome (P : Parameters N d) (hP : P.Valid) (R : Report P)
    (C : Matrix (Fin N) (Fin N) ℝ)
    (hfloor : floor • (1 : Matrix (Fin N) (Fin N) ℝ)≤C) (hC1 : C≤1) :
    (prepareMatrix P R C).isSome=true := output_isSome P hP R _ (initial_state C hfloor hC1)

theorem prepareMatrix_sound (P : Parameters N d) (hP : P.Valid) (R : Report P)
    (C : Matrix (Fin N) (Fin N) ℝ)
    (hfloor : floor • (1 : Matrix (Fin N) (Fin N) ℝ)≤C) (hC1 : C≤1)
    {y : Owner N × ℕ} (ho : prepareMatrix P R C=some y) :
    Certificate P (initial C) (budget P) y := output_sound P hP R _ (initial_state C hfloor hC1) ho

theorem prepareIdentity_isSome (P : Parameters N d) (hP : P.Valid) (R : Report P) :
    (prepareMatrix P R (1 : Matrix (Fin N) (Fin N) ℝ)).isSome=true := by
  apply prepareMatrix_isSome P hP R _ ?_ le_rfl
  apply Matrix.le_iff.mpr
  have hh := (Matrix.PosSemidef.one : (1 : Matrix (Fin N) (Fin N) ℝ).PosSemidef).smul
    (by norm_num [floor] : (0:ℝ)≤1-floor)
  simpa only [sub_smul,one_smul] using hh

end MatrixSpencer.RectangularRidgePreparationRun
