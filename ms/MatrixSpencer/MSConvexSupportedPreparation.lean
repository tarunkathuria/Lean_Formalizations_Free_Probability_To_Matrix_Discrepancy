import MatrixSpencer.MSManuscriptSupportedPreparation
import MatrixSpencer.MSConvexSupportedGamma

/-! The original square walk with convex owner-value queries substituted.
The state, invariants, tuning constants and non-query primitives remain original. -/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSConvexSupportedPreparation
open MSManuscriptSupportedPreparation MSManuscriptSupportedOwner MSManuscriptSupportedGamma MSManuscriptSupportedPaid MSConvexSupportedGamma
variable [MSConvexOwnerValue.Oracle]
variable {N d : ℕ}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
attribute [local irreducible] ownerPotential
export MSManuscriptSupportedPreparation (State Certificate clean_state budget initial initial_state)

def run (P : Parameters N d) : ℕ → Owner N → Option (Owner N × ℕ)
  | 0,_ => none
  | fuel+1,O =>
    let K := clean O P.floor
    match MSConvexSupportedGamma.direction P K with
    | none => some (K,0)
    | some u => (run P fuel (paid K (paidSize P) (WithLp.ofLp u))).map (fun y => (y.1,y.2+1))

private theorem trace_mono {C K : Matrix (Fin N) (Fin N) ℝ} (h : K≤C) : realTrace K≤realTrace C := by
  have ht := realTrace_nonneg (Matrix.le_iff.mp h)
  rw [realTrace_sub] at ht
  linarith

theorem continuation (P : Parameters N d) (hP : P.Valid) (K : Owner N)
    (hK : K.Valid (2*P.floor)) (hK1 : K.physical≤1) (hKN : K.dim≤N)
    {u : EuclideanSpace ℝ (Fin K.dim)} (hu : MSConvexSupportedGamma.direction P K=some u) :
    State P (paid K (paidSize P) (WithLp.ofLp u)) ∧ WithLp.ofLp u≠0 ∧
    potential P (paid K (paidSize P) (WithLp.ofLp u))+paidGain P≤potential P K := by
  have hKδ := valid_mono K hK (by linarith [hP.2.2.2.1] : P.floor≤2*P.floor)
  have hh := MSConvexSupportedGamma.direction_some P hP K hKδ hK1 hu
  have hne : WithLp.ofLp u≠0 := by
    intro hz
    have he : u=0 := WithLp.ofLp_injective 2 hz
    rw [he,norm_zero] at hh
    norm_num at hh
  refine ⟨⟨paid_valid K hP.2.2.2.1 hK (paidSize_pos P hP).le
    ((paidSize_le P).trans (by linarith [hP.2.2.2.1] : P.floor/4≤P.floor)) u hh.1,
    (paid_le K (paidSize_pos P hP).le _).trans hK1,hKN⟩,hne,?_⟩
  exact paid_potential_drop P hP K hK hK1 hKN u hh.1 hh.2.le

theorem run_sound (P : Parameters N d) (hP : P.Valid) (fuel : ℕ)
    {O : Owner N} (hO : State P O) {y : Owner N × ℕ} (ho : run P fuel O=some y) :
    Certificate P O fuel y := by
  induction fuel generalizing O y with
  | zero => simp [run] at ho
  | succ fuel ih =>
    obtain ⟨hK,hK1,hKN⟩ := clean_state P hP O hO
    have hKδ := valid_mono (clean O P.floor) hK (by linarith [hP.2.2.2.1])
    have hclean := clean_le O hP.2.2.2.1.le hO.1
    have hdim := clean_dim_le O P.floor
    have htrclean := trace_mono hclean
    have hvalclean := clean_potential_le P hP O hO.1
    have hloss := clean_trace_loss O hP.2.2.2.1 hO.1
    cases hc : MSConvexSupportedGamma.direction P (clean O P.floor) with
    | none =>
      simp only [run,hc,Option.some.injEq] at ho
      subst y
      refine ⟨hK,hclean,hdim,MSConvexSupportedGamma.direction_none P hP _ hKδ hK1 hc,by omega,?_,?_,?_⟩
      · simpa using htrclean
      · simpa using hloss
      · simpa using hvalclean
    | some u =>
      simp only [run,hc] at ho
      obtain ⟨z,hz,hzy⟩ := Option.map_eq_some_iff.mp ho
      subst y
      obtain ⟨hpaid,hune,hvalpaid⟩ := continuation P hP _ hK hK1 hKN hc
      have hzcert := ih hpaid hz
      have htrpaid := paid_trace (clean O P.floor) hK.1 (paidSize P) (WithLp.ofLp u) hune
      have hpaidle := paid_le (clean O P.floor) (paidSize_pos P hP).le (WithLp.ofLp u)
      have hdimz : z.1.dim≤(clean O P.floor).dim := hzcert.dim_le
      have hdeq : O.dim-z.1.dim=(O.dim-(clean O P.floor).dim)+((clean O P.floor).dim-z.1.dim) := by omega
      refine ⟨hzcert.valid,hzcert.below.trans (hpaidle.trans hclean),hdimz.trans hdim,
        hzcert.cap,by have hh := hzcert.counter_le; dsimp; omega,?_,?_,?_⟩
      · have hh := hzcert.trace_paid
        dsimp
        push_cast
        linarith
      · have hh := hzcert.trace_loss
        change realTrace (paid (clean O P.floor) (paidSize P) (WithLp.ofLp u)).physical-
          realTrace z.1.physical≤paidSize P*(z.2:ℝ)+4*P.floor*((clean O P.floor).dim-z.1.dim:ℕ) at hh
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

theorem trace_lower_of_none (P : Parameters N d) (hP : P.Valid) (fuel : ℕ)
    {O : Owner N} (hO : State P O) (ho : run P fuel O=none) :
    (fuel:ℝ)*paidSize P≤realTrace O.physical := by
  induction fuel generalizing O with
  | zero => simpa using realTrace_nonneg (hO.1.physical_posSemidef O hP.2.2.2.1.le)
  | succ fuel ih =>
    obtain ⟨hK,hK1,hKN⟩ := clean_state P hP O hO
    cases hc : MSConvexSupportedGamma.direction P (clean O P.floor) with
    | none => simp [run,hc] at ho
    | some u =>
      have hn : run P fuel (paid (clean O P.floor) (paidSize P) (WithLp.ofLp u))=none := by
        simpa only [run,hc,Option.map_eq_none_iff] using ho
      obtain ⟨hpaid,hune,_⟩ := continuation P hP _ hK hK1 hKN hc
      have ht := ih hpaid hn
      have htr := paid_trace (clean O P.floor) hK.1 (paidSize P) (WithLp.ofLp u) hune
      have hclean := trace_mono (clean_le O hP.2.2.2.1.le hO.1)
      push_cast
      nlinarith

def output (P : Parameters N d) (O : Owner N) := run P (budget P) O

theorem output_isSome (P : Parameters N d) (hP : P.Valid) (O : Owner N) (hO : State P O) :
    (output P O).isSome=true := by
  have htrace : realTrace O.physical≤N := by
    simpa only [realTrace,Matrix.trace_one,Fintype.card_fin] using trace_mono hO.2.1
  cases ho : output P O with
  | some y => rfl
  | none =>
    have ht := trace_lower_of_none P hP (budget P) hO ho
    have hb := MSManuscriptPreparationRun.budget_trace_lt (L:=(N:ℝ)) (paidSize_pos P hP)
    exfalso
    change (N:ℝ)<(budget P:ℝ)*paidSize P at hb
    linarith

theorem output_sound (P : Parameters N d) (hP : P.Valid) (O : Owner N) (hO : State P O)
    {y : Owner N × ℕ} (ho : output P O=some y) : Certificate P O (budget P) y :=
  run_sound P hP _ hO ho

theorem output_paid_count (P : Parameters N d) (hP : P.Valid) (O : Owner N)
    (hO : State P O) {y : Owner N × ℕ} (ho : output P O=some y) :
    (y.2:ℝ)≤(N:ℝ)/paidSize P := by
  have hc := output_sound P hP O hO ho
  have hy := hc.state P hP hO
  have hnonneg := realTrace_nonneg (hy.1.physical_posSemidef y.1 hP.2.2.2.1.le)
  have htrace : realTrace O.physical≤N := by
    simpa only [realTrace,Matrix.trace_one,Fintype.card_fin] using trace_mono hO.2.1
  apply (le_div_iff₀ (paidSize_pos P hP)).mpr
  nlinarith [hc.trace_paid]

theorem output_unpaid_loss (P : Parameters N d) (hP : P.Valid) (O : Owner N)
    (hO : State P O) {y : Owner N × ℕ} (ho : output P O=some y) :
    realTrace O.physical-realTrace y.1.physical-paidSize P*(y.2:ℝ)≤4*P.floor*N := by
  have hc := output_sound P hP O hO ho
  have hdim : (O.dim-y.1.dim:ℕ)≤N := (Nat.sub_le _ _).trans hO.2.2
  have hcast : ((O.dim-y.1.dim:ℕ):ℝ)≤N := Nat.cast_le.mpr hdim
  have hm := mul_le_mul_of_nonneg_left hcast (mul_nonneg (by norm_num : (0:ℝ)≤4) hP.2.2.2.1.le)
  linarith [hc.trace_loss]

def prepareMatrix (P : Parameters N d) (C : Matrix (Fin N) (Fin N) ℝ) := output P (initial C)

theorem prepareMatrix_isSome (P : Parameters N d) (hP : P.Valid)
    (C : Matrix (Fin N) (Fin N) ℝ)
    (hfloor : P.floor • (1 : Matrix (Fin N) (Fin N) ℝ)≤C) (hC1 : C≤1) :
    (prepareMatrix P C).isSome=true := output_isSome P hP _ (initial_state P C hfloor hC1)

theorem prepareMatrix_sound (P : Parameters N d) (hP : P.Valid)
    (C : Matrix (Fin N) (Fin N) ℝ)
    (hfloor : P.floor • (1 : Matrix (Fin N) (Fin N) ℝ)≤C) (hC1 : C≤1)
    {y : Owner N × ℕ} (ho : prepareMatrix P C=some y) :
    Certificate P (initial C) (budget P) y :=
  output_sound P hP _ (initial_state P C hfloor hC1) ho

theorem prepareIdentity_isSome (P : Parameters N d) (hP : P.Valid) :
    (prepareMatrix P (1 : Matrix (Fin N) (Fin N) ℝ)).isSome=true := by
  have hi : (initial (1 : Matrix (Fin N) (Fin N) ℝ)).Valid 1 := by
    simp [initial,Owner.Valid]
  have hv := valid_mono _ hi hP.2.2.2.2.1
  exact prepareMatrix_isSome P hP _ hv.2 le_rfl

end MatrixSpencer.MSConvexSupportedPreparation
