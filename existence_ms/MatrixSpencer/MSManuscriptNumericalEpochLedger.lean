import MatrixSpencer.MSManuscriptNumericalCoordinateStep
import MatrixSpencer.MSManuscriptOwnerAdvance
import MatrixSpencer.MSManuscriptPreparedResponse

/-! Pathwise bookkeeping for the actual numerical owner preparation and LDL
movement. `variance` records the literal cumulative h² Tr(Q), giving an exact
trace balance and deterministic squared-norm progress on every sampled path.
This module makes no probability or completed-epoch claim. -/
open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.MSManuscriptNumericalEpochLedger
open MSManuscriptSupportedOwner MSManuscriptSupportedGamma MSManuscriptSupportedPaid
variable {N d : ℕ}

structure State (N : ℕ) where
  point : EuclideanSpace ℝ (Fin N)
  owner : Owner N
  time : ℝ
  variance : ℝ
  paid : ℝ
  dust : ℝ
  rounding : ℝ
  centered : EuclideanSpace ℝ (Fin N)

structure Invariant (ε δ E₀ : ℝ) (s : State N) : Prop where
  regular : CubeRegular ε s.point
  owner_valid : s.owner.Valid δ
  owner_le_one : s.owner.physical≤1
  dim_le : s.owner.dim≤N
  time_nonneg : 0≤s.time
  variance_nonneg : 0≤s.variance
  paid_nonneg : 0≤s.paid
  dust_nonneg : 0≤s.dust
  rounding_nonneg : 0≤s.rounding
  trace_balance : realTrace s.owner.physical+s.paid+s.dust+s.variance=N
  variance_le : s.variance≤N*s.time
  variance_ge : (N:ℝ)/16*s.time≤s.variance
  dust_le : s.dust≤4*δ*(N-s.owner.dim:ℕ)
  rounding_le : s.rounding≤ε*(frozenCoordinates s.point).card
  norm_progress : E₀+s.variance≤‖s.point‖^2

/-- Actual preparation accounting: paid mass is its counted fixed-size cuts;
the nonnegative residual trace loss is charged to discarded support. -/
def afterPrepare (P : Parameters N d) (s : State N) (y : Owner N × ℕ) : State N :=
  {s with
    owner:=y.1,
    paid:=s.paid+paidSize P*(y.2:ℝ),
    dust:=s.dust+(realTrace s.owner.physical-realTrace y.1.physical-paidSize P*(y.2:ℝ))}

theorem afterPrepare_invariant (P : Parameters N d) (hP : P.Valid)
    {ε E₀ : ℝ} {s : State N} (hs : Invariant ε P.floor E₀ s)
    {y : Owner N × ℕ} (ho : MSManuscriptSupportedPreparation.output P s.owner=some y) :
    Invariant ε P.floor E₀ (afterPrepare P s y) := by
  have hc := MSManuscriptSupportedPreparation.output_sound P hP s.owner
    ⟨hs.owner_valid,hs.owner_le_one,hs.dim_le⟩ ho
  have hv := hc.state P hP ⟨hs.owner_valid,hs.owner_le_one,hs.dim_le⟩
  have hnonneg : 0≤realTrace s.owner.physical-realTrace y.1.physical-paidSize P*(y.2:ℝ) := by
    linarith [hc.trace_paid]
  refine ⟨hs.regular,hv.1,hv.2.1,hv.2.2,hs.time_nonneg,hs.variance_nonneg,
    add_nonneg hs.paid_nonneg (mul_nonneg (paidSize_pos P hP).le (Nat.cast_nonneg _)),
    add_nonneg hs.dust_nonneg hnonneg,hs.rounding_nonneg,?_,hs.variance_le,hs.variance_ge,?_,
    hs.rounding_le,hs.norm_progress⟩
  · change realTrace y.1.physical+(s.paid+paidSize P*(y.2:ℝ))+
      (s.dust+(realTrace s.owner.physical-realTrace y.1.physical-paidSize P*(y.2:ℝ)))+s.variance=N
    linarith [hs.trace_balance]
  · have hdim : N-y.1.dim=(N-s.owner.dim)+(s.owner.dim-y.1.dim) := by
      have hi:=hs.dim_le; have hj:=hc.dim_le; omega
    change s.dust+(realTrace s.owner.physical-realTrace y.1.physical-paidSize P*(y.2:ℝ))≤
      4*P.floor*(N-y.1.dim:ℕ)
    rw [hdim,Nat.cast_add]
    linarith [hs.dust_le,hc.trace_loss]

def samplingSpace (s : State N) := SimpleMS.Movement.Space s.owner.physical (frozenCoordinates s.point) s.point

abbrev Draws (s : State N) := MSManuscriptNumericalCoordinateStep.Draws s.owner.physical s.point

def Q (s : State N) := MSManuscriptNumericalCoordinateStep.covariance s.owner.physical s.point

def afterMove (ε : ℝ) (s : State N) (h : ℝ) (z : Draws s) : State N :=
  {s with
    point:=MSManuscriptNumericalCoordinateStep.rounded ε s.owner.physical s.point h z,
    owner:=MSManuscriptOwnerAdvance.advance s.owner (Q s) h,
    time:=s.time+h^2,
    variance:=s.variance+h^2*realTrace (Q s),
    rounding:=s.rounding+∑i,|MSManuscriptNumericalCoordinateStep.rounded ε s.owner.physical s.point h z i-
      MSManuscriptNumericalCoordinateStep.moved s.owner.physical s.point h z i|,
    centered:=s.centered+h • MSManuscriptNumericalCoordinateStep.increment s.owner.physical s.point z}

theorem afterMove_invariant {ε δ E₀ : ℝ} (hε : 0≤ε) (hδ : 0≤δ)
    {s : State N} (hs : Invariant ε δ E₀ s) (hfloor : s.owner.Valid (2*δ))
    {h : ℝ} (hh : 0≤h) (hsmall : h*Real.sqrt (N:ℝ)≤ε) (hh2 : h^2≤1/2)
    (hq : (N:ℝ)/16≤realTrace (Q s)) (z : Draws s) :
    Invariant ε δ E₀ (afterMove ε s h z) := by
  have hC := hs.owner_valid.physical_posSemidef s.owner hδ
  have hQ : (Q s).PosSemidef := MSManuscriptNumericalCoordinateStep.covariance_posSemidef _ hC _
  have hQC : Q s≤s.owner.physical := MSManuscriptNumericalCoordinateStep.covariance_le _ hC _
  have hqN : realTrace (Q s)≤N := MSManuscriptNumericalCoordinateStep.covariance_trace_le hC hs.owner_le_one _
  have ht := MSManuscriptOwnerAdvance.trace s.owner hs.owner_valid (Q s) hQ hQC h
  have hn := MSManuscriptNumericalCoordinateStep.rounded_norm_gain hC hs.owner_le_one hs.regular hh hsmall z
  have hc := MSManuscriptNumericalCoordinateStep.rounding_cost_le_new_frozen hC hs.owner_le_one hε hs.regular hh hsmall z
  have hf := MSManuscriptNumericalCoordinateStep.frozen_subset hC ε s.point h z
  refine ⟨MSManuscriptNumericalCoordinateStep.rounded_regular hC hs.owner_le_one hs.regular hh hsmall z,
    MSManuscriptOwnerAdvance.valid s.owner hδ hfloor (Q s) hQC hh2,
    (MSManuscriptOwnerAdvance.below s.owner hs.owner_valid (Q s) hQ hQC h).trans hs.owner_le_one,
    hs.dim_le,add_nonneg hs.time_nonneg (sq_nonneg h),
    add_nonneg hs.variance_nonneg (mul_nonneg (sq_nonneg h) (realTrace_nonneg hQ)),
    hs.paid_nonneg,hs.dust_nonneg,
    add_nonneg hs.rounding_nonneg (Finset.sum_nonneg (fun i _=>abs_nonneg _)),?_,?_,?_,hs.dust_le,?_,?_⟩
  · change realTrace (MSManuscriptOwnerAdvance.advance s.owner (Q s) h).physical+s.paid+s.dust+
      (s.variance+h^2*realTrace (Q s))=N
    rw [ht]
    linarith [hs.trace_balance]
  · change s.variance+h^2*realTrace (Q s)≤(N:ℝ)*(s.time+h^2)
    nlinarith [hs.variance_le,mul_le_mul_of_nonneg_left hqN (sq_nonneg h)]
  · change (N:ℝ)/16*(s.time+h^2)≤s.variance+h^2*realTrace (Q s)
    nlinarith [hs.variance_ge,mul_le_mul_of_nonneg_left hq (sq_nonneg h)]
  · have hcard:=Finset.card_le_card hf
    rw [Nat.cast_sub hcard] at hc
    change s.rounding+_≤ε*(frozenCoordinates
      (MSManuscriptNumericalCoordinateStep.rounded ε s.owner.physical s.point h z)).card
    linarith [hs.rounding_le]
  · change E₀+(s.variance+h^2*realTrace (Q s))≤
      ‖MSManuscriptNumericalCoordinateStep.rounded ε s.owner.physical s.point h z‖^2
    change ‖s.point‖^2+h^2*realTrace (Q s)≤_ at hn
    linarith [hs.norm_progress]


/-- The centered movement omits threshold snaps; their total discrepancy is
bounded by the same explicitly accumulated rounding cost. -/
def CenteredInvariant (x₀ : EuclideanSpace ℝ (Fin N)) (s : State N) : Prop :=
  (∑i,|s.point i-x₀ i-s.centered i|)≤s.rounding

theorem centered_afterPrepare (P : Parameters N d) {s : State N} {x₀ : EuclideanSpace ℝ (Fin N)}
    (hs : CenteredInvariant x₀ s) (y : Owner N×ℕ) : CenteredInvariant x₀ (afterPrepare P s y) := hs

theorem centered_afterMove (ε : ℝ) {s : State N} {x₀ : EuclideanSpace ℝ (Fin N)}
    (hs : CenteredInvariant x₀ s) (h : ℝ) (z : Draws s) : CenteredInvariant x₀ (afterMove ε s h z) := by
  have he (i : Fin N) : (afterMove ε s h z).point i-x₀ i-(afterMove ε s h z).centered i=
      (MSManuscriptNumericalCoordinateStep.rounded ε s.owner.physical s.point h z i-
       MSManuscriptNumericalCoordinateStep.moved s.owner.physical s.point h z i)+
       (s.point i-x₀ i-s.centered i) := by
    simp only [afterMove,MSManuscriptNumericalCoordinateStep.moved,MSManuscriptNumericalCoordinateStep.increment,
      MSManuscriptNumericalMovement.nextPoint,SimpleMS.Movement.nextPoint,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
    ring
  have hb : (∑i,|(afterMove ε s h z).point i-x₀ i-(afterMove ε s h z).centered i|)≤
      ∑i,(|MSManuscriptNumericalCoordinateStep.rounded ε s.owner.physical s.point h z i-
        MSManuscriptNumericalCoordinateStep.moved s.owner.physical s.point h z i|+
        |s.point i-x₀ i-s.centered i|) :=
    Finset.sum_le_sum (fun i _ => by rw [he i]; exact abs_add_le _ _)
  rw [Finset.sum_add_distrib] at hb
  unfold CenteredInvariant at hs ⊢
  change _≤s.rounding+_
  linarith

def initial (x : EuclideanSpace ℝ (Fin N)) : State N where
  point:=x
  owner:=MSManuscriptSupportedPreparation.initial 1
  time:=0
  variance:=0
  paid:=0
  dust:=0
  rounding:=0
  centered:=0

theorem initial_invariant {ε δ : ℝ} (hε : 0≤ε) (hδ : δ≤1)
    (x : EuclideanSpace ℝ (Fin N)) (hx : CubeRegular ε x) :
    Invariant ε δ (‖x‖^2) (initial x) := by
  have hv : (MSManuscriptSupportedPreparation.initial (1 : Matrix (Fin N) (Fin N) ℝ)).Valid 1 := by
    simp [MSManuscriptSupportedPreparation.initial,Owner.Valid]
  refine ⟨hx,valid_mono _ hv hδ,?_,le_rfl,le_rfl,le_rfl,le_rfl,le_rfl,le_rfl,?_,?_,?_,?_,?_,?_⟩
  · simp [initial,MSManuscriptSupportedPreparation.initial,Owner.physical]
  · simp [initial,MSManuscriptSupportedPreparation.initial,Owner.physical,realTrace]
  · simp [initial]
  · simp [initial]
  · simp [initial,MSManuscriptSupportedPreparation.initial]
  · exact mul_nonneg hε (Nat.cast_nonneg _)
  · simp [initial]

theorem initial_centered (x : EuclideanSpace ℝ (Fin N)) : CenteredInvariant x (initial x) := by
  simp [CenteredInvariant,initial]

def timeLimit : ℝ := 1/1539

def Terminal (s : State N) : Prop :=
  timeLimit≤s.time ∨ (N:ℝ)/64≤(frozenCoordinates s.point).card ∨ (N:ℝ)/64<s.paid+s.dust

theorem short_trace_lower {ε δ E₀ : ℝ} (hδ : 0≤δ) {s : State N}
    (hs : Invariant ε δ E₀ s) (hN : 32≤N) (hnt : ¬Terminal s) :
    (N:ℝ)/16≤realTrace (Q s) ∧ 0<realTrace (Q s) := by
  have hh := not_or.mp hnt
  have hf := not_or.mp hh.2
  have ht : s.time<1/1539 := lt_of_not_ge hh.1
  have hp : s.paid+s.dust≤(N:ℝ)/64 := le_of_not_gt hf.2
  have hF : ((frozenCoordinates s.point).card:ℝ)≤(N:ℝ)/64 := (lt_of_not_ge hf.1).le
  have htrace : realTrace (1-s.owner.physical)≤(N:ℝ)/64+(N:ℝ)/1539 := by
    rw [realTrace_sub]
    have hone : realTrace (1 : Matrix (Fin N) (Fin N) ℝ)=(N:ℝ) := by simp [realTrace]
    rw [hone]
    have htN := mul_le_mul_of_nonneg_left ht.le (Nat.cast_nonneg N : (0:ℝ)≤N)
    nlinarith [hs.trace_balance,hs.variance_le,Nat.cast_nonneg (α:=ℝ) N]
  exact MSManuscriptNumericalMovement.trace_positive_of_ledger s.owner.physical
    (hs.owner_valid.physical_posSemidef _ hδ) hs.owner_le_one _ _ hN htrace hF

end MatrixSpencer.MSManuscriptNumericalEpochLedger
