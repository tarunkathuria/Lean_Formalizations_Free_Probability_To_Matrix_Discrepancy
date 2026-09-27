import MatrixSpencer.MSManuscriptNumericalEpochFactory
import MatrixSpencer.MSConvexAcceptedEpoch
import MatrixSpencer.MSManuscriptCoefficientReindex
import MatrixSpencer.MSManuscriptMatrixReindex
import MatrixSpencer.MSManuscriptNumericalFullSigning

/-! Ordered live-label enumeration instantiates the numerical phase factory
with the actual accepted numerical epoch. All original frozen labels are
retained by the explicit lift. No epoch provider is a premise of this factory. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSConvexNumericalEpochFactory
variable [MSConvexOwnerValue.Oracle]
open PhaseRestriction MSManuscriptAdaptive MSManuscriptPhase MSManuscriptCoefficientReindex
variable {ι : Type*} [Fintype ι] [LinearOrder ι] {d : ℕ} [Nonempty (Fin d)]
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
attribute [local irreducible] ownerPotential

/-- Input permutation to the computed increasing enumeration of live labels. -/
def reindexConfig {κ : Type*} [Fintype κ] [DecidableEq κ]
    (c : EpochConfig κ (Fin d)) (e : Fin (Fintype.card κ)≃κ) :
    EpochConfig (Fin (Fintype.card κ)) (Fin d) where
  matrices:=fun i=>c.matrices (e i)
  hermitian:=fun i=>c.hermitian (e i)
  contractions:=fun i=>c.contractions (e i)
  offset:=c.offset
  start:=point e c.start
  epsilon:=c.epsilon
  epsilon_pos:=c.epsilon_pos
  epsilon_small:=by simpa only [Fintype.card_fin] using c.epsilon_small
  start_regular:=point_regular e c.start_regular
  start_unfrozen:=fun i=>c.start_unfrozen (e i)
  count_large:=by simpa only [Fintype.card_fin] using c.count_large

variable (offset : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) (A : ι→Matrix (Fin d) (Fin d) ℂ)
  (hA : ∀i,(A i).IsHermitian) (hN : ∀i,‖A i‖≤1) (ε : ℝ) (hε : 0<ε)
  (hsmall : (Fintype.card ι:ℝ)*ε≤1/1000) (hd : 0<d)

def cfg (x : Point (ι:=ι) ε) (hl : 32≤Fintype.card (Live x.val)) :=
  reindexConfig (epochConfig offset A hA hN x.val ε hε hsmall x.property hl) (enumeration (Live x.val))

def restored (x : Point (ι:=ι) ε) (y : EuclideanSpace ℝ (Fin (Fintype.card (Live x.val)))) :
    EuclideanSpace ℝ (Live x.val) := point (enumeration (Live x.val)).symm y

theorem good_advance (x : Point (ι:=ι) ε) (hl : 32≤Fintype.card (Live x.val))
    (s : MSManuscriptNumericalEpochRun.Certified (MSManuscriptNumericalConfig.ofEpochConfig
      (cfg offset A hA hN ε hε hsmall x hl) hd))
    (hg : MSConvexAcceptedEpoch.GoodEndpoint (cfg offset A hA hN ε hε hsmall x hl) hd s) :
    FiniteHalfPhase.EpochAdvance (remainingPotential offset A hA)
      MSManuscriptNumericalHalfPhase.epochTime MSManuscriptNumericalHalfPhase.epochCost
      x.val (liftPoint x.val (restored ε x s.val.point)) s.val.time := by
  let C:=epochConfig offset A hA hN x.val ε hε hsmall x.property hl
  let e:=enumeration (Live x.val)
  let y:=restored ε x s.val.point
  have hy : CubeRegular ε y := point_regular e.symm s.property.1.regular
  have hn : ‖restrictPoint x.val‖^2+(Fintype.card (Live x.val):ℝ)/16*s.val.time≤‖y‖^2 := by
    have hh:=s.property.1.norm_progress
    have hv:=s.property.1.variance_ge
    change ‖point e (restrictPoint x.val)‖^2+s.val.variance≤‖s.val.point‖^2 at hh
    rw [point_norm_sq] at hh
    change _≤‖point e.symm s.val.point‖^2
    rw [point_norm_sq]
    linarith
  refine ⟨(liftPoint_regular x.property hy).1,frozen_subset_liftPoint _ _,s.property.1.time_nonneg,?_,?_,?_⟩
  · simpa only [live_card,FiniteHalfPhase.liveCount] using norm_gain_liftPoint x.val y _ hn
  · rcases hg.progress with hf|ht
    · right
      rw [frozen_card_gain_real]
      change _≤((frozenCoordinates (point e.symm s.val.point)).card:ℝ)
      rw [frozen_card]
      simpa only [live_card,FiniteHalfPhase.liveCount] using hf
    · left
      convert ht using 1
      norm_num [MSManuscriptNumericalHalfPhase.epochTime,MSManuscriptNumericalEpochLedger.timeLimit]
  · have hdrop:=remainingPotential_lift_le offset A hA x.val y
    have hend:=centered_potential_one C.offset C.matrices C.hermitian e y (1:ℝ)
    have hi : point e y=s.val.point := point_inverse e.symm s.val.point
    rw [hi] at hend
    have hstart:=centered_potential_one C.offset C.matrices C.hermitian e C.start (1:ℝ)
    have hcenter:=center_liftPoint offset A hA x.val (restrictPoint x.val)
    rw [liftPoint_restrictPoint] at hcenter
    have hbase : ownerPotential (epochCenter C.offset C.matrices C.hermitian C.start) C.matrices 1 1=
        remainingPotential offset A hA x.val := by
      change ownerPotential (epochCenter (restrictedOffset offset A hA x.val) (restrictedFamily A x.val)
        (restrictedFamily_hermitian A hA x.val) (restrictPoint x.val)) (restrictedFamily A x.val) 1 1=_
      rw [←hcenter]
      rfl
    have hcost:=hg.reset_growth
    change ownerPotential (epochCenter C.offset (fun i=>C.matrices (e i)) (fun i=>C.hermitian (e i)) s.val.point)
      (fun i=>C.matrices (e i)) 1 1≤
      ownerPotential (epochCenter C.offset (fun i=>C.matrices (e i)) (fun i=>C.hermitian (e i)) (point e C.start))
        (fun i=>C.matrices (e i)) 1 1+27*Real.sqrt (Fintype.card (Live x.val):ℝ) at hcost
    rw [hend,hstart,hbase] at hcost
    change remainingPotential offset A hA (liftPoint x.val y)≤_
    rw [FiniteHalfPhase.liveCount,←live_card]
    exact hdrop.trans hcost

def sample (x : Point (ι:=ι) ε) (hl : 32≤Fintype.card (Live x.val)) (r : ℕ) :
    Sampler (Option (Point (ι:=ι) ε×ℝ)) :=
  (MSConvexAcceptedEpoch.output (cfg offset A hA hN ε hε hsmall x hl) hd r).map
    (Option.map (fun s=>(⟨liftPoint x.val (restored ε x s.val.point),
      liftPoint_regular x.property (point_regular _ s.property.1.regular)⟩,s.val.time)))

theorem sample_sound (x : Point (ι:=ι) ε) (hl : 32≤Fintype.card (Live x.val)) (r : ℕ)
    (z : (sample offset A hA hN ε hε hsmall hd x hl r).Draws) (y : Point (ι:=ι) ε×ℝ)
    (ho : (sample offset A hA hN ε hε hsmall hd x hl r).value z=some y) :
    FiniteHalfPhase.EpochAdvance (remainingPotential offset A hA)
      MSManuscriptNumericalHalfPhase.epochTime MSManuscriptNumericalHalfPhase.epochCost x.val y.1.val y.2 := by
  change ((MSConvexAcceptedEpoch.output (cfg offset A hA hN ε hε hsmall x hl) hd r).value z).map _=some y at ho
  obtain ⟨s,hs,hsy⟩:=Option.map_eq_some_iff.mp ho
  subst y
  exact good_advance offset A hA hN ε hε hsmall hd x hl s
    (MSConvexAcceptedEpoch.output_sound _ hd r z s hs)

theorem sample_failure (x : Point (ι:=ι) ε) (hl : 32≤Fintype.card (Live x.val)) (r : ℕ) :
    (sample offset A hA hN ε hε hsmall hd x hl r).expectation failure≤(301/800:ℝ)^r := by
  unfold sample
  rw [Sampler.failure_map]
  exact MSConvexAcceptedEpoch.output_failure_le _ hd r

private theorem large {x : Point (ι:=ι) ε} (hx : ¬FiniteHalfPhase.Terminal x.val) :
    32≤Fintype.card (Live x.val) := by
  simpa only [live_card,FiniteHalfPhase.liveCount] using FiniteHalfPhase.liveCount_large_of_nonterminal hx

/-- Fully instantiated numerical epoch factory; its only inputs are the
original family, cube-margin data and the number of independent retries. -/
def factory (r : ℕ) : MSManuscriptNumericalHalfPhase.EpochFactory offset A hA ε ((301/800:ℝ)^r) where
  sample x hx:=sample offset A hA hN ε hε hsmall hd x (large ε hx) r
  sound x hx:=sample_sound offset A hA hN ε hε hsmall hd x (large ε hx) r
  failure_le x hx:=sample_failure offset A hA hN ε hε hsmall hd x (large ε hx) r

end MatrixSpencer.MSConvexNumericalEpochFactory
