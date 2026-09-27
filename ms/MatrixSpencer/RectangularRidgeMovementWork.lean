import SimpleMS.CountedSpectralSampler
import MatrixSpencer.MSCountedMovement
import MatrixSpencer.RectangularRidgeEpochRun

/-! Concrete finite uniform movement of a certified live rectangular ridge state. Both
materialization of the physical covariance and its uniform signed spectral-frame sampling law are
accounted for. The conservative implementation may recompute covariance and
increment during the ledger update; both computations are charged. -/
open Matrix Set
noncomputable section
namespace MatrixSpencer.RectangularRidgeMovementWork
open RealRAM
open RealRAM.JacobiIteration (Counted)
open MSCountedSampler
open RectangularRidgeEpochInput RectangularRidgeEpochRun
open RectangularRidgePreparationData (floor)
open MSManuscriptNumericalEpochLedger (State Q short_trace_lower samplingSpace)
variable {N d : ℕ} [Nonempty (Fin d)]
set_option maxRecDepth 4096
attribute [local instance] Classical.propDecidable

def covariance (s : State N) : Counted (Matrix (Fin N) (Fin N) ℝ) :=
  let p := MSGammaTop.physical s.owner
  let q := MSCovariance.covariance p.value s.point
  ⟨q.value,p.cost+q.cost+2⟩

theorem covariance_value (s : State N) : (covariance s).value=Q s := by
  simp only [covariance,MSGammaTop.physical_value,MSCovariance.covariance_value]
  rfl

def value (c : Config N d) (s : Certified c)
    (hfloor : s.val.owner.Valid (2*floor)) (hnt : ¬Stopped c s.val)
    (z : MSManuscriptNumericalEpochLedger.Draws s.val) : Counted (Certified c) :=
  let y := MSCountedMovement.afterMove (margin N) s.val (mesh c) z
  ⟨⟨y.value,by
      have he := MSCountedMovement.afterMove_value (margin N) s.val (mesh c) z
      rw [he]
      exact (moveValue c s hfloor hnt z).property⟩,y.cost+1⟩

theorem value_eq (c : Config N d) (s : Certified c)
    (hfloor : s.val.owner.Valid (2*floor)) (hnt : ¬Stopped c s.val)
    (z : MSManuscriptNumericalEpochLedger.Draws s.val) :
    (value c s hfloor hnt z).value=moveValue c s hfloor hnt z := by
  apply Subtype.ext
  exact MSCountedMovement.afterMove_value (margin N) s.val (mesh c) z

def cost (c : Config N d) (s : Certified c)
    (hfloor : s.val.owner.Valid (2*floor)) (hnt : ¬Stopped c s.val)
    (u : ℝ) (z : MSManuscriptNumericalEpochLedger.Draws s.val) : ℕ :=
  (covariance s.val).cost+SimpleMS.CountedSpectralSampler.drawCost (samplingSpace s.val) u z+
    (value c s hfloor hnt z).cost+3

def implementation (c : Config N d) (s : Certified c)
    (hfloor : s.val.owner.Valid (2*floor)) (hnt : ¬Stopped c s.val) :
    Implementation (movement c s hfloor hnt) where
  Executes z out k draws := ∃u, u∈Ico (0:ℝ) 1 ∧ (SimpleMS.CountedSpectralSampler.pick (samplingSpace s.val) u).value=some z ∧
    out=(value c s hfloor hnt z).value ∧ k=cost c s hfloor hnt u z ∧ draws=1
  result z out k draws h := by
    obtain ⟨u,hu,hp,ho,hk,hr⟩:=h
    exact ho.trans (value_eq c s hfloor hnt z)
  complete z := by
    have hq := short_trace c s hnt
    obtain ⟨u,hu,hp⟩:=RealRAM.CategoricalLabels.complete (SimpleMS.CountedSpectralSampler.table (samplingSpace s.val))
      (SimpleMS.CountedSpectralSampler.weights (samplingSpace s.val)).value
      (fun a => by rw [SimpleMS.CountedSpectralSampler.weights_value]; exact SimpleMS.UniformSampler.weight_positive (samplingSpace s.val) (SimpleMS.Movement.rank_positive _ _ _ hq.2) a)
      (by simp only [SimpleMS.CountedSpectralSampler.weights_value]; exact SimpleMS.UniformSampler.weights_sum (samplingSpace s.val) (SimpleMS.Movement.rank_positive _ _ _ hq.2)) z
    exact ⟨cost c s hfloor hnt u z,1,u,hu,hp,(value_eq c s hfloor hnt z).symm,rfl,rfl⟩

theorem cost_le (c : Config N d) (s : Certified c)
    (hfloor : s.val.owner.Valid (2*floor)) (hnt : ¬Stopped c s.val)
    (u : ℝ) (z : MSManuscriptNumericalEpochLedger.Draws s.val) :
    cost c s hfloor hnt u z≤200000*(N+1)^5 := by
  have hp:=MSGammaTop.physical_cost s.val.owner
  have hq:=MSCovariance.covariance_cost (MSGammaTop.physical s.val.owner).value s.val.point
  have hc:=SimpleMS.CountedSpectralSampler.drawCost_le (samplingSpace s.val) u z
  have hm:=MSCountedMovement.afterMove_cost (margin N) s.val (mesh c) z
  have hd:=s.property.1.dim_le.trans (live_le c)
  have h5 : (N+s.val.owner.dim+1)^5≤32*(N+1)^5 := by
    calc
      _ ≤ (2*(N+1))^5 := Nat.pow_le_pow_left (by omega) 5
      _ = _ := by ring
  have h3 : (N+s.val.owner.dim+1)^3≤(N+s.val.owner.dim+1)^5 := Nat.pow_le_pow_right (by omega) (by omega)
  have hn : (N+1)^3≤(N+1)^5 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : 1≤(N+1)^5 := Nat.one_le_pow _ _ (by omega)
  unfold cost covariance value
  dsimp only
  omega

theorem implementation_bounded (c : Config N d) (s : Certified c)
    (hfloor : s.val.owner.Valid (2*floor)) (hnt : ¬Stopped c s.val) :
    Bounded (implementation c s hfloor hnt) (200000*(N+1)^5) 1 := by
  intro z out k draws h
  obtain ⟨u,hu,hp,ho,rfl,rfl⟩:=h
  exact ⟨cost_le c s hfloor hnt u z,le_rfl⟩

end MatrixSpencer.RectangularRidgeMovementWork
