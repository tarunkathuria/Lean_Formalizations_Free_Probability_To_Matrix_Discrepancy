import MatrixSpencer.MSManuscriptNumericalProvider
import MatrixSpencer.MSConvexValueEpochFactory

/-! Primitive-input numerical epoch provider. Physical matrix coordinates are
permuted by an explicit supplied finite equivalence. Each subsequently live
coefficient family is increasingly enumerated by the numerical epoch factory.
There is no report, moment, transition, epoch factory or provider hypothesis. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSConvexValueProvider
variable [MSConvexOwnerValue.Oracle]
open PhaseRestriction MSManuscriptPhase MSManuscriptNumericalHalfPhase MSManuscriptMatrixReindex
variable {ι n : Type*} [Fintype ι] [LinearOrder ι] [Fintype n] [DecidableEq n] [Nonempty n]
variable {d : ℕ}
local instance {m : Type*} [Fintype m] [DecidableEq m] : CStarAlgebra (Matrix m m ℂ) := {}
set_option maxHeartbeats 1200000

variable (e : Fin d≃n) (hd : 0<d)
    (offset : selfAdjoint (Matrix n n ℂ)) (A : ι→Matrix n n ℂ)
    (hA : ∀i,(A i).IsHermitian) (hN : ∀i,‖A i‖≤1) (ε : ℝ) (hε : 0<ε)
    (hsmall : (Fintype.card ι:ℝ)*ε≤1/1000)

def factory (r : ℕ) : EpochFactory offset A hA ε ((301/800:ℝ)^r) := by
  letI : Nonempty (Fin d):=Fin.pos_iff_nonempty.mp hd
  let H':=selfAdjointReindex e offset
  let A':=fun i=>(A i).submatrix e e
  let hA':=fun i=>(hA i).submatrix e
  have hN' : ∀i,‖A' i‖≤1:=fun i=>reindex_contraction e (hN i)
  have heq : remainingPotential H' A' hA'=remainingPotential offset A hA := by
    funext x
    exact remainingPotential_reindex e offset A hA x
  let F:=MSConvexValueEpochFactory.factory H' A' hA' hN' ε hε hsmall hd r
  exact {
    sample:=F.sample
    sound:=fun x hx z y ho=>by
      have hh:=F.sound x hx z y ho
      simpa only [heq] using hh
    failure_le:=F.failure_le }

/-- The actual factories for every outer live family. This is concrete data
built from the input family and finite retry count, not a supplied interface. -/
def provider (r : ℕ) : MSManuscriptNumericalFullSigning.EpochProvider offset A hA ε ((301/800:ℝ)^r) where
  atPoint x:=factory e hd (restrictedOffset offset A hA x.val) (restrictedFamily A x.val)
    (restrictedFamily_hermitian A hA x.val) (restrictedFamily_contractions A hN x.val) ε hε
    ((mul_le_mul_of_nonneg_right
      (show (Fintype.card (Live x.val):ℝ)≤Fintype.card ι from by
        exact_mod_cast Fintype.card_subtype_le (fun i=>i∉frozenCoordinates x.val)) hε.le).trans hsmall) r

/-- Fully numerical adaptive signing output with original coefficient labels. -/
def output (r : ℕ) (start : Point (ι:=ι) ε) :
    MSManuscriptAdaptive.Sampler (Option (Point (ι:=ι) ε)) :=
  MSManuscriptNumericalFullSigning.output offset A hA hN ε ((301/800:ℝ)^r)
    (provider e hd offset A hA hN ε hε hsmall r) (by positivity) start

theorem output_sound (r : ℕ) (start : Point (ι:=ι) ε)
    (z : (output e hd offset A hA hN ε hε hsmall r start).Draws)
    (y : Point (ι:=ι) ε)
    (ho : (output e hd offset A hA hN ε hε hsmall r start).value z=some y) :
    (∀i,IsSign (y.val i)) ∧ remainingPotential offset A hA y.val≤remainingPotential offset A hA start.val+
      4*phaseCost*Real.sqrt (Fintype.card (Live start.val):ℝ) :=
  MSManuscriptNumericalFullSigning.output_sound offset A hA hN ε ((301/800:ℝ)^r)
    (provider e hd offset A hA hN ε hε hsmall r) (by positivity) start z y ho

theorem output_event_probability (r : ℕ) (start : Point (ι:=ι) ε) :
    1-((Fintype.card ι+1:ℕ):ℝ)*((epochCalls:ℝ)*(301/800:ℝ)^r)≤
      ∑z:(output e hd offset A hA hN ε hε hsmall r start).Draws,
        (output e hd offset A hA hN ε hε hsmall r start).weight z*
        (if ((output e hd offset A hA hN ε hε hsmall r start).value z).isSome then 1 else 0) :=
  MSManuscriptNumericalFullSigning.output_event_probability offset A hA hN ε ((301/800:ℝ)^r)
    (provider e hd offset A hA hN ε hε hsmall r) (by positivity) start

end MatrixSpencer.MSConvexValueProvider
