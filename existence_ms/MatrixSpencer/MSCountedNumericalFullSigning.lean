import MatrixSpencer.MSCountedHalfPhase
import MatrixSpencer.MSCountedFullProcess
import MatrixSpencer.RealRAMMSLabelTransport
import MatrixSpencer.MSManuscriptNumericalFullSigning

/-! Counted composition of the actual numerical full-signing sampler. The
restricted phase is supplied by its counted implementation, and the output
is lifted by explicit scalar sign tests/copies. Restriction/setup work is
charged separately by the concrete input wrapper. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSCountedNumericalFullSigning
open MSManuscriptAdaptive MSCountedSampler MSManuscriptPhase PhaseRestriction
open MSManuscriptNumericalHalfPhase
open RealRAM.JacobiIteration (Counted)
open RealRAM.MSPoint (Table)
variable {ι : Type*} [Fintype ι] [LinearOrder ι] {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
set_option maxRecDepth 12000
attribute [local irreducible] MSManuscriptAdaptive.run MSManuscriptBoundedProcess.run
set_option maxHeartbeats 1200000
variable (H : selfAdjoint (Matrix n n ℂ)) (A : ι→Matrix n n ℂ)
  (hA : ∀i,(A i).IsHermitian) (hN : ∀i,‖A i‖≤1) (ε p : ℝ)
  (P : MSManuscriptNumericalFullSigning.EpochProvider H A hA ε p) (hp : 0≤p)

def phaseSampler (x : Point (ι:=ι) ε) (hx : 0<Fintype.card (Live x.val)) :=
  MSManuscriptNumericalHalfPhase.output (restrictedOffset H A hA x.val)
    (restrictedFamily A x.val) (restrictedFamily_hermitian A hA x.val) ε p
    (P.atPoint x) hp hx ⟨restrictPoint x.val,restrictPoint_regular x.property⟩

theorem lift_value_native (L : Table ι) (x : EuclideanSpace ℝ ι)
    (y : EuclideanSpace ℝ (Live x)) :
    (RealRAM.MSLabelTransport.lift L x y).value=liftPoint x y := by
  ext i
  simp only [RealRAM.MSLabelTransport.lift,liftPoint,mem_frozenCoordinates,IsSign]

def liftOption (L : Table ι) (x : Point (ι:=ι) ε) :
    Option (Point (ι:=Live x.val) ε) → Counted (Option (Point (ι:=ι) ε))
  | none => ⟨none,1⟩
  | some y =>
      let z := RealRAM.MSLabelTransport.lift L x.val y.val
      ⟨some ⟨z.value,by rw [lift_value_native]; exact liftPoint_regular x.property y.property⟩,
        z.cost+2⟩

theorem liftOption_value (L : Table ι) (x : Point (ι:=ι) ε) :
    (fun y => (liftOption ε L x y).value)=Option.map
      (fun y : Point (ι:=Live x.val) ε => (⟨liftPoint x.val y.val,liftPoint_regular x.property y.property⟩ : Point (ι:=ι) ε)) := by
  funext y
  cases y with
  | none => rfl
  | some y =>
    apply congrArg some
    apply Subtype.ext
    exact lift_value_native L x.val y.val

theorem liftOption_cost (L : Table ι) (x : Point (ι:=ι) ε) (y : Option (Point (ι:=Live x.val) ε)) :
    (liftOption ε L x y).cost≤10*Fintype.card ι+3 := by
  cases y with
  | none => dsimp [liftOption]; omega
  | some y => simp only [liftOption,RealRAM.MSLabelTransport.lift_cost]; omega

theorem sample_map_eq (L : Table ι) (x : Point (ι:=ι) ε) (hx : 0<Fintype.card (Live x.val)) :
    (phaseSampler H A hA ε p P hp x hx).map (fun y => (liftOption ε L x y).value)=
      MSManuscriptNumericalFullSigning.sample H A hA ε p P hp x hx := by
  rw [liftOption_value]
  rfl

def sample (L : Table ι)
    (E : ∀x hx,Implementation (phaseSampler H A hA ε p P hp x hx))
    (setup : Point (ι:=ι) ε → ℕ) (x : Point (ι:=ι) ε) (hx : 0<Fintype.card (Live x.val)) :
    Implementation (MSManuscriptNumericalFullSigning.sample H A hA ε p P hp x hx) :=
  congr (sample_map_eq H A hA ε p P hp L x hx)
    (overhead (map (E x hx) (liftOption ε L x)) (setup x))

private theorem weaken {α : Type*} {S : Sampler α} (E : Implementation S) {B C R T : ℕ}
    (h : Bounded E B R) (hb : B≤C) (hr : R≤T) : Bounded E C T := by
  intro z out cost draws he
  have h':=h z out cost draws he
  exact ⟨h'.1.trans hb,h'.2.trans hr⟩

theorem sample_bounded (L : Table ι)
    (E : ∀x hx,Implementation (phaseSampler H A hA ε p P hp x hx))
    (setup : Point (ι:=ι) ε → ℕ) {B J R : ℕ}
    (hE : ∀x hx,Bounded (E x hx) B R) (hJ : ∀x,setup x≤J)
    (x : Point (ι:=ι) ε) (hx : 0<Fintype.card (Live x.val)) :
    Bounded (sample H A hA ε p P hp L E setup x hx) (B+J+10*Fintype.card ι+5) R := by
  apply congr_bounded
  apply weaken _ (overhead_bounded _ (setup x)
    (map_bounded (E x hx) (liftOption ε L x) (hE x hx) (liftOption_cost ε L x)))
  · have hj:=hJ x
    omega
  · exact le_rfl

def output (L : Table ι)
    (E : ∀x hx,Implementation (phaseSampler H A hA ε p P hp x hx))
    (setup : Point (ι:=ι) ε → ℕ) (start : Point (ι:=ι) ε) :
    Implementation (MSManuscriptNumericalFullSigning.output H A hA hN ε p P hp start) :=
  MSCountedFullProcess.output (MSManuscriptNumericalFullSigning.factory H A hA hN ε p P hp)
    (fun x => RealRAM.MSPoint.emptyTest L x.val)
    (fun x => by simp only [RealRAM.MSPoint.emptyTest_value] <;> rfl)
    (sample H A hA ε p P hp L E setup) phaseCost_nonneg (by positivity)
    (Fintype.card ι) (fun x => Fintype.card_subtype_le _) start

theorem output_bounded (L : Table ι)
    (E : ∀x hx,Implementation (phaseSampler H A hA ε p P hp x hx))
    (setup : Point (ι:=ι) ε → ℕ) (start : Point (ι:=ι) ε) {B J R : ℕ}
    (hE : ∀x hx,Bounded (E x hx) B R) (hJ : ∀x,setup x≤J) :
    Bounded (output H A hA hN ε p P hp L E setup start)
      ((Fintype.card ι+1)*(B+J+32*Fintype.card ι+26)+4) ((Fintype.card ι+1)*R) := by
  have h:=MSCountedFullProcess.output_bounded
    (MSManuscriptNumericalFullSigning.factory H A hA hN ε p P hp)
    (fun x => RealRAM.MSPoint.emptyTest L x.val)
    (fun x => by simp only [RealRAM.MSPoint.emptyTest_value] <;> rfl)
    (sample H A hA ε p P hp L E setup) phaseCost_nonneg (by positivity)
    (Fintype.card ι) (fun x => Fintype.card_subtype_le _) start
    (D:=11*Fintype.card ι+6) (fun x => (RealRAM.MSPoint.emptyTest_cost L x.val).le)
    (sample_bounded H A hA ε p P hp L E setup hE hJ)
  convert h using 1 <;> ring

end MatrixSpencer.MSCountedNumericalFullSigning
