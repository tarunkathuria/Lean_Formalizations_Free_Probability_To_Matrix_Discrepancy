import MatrixSpencer.MSCountedEpochFactory
import FaithfulMS.SquareDirectCountedAcceptance
import FaithfulMS.SquareDirectEpochFactory

/-! The counted accepted epoch is transported back through the original live
label enumeration and inserted into the original factory sampler. Setup and
output restoration are explicit counted interfaces, to be instantiated by the
stored-label and restriction circuits. Their costs are charged on every call. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
open MatrixSpencer
namespace FaithfulMS.SquareDirectCountedFactory
open MSCountedSampler MSManuscriptAdaptive MSManuscriptPhase PhaseRestriction
open RealRAM.JacobiIteration (Counted)
variable {ι : Type*} [Fintype ι] [LinearOrder ι] {d : ℕ} [Nonempty (Fin d)]
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000

section GenericSetup
variable {α : Type*} {S : Sampler α}

abbrev SetupExec (E : Implementation S) (setupCost : ℕ) :=
  MSCountedEpochFactory.SetupExec E setupCost

abbrev addSetup (E : Implementation S) (setupCost : ℕ) : Implementation S :=
  MSCountedEpochFactory.addSetup E setupCost

theorem addSetup_bounded (E : Implementation S) (setupCost : ℕ) {B R : ℕ}
    (hE : Bounded E B R) : Bounded (addSetup E setupCost) (setupCost+B+1) R :=
  MSCountedEpochFactory.addSetup_bounded E setupCost hE

end GenericSetup

variable [SquareDirectOracle.Oracle]
variable (offset : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) (A : ι→Matrix (Fin d) (Fin d) ℂ)
  (hA : ∀i,(A i).IsHermitian) (hN : ∀i,‖A i‖≤1) (ε : ℝ) (hε : 0<ε)
  (hsmall : (Fintype.card ι:ℝ)*ε≤1/1000) (hd : 0<d)

abbrev configuration (x : Point (ι:=ι) ε) (hl : 32≤Fintype.card (Live x.val)) :=
  SquareDirectEpochFactory.cfg offset A hA hN ε hε hsmall x hl

abbrev Certificate (x : Point (ι:=ι) ε) (hl : 32≤Fintype.card (Live x.val)) :=
  MSManuscriptNumericalEpochRun.Certified (MSManuscriptNumericalConfig.ofEpochConfig
    (configuration offset A hA hN ε hε hsmall x hl) hd)

def outputValue (x : Point (ι:=ι) ε) (hl : 32≤Fintype.card (Live x.val))
    (s : Certificate offset A hA hN ε hε hsmall hd x hl) : Point (ι:=ι) ε×ℝ :=
  (⟨liftPoint x.val (SquareDirectEpochFactory.restored ε x s.val.point),
    liftPoint_regular x.property (MSManuscriptCoefficientReindex.point_regular _ s.property.1.regular)⟩,
    s.val.time)

def sample (x : Point (ι:=ι) ε) (hl : 32≤Fintype.card (Live x.val)) (r : ℕ) :
    Sampler (Option (Point (ι:=ι) ε×ℝ)) :=
  SquareDirectEpochFactory.sample offset A hA hN ε hε hsmall hd x hl r

structure Routines (x : Point (ι:=ι) ε) (hl : 32≤Fintype.card (Live x.val)) where
  config : Counted (EpochConfig (Fin (Fintype.card (Live x.val))) (Fin d))
  config_value : config.value=configuration offset A hA hN ε hε hsmall x hl
  restore : Certificate offset A hA hN ε hε hsmall hd x hl→ Counted (Point (ι:=ι) ε×ℝ)
  restore_value : ∀s,(restore s).value=outputValue offset A hA hN ε hε hsmall hd x hl s

def mapRestore {x : Point (ι:=ι) ε} {hl : 32≤Fintype.card (Live x.val)}
    (C : Routines offset A hA hN ε hε hsmall hd x hl) :
    Option (Certificate offset A hA hN ε hε hsmall hd x hl)→ Counted (Option (Point (ι:=ι) ε×ℝ))
  | none=>⟨none,1⟩
  | some s=>let t:=C.restore s;⟨some t.value,t.cost+1⟩

theorem mapRestore_value {x : Point (ι:=ι) ε} {hl : 32≤Fintype.card (Live x.val)}
    (C : Routines offset A hA hN ε hε hsmall hd x hl)
    (a : Option (Certificate offset A hA hN ε hε hsmall hd x hl)) :
    (mapRestore offset A hA hN ε hε hsmall hd C a).value=
      a.map (outputValue offset A hA hN ε hε hsmall hd x hl) := by
  cases a with
  | none=>rfl
  | some s=>simp only [mapRestore,C.restore_value,Option.map_some]

theorem mapRestore_cost {x : Point (ι:=ι) ε} {hl : 32≤Fintype.card (Live x.val)}
    (C : Routines offset A hA hN ε hε hsmall hd x hl) {K : ℕ}
    (hC : ∀s,(C.restore s).cost≤K)
    (a : Option (Certificate offset A hA hN ε hε hsmall hd x hl)) :
    (mapRestore offset A hA hN ε hε hsmall hd C a).cost≤K+1 := by
  cases a with
  | none=>simp only [mapRestore];omega
  | some s=>exact Nat.add_le_add_right (hC s) 1

theorem map_eq (x : Point (ι:=ι) ε) (hl : 32≤Fintype.card (Live x.val)) (r : ℕ)
    (C : Routines offset A hA hN ε hε hsmall hd x hl) :
    ((SquareDirectAcceptedEpoch.output (configuration offset A hA hN ε hε hsmall x hl) hd r).map
      (fun a=>(mapRestore offset A hA hN ε hε hsmall hd C a).value))=
      sample offset A hA hN ε hε hsmall hd x hl r := by
  have he : (fun a=>(mapRestore offset A hA hN ε hε hsmall hd C a).value)=
      Option.map (outputValue offset A hA hN ε hε hsmall hd x hl) := by
    funext a
    exact mapRestore_value offset A hA hN ε hε hsmall hd C a
  rw [he]
  rfl

def implementation (x : Point (ι:=ι) ε) (hl : 32≤Fintype.card (Live x.val))
    (C : Routines offset A hA hN ε hε hsmall hd x hl) (r : ℕ)
    (E : Implementation (SquareDirectAcceptedEpoch.output
      (configuration offset A hA hN ε hε hsmall x hl) hd r)) :
    Implementation (sample offset A hA hN ε hε hsmall hd x hl r) :=
  addSetup (MSCountedSampler.congr (map_eq offset A hA hN ε hε hsmall hd x hl r C)
    (MSCountedSampler.map E (mapRestore offset A hA hN ε hε hsmall hd C))) C.config.cost

theorem implementation_bounded (x : Point (ι:=ι) ε)
    (hl : 32≤Fintype.card (Live x.val))
    (C : Routines offset A hA hN ε hε hsmall hd x hl) (r : ℕ)
    (E : Implementation (SquareDirectAcceptedEpoch.output
      (configuration offset A hA hN ε hε hsmall x hl) hd r))
    {B R J K : ℕ} (hE : Bounded E B R) (hJ : C.config.cost≤J)
    (hK : ∀s,(C.restore s).cost≤K) :
    Bounded (implementation offset A hA hN ε hε hsmall hd x hl C r E)
      (J+B+K+4) R := by
  have hmapped := MSCountedSampler.map_bounded E
    (mapRestore offset A hA hN ε hε hsmall hd C) hE
    (mapRestore_cost offset A hA hN ε hε hsmall hd C hK)
  have hc := MSCountedSampler.congr_bounded
    (map_eq offset A hA hN ε hε hsmall hd x hl r C) _ hmapped
  have hs := addSetup_bounded _ C.config.cost hc
  intro z out cost draws he
  have hh := hs z out cost draws he
  constructor <;> omega

end FaithfulMS.SquareDirectCountedFactory
