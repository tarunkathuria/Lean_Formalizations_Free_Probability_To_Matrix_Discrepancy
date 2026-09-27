import MatrixSpencer.MSCountedAcceptedEpoch
import MatrixSpencer.MSConvexValueEpochFactory

/-! The counted accepted epoch is transported back through the original live
label enumeration and inserted into the original factory sampler. Setup and
output restoration are explicit counted interfaces, to be instantiated by the
stored-label and restriction circuits. Their costs are charged on every call. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSCountedEpochFactory
open MSCountedSampler MSManuscriptAdaptive MSManuscriptPhase PhaseRestriction
open RealRAM.JacobiIteration (Counted)
variable {ι : Type*} [Fintype ι] [LinearOrder ι] {d : ℕ} [Nonempty (Fin d)]
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000

section GenericSetup
variable {α : Type*} {S : Sampler α}

inductive SetupExec (E : Implementation S) (setupCost : ℕ) : S.Draws→α→ℕ→ℕ→Prop where
  | setup (z : S.Draws) (out : α) (cost draws : ℕ) :
      E.Executes z out cost draws → SetupExec E setupCost z out (setupCost+cost+1) draws

def addSetup (E : Implementation S) (setupCost : ℕ) : Implementation S where
  Executes:=SetupExec E setupCost
  result z out cost draws h:=by cases h with | setup _ _ he=>exact E.result _ _ _ _ he
  complete z:=by
    obtain ⟨cost,draws,h⟩:=E.complete z
    exact ⟨setupCost+cost+1,draws,SetupExec.setup z _ cost draws h⟩

theorem addSetup_bounded (E : Implementation S) (setupCost : ℕ) {B R : ℕ} (hE : Bounded E B R) :
    Bounded (addSetup E setupCost) (setupCost+B+1) R := by
  intro z out cost draws h
  cases h with
  | setup _ _ he=>
    have hb:=hE _ _ _ _ he
    constructor <;> omega

end GenericSetup

variable (P : KSPolynomialConvexSolver.PolynomialSolver)
variable (offset : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) (A : ι→Matrix (Fin d) (Fin d) ℂ)
  (hA : ∀i,(A i).IsHermitian) (hN : ∀i,‖A i‖≤1) (ε : ℝ) (hε : 0<ε)
  (hsmall : (Fintype.card ι:ℝ)*ε≤1/1000) (hd : 0<d)

abbrev configuration (x : Point (ι:=ι) ε) (hl : 32≤Fintype.card (Live x.val)) :=
  MSConvexValueEpochFactory.cfg offset A hA hN ε hε hsmall x hl

abbrev Certificate (x : Point (ι:=ι) ε) (hl : 32≤Fintype.card (Live x.val)) :=
  MSManuscriptNumericalEpochRun.Certified (MSManuscriptNumericalConfig.ofEpochConfig
    (configuration offset A hA hN ε hε hsmall x hl) hd)

def outputValue (x : Point (ι:=ι) ε) (hl : 32≤Fintype.card (Live x.val))
    (s : Certificate offset A hA hN ε hε hsmall hd x hl) : Point (ι:=ι) ε×ℝ :=
  (⟨liftPoint x.val (MSConvexValueEpochFactory.restored ε x s.val.point),
    liftPoint_regular x.property (MSManuscriptCoefficientReindex.point_regular _ s.property.1.regular)⟩,
    s.val.time)

def sample (x : Point (ι:=ι) ε) (hl : 32≤Fintype.card (Live x.val)) (r : ℕ) :
    Sampler (Option (Point (ι:=ι) ε×ℝ)) :=
  letI:=RealRAM.MSRawOwnerReport.oracle P
  MSConvexValueEpochFactory.sample offset A hA hN ε hε hsmall hd x hl r

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
    ((MSCountedAcceptedEpoch.output P (configuration offset A hA hN ε hε hsmall x hl) hd r).map
      (fun a=>(mapRestore offset A hA hN ε hε hsmall hd C a).value))=
      sample P offset A hA hN ε hε hsmall hd x hl r := by
  have he : (fun a=>(mapRestore offset A hA hN ε hε hsmall hd C a).value)=
      Option.map (outputValue offset A hA hN ε hε hsmall hd x hl) := by
    funext a
    exact mapRestore_value offset A hA hN ε hε hsmall hd C a
  rw [he]
  rfl

def implementation (x : Point (ι:=ι) ε) (hl : 32≤Fintype.card (Live x.val))
    (C : Routines offset A hA hN ε hε hsmall hd x hl)
    (E : Implementation (MSCountedAcceptedEpoch.trial P
      (configuration offset A hA hN ε hε hsmall x hl) hd)) (r : ℕ) :
    Implementation (sample P offset A hA hN ε hε hsmall hd x hl r) :=
  addSetup (MSCountedSampler.congr (map_eq P offset A hA hN ε hε hsmall hd x hl r C)
    (MSCountedSampler.map (MSCountedAcceptedEpoch.implementation P
      (configuration offset A hA hN ε hε hsmall x hl) hd E r)
      (mapRestore offset A hA hN ε hε hsmall hd C))) C.config.cost

theorem implementation_bounded {N : ℕ} (x : Point (ι:=ι) ε)
    (hl : 32≤Fintype.card (Live x.val)) (hm : Fintype.card (Live x.val)≤N)
    (C : Routines offset A hA hN ε hε hsmall hd x hl)
    (E : Implementation (MSCountedAcceptedEpoch.trial P
      (configuration offset A hA hN ε hε hsmall x hl) hd))
    {B R J K : ℕ} (hE : Bounded E B R) (hJ : C.config.cost≤J)
    (hK : ∀s,(C.restore s).cost≤K) (r : ℕ) :
    Bounded (implementation P offset A hA hN ε hε hsmall hd x hl C E r)
      (J+MSCountedAcceptedEpoch.operations P N d r B+K+4) (r*R) := by
  have hr:=MSCountedAcceptedEpoch.implementation_bounded P
    (configuration offset A hA hN ε hε hsmall x hl) hd hm E hE r
  have hmapped:=MSCountedSampler.map_bounded _ (mapRestore offset A hA hN ε hε hsmall hd C) hr
    (mapRestore_cost offset A hA hN ε hε hsmall hd C hK)
  have hc:=MSCountedSampler.congr_bounded (map_eq P offset A hA hN ε hε hsmall hd x hl r C) _ hmapped
  have hs:=addSetup_bounded _ C.config.cost hc
  intro z out cost draws he
  have hh:=hs z out cost draws he
  constructor <;> omega

end MatrixSpencer.MSCountedEpochFactory
