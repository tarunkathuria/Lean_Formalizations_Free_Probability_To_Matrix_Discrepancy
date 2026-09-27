import MatrixSpencer.RectangularRidgePhaseAssembly
import MatrixSpencer.MSCountedBoundedProcess
import MatrixSpencer.RealRAMMSPoint

/-! Primitive original-label tests and execution accounting for the exact
relative half-phase sampler. Proof-ledger attachment is data projection;
neither favorable leaves nor proof predicates are searched at runtime. -/
noncomputable section
namespace MatrixSpencer.RectangularRidgeCountedPhase
open MSManuscriptAdaptive MSCountedSampler RectangularRidgePhaseAssembly
open RectangularRidgeRemainingPotential RectangularRidgePhaseProgress
open RealRAM.JacobiIteration (Counted)
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {f : EuclideanSpace ℝ (Fin N) → ℝ} {ε τ K p : ℝ}

def terminalTest (start x : EuclideanSpace ℝ (Fin N)) : Counted Bool :=
  let a := RealRAM.MSPoint.liveCount (RealRAM.MSPoint.finTable N) start
  let b := RealRAM.MSPoint.liveCount (RealRAM.MSPoint.finTable N) x
  ⟨decide (2 * b.value ≤ a.value ∨ b.value < 32), a.cost + b.cost + 6⟩

theorem terminalTest_value (start x : EuclideanSpace ℝ (Fin N)) :
    (terminalTest start x).value = decide (terminal start x) := by
  simp only [terminalTest, RealRAM.MSPoint.liveCount_value, ← liveCount_eq, terminal]
  congr 1

theorem terminalTest_cost (start x : EuclideanSpace ℝ (Fin N)) :
    (terminalTest start x).cost = 22 * N + 14 := by
  simp only [terminalTest, RealRAM.MSPoint.liveCount_cost, Fintype.card_fin]
  omega

def retained (F : EpochFactory f ε τ K p) (start : Point (N := N) ε)
    (x : PhasePoint start) (hx : 32 ≤ liveCount x.val.val) : Sampler (Option (PhasePoint start)) where
  Draws := (F.sample x.val hx).Draws
  fintypeDraws := inferInstance
  weight := (F.sample x.val hx).weight
  value z := match he : (F.sample x.val hx).value z with
    | none => none
    | some y => some ⟨y.1, x.property.trans (F.sound x.val hx z y he).frozen⟩
  weight_nonneg := (F.sample x.val hx).weight_nonneg
  weight_sum := (F.sample x.val hx).weight_sum

theorem retained_value (F : EpochFactory f ε τ K p) (start : Point (N := N) ε)
    (x : PhasePoint start) (hx : 32 ≤ liveCount x.val.val) (z : (retained F start x hx).Draws) :
    ((retained F start x hx).value z).map Subtype.val = ((F.sample x.val hx).value z).map Prod.fst := by
  simp only [retained]
  split <;> simp_all

def retain (F : EpochFactory f ε τ K p) (start : Point (N := N) ε)
    (x : PhasePoint start) (hx : 32 ≤ liveCount x.val.val)
    (E : Implementation (F.sample x.val hx)) : Implementation (retained F start x hx) where
  Executes z out cost draws := ∃ old k, E.Executes z old k draws ∧
    out.map Subtype.val = old.map Prod.fst ∧ cost = k + 3
  result z out cost draws h := by
    obtain ⟨old, k, he, hout, _⟩ := h
    have hr := E.result z old k draws he
    have hinj : Function.Injective (Option.map (Subtype.val : PhasePoint start → Point ε)) :=
      Option.map_injective Subtype.val_injective
    apply hinj
    rw [hout, hr, retained_value]
  complete z := by
    obtain ⟨k, r, he⟩ := E.complete z
    exact ⟨k + 3, r, (F.sample x.val hx).value z, k, he, retained_value F start x hx z, rfl⟩

theorem retain_bounded (F : EpochFactory f ε τ K p) (start : Point (N := N) ε)
    (x : PhasePoint start) (hx : 32 ≤ liveCount x.val.val)
    (E : Implementation (F.sample x.val hx)) {B R : ℕ} (hE : Bounded E B R) :
    Bounded (retain F start x hx E) (B + 3) R := by
  intro z out cost draws h
  obtain ⟨old, k, he, _, rfl⟩ := h
  have hb := hE z old k draws he
  constructor <;> omega

def raw (F : EpochFactory f ε τ K p) (E : ∀ x hx, Implementation (F.sample x hx))
    (start : Point (N := N) ε) (x : PhasePoint start) :
    Implementation (RectangularRidgePhaseAssembly.rawStep F start x) := by
  by_cases ht : (terminalTest start.val x.val.val).value = true
  · have hx : terminal start.val x.val.val := by
      simpa only [terminalTest_value, decide_eq_true_eq] using ht
    exact congr (by simp [RectangularRidgePhaseAssembly.rawStep, hx])
      (overhead (pure (some x) 0) ((terminalTest start.val x.val.val).cost + 1))
  · have hx : ¬terminal start.val x.val.val := by
      simpa only [terminalTest_value, decide_eq_true_eq] using ht
    have h32 : 32 ≤ liveCount x.val.val := Nat.le_of_not_gt (fun h => hx (Or.inr h))
    exact congr (by simp only [RectangularRidgePhaseAssembly.rawStep, dif_neg hx]; rfl)
      (overhead (retain F start x h32 (E x.val h32)) ((terminalTest start.val x.val.val).cost + 1))

theorem raw_bounded (F : EpochFactory f ε τ K p) (E : ∀ x hx, Implementation (F.sample x hx))
    {B R : ℕ} (hE : ∀ x hx, Bounded (E x hx) B R)
    (start : Point (N := N) ε) (x : PhasePoint start) :
    Bounded (raw F E start x) (B + 22 * N + 18) R := by
  unfold raw
  split
  · apply congr_bounded
    intro z out cost draws h
    obtain ⟨k, h, rfl⟩ := h
    rcases h with ⟨_, rfl, rfl⟩
    rw [terminalTest_cost]
    constructor <;> omega
  · apply congr_bounded
    intro z out cost draws h
    obtain ⟨k, h, rfl⟩ := h
    have hb := retain_bounded F start x _ (E x.val _) (hE x.val _) z out k draws h
    rw [terminalTest_cost]
    constructor <;> omega

def output (F : EpochFactory f ε τ K p) (E : ∀ x hx, Implementation (F.sample x hx))
    (hτ : 0 < τ) (hK : 0 ≤ K) (hp : 0 ≤ p) (start : Point (N := N) ε)
    (hs : 0 < liveCount start.val) (calls : ℕ) :
    Implementation (RectangularRidgePhaseAssembly.output F hτ hK hp start hs calls) :=
  MSCountedBoundedProcess.output (config F hτ hK hp start hs)
    (fun x => terminalTest start.val x.val.val) (fun x => terminalTest_value start.val x.val.val)
    (raw F E start) calls

theorem output_bounded (F : EpochFactory f ε τ K p) (E : ∀ x hx, Implementation (F.sample x hx))
    (hτ : 0 < τ) (hK : 0 ≤ K) (hp : 0 ≤ p) (start : Point (N := N) ε)
    (hs : 0 < liveCount start.val) (calls : ℕ) {B R : ℕ}
    (hE : ∀ x hx, Bounded (E x hx) B R) :
    Bounded (output F E hτ hK hp start hs calls) (calls * (B + 44 * N + 39) + 4) (calls * R) := by
  have hh := MSCountedBoundedProcess.output_bounded (config F hτ hK hp start hs)
    (fun x => terminalTest start.val x.val.val) (fun x => terminalTest_value start.val x.val.val)
    (raw F E start) (B := B + 22 * N + 18) (D := 22 * N + 14)
    (fun x => (terminalTest_cost start.val x.val.val).le) (fun x _ => raw_bounded F E hE start x) calls
  convert hh using 1
  ring

end MatrixSpencer.RectangularRidgeCountedPhase
