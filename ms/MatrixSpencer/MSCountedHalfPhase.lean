import MatrixSpencer.MSCountedBoundedProcess
import MatrixSpencer.RealRAMMSPoint

/-! Execution accounting for the actual adaptive half-phase. Both terminal
checks present in the source are charged, only the sampled epoch continuation
is followed, and the final small-live nearest-sign scan is counted. -/
noncomputable section
namespace MatrixSpencer.MSCountedHalfPhase
open MSManuscriptAdaptive MSCountedSampler MSManuscriptPhase
open RealRAM.JacobiIteration (Counted)
open RealRAM.MSPoint (Table)
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] [Nonempty n]
attribute [local instance] Classical.propDecidable
variable {potential : EuclideanSpace ℝ ι → ℝ} {ε τ B p : ℝ}

def rawStep (L : Table ι) (F : Factory potential ε τ B p)
    (E : ∀ x hx, Implementation (F.sample x hx)) (x : Point (ι:=ι) ε) :
    Implementation (MSManuscriptPhase.rawStep F x) := by
  by_cases ht : (RealRAM.MSPoint.terminalTest L x.val).value=true
  · have hx : FiniteHalfPhase.Terminal x.val := by
      simpa only [RealRAM.MSPoint.terminalTest_value,decide_eq_true_eq] using ht
    exact congr (by simp [MSManuscriptPhase.rawStep,hx])
      (overhead (pure (some x) 0) ((RealRAM.MSPoint.terminalTest L x.val).cost+1))
  · have hx : ¬FiniteHalfPhase.Terminal x.val := by
      simpa only [RealRAM.MSPoint.terminalTest_value,decide_eq_true_eq] using ht
    exact congr (by simp [MSManuscriptPhase.rawStep,hx])
      (overhead (map (E x hx) (fun y => ⟨y.map Prod.fst,1⟩))
        ((RealRAM.MSPoint.terminalTest L x.val).cost+1))

theorem rawStep_bounded (L : Table ι) (F : Factory potential ε τ B p)
    (E : ∀ x hx, Implementation (F.sample x hx)) {C R : ℕ}
    (hE : ∀ x hx, Bounded (E x hx) C R) (x : Point (ι:=ι) ε) :
    Bounded (rawStep L F E x) (C+12*Fintype.card ι+13) R := by
  unfold rawStep
  split
  · apply congr_bounded
    intro z out cost draws h
    obtain ⟨k,h,rfl⟩ := h
    rcases h with ⟨_,rfl,rfl⟩
    rw [RealRAM.MSPoint.terminalTest_cost]
    constructor <;> omega
  · apply congr_bounded
    intro z out cost draws h
    obtain ⟨k,h,rfl⟩ := h
    have hb := map_bounded _ (fun y => (⟨y.map Prod.fst,1⟩ : Counted (Option (Point (ι:=ι) ε))))
      (C := 1) (hE _ _) (fun _ => le_rfl) _ _ _ _ h
    rw [RealRAM.MSPoint.terminalTest_cost]
    constructor <;> omega

def terminal (L : Table ι) (F : Factory potential ε τ B p)
    (E : ∀ x hx, Implementation (F.sample x hx)) (hτ : 0<τ)
    (hk : 0<Fintype.card ι) (hB : 0≤B) (hp : 0≤p)
    (start : Point (ι:=ι) ε) (K : ℕ) :
    Implementation (MSManuscriptPhase.output F hτ hk hB hp start K) :=
  MSCountedBoundedProcess.output (config F hτ hk hB hp start)
    (fun x => RealRAM.MSPoint.terminalTest L x.val)
    (fun x => RealRAM.MSPoint.terminalTest_value L x.val) (rawStep L F E) K

theorem terminal_bounded (L : Table ι) (F : Factory potential ε τ B p)
    (E : ∀ x hx, Implementation (F.sample x hx)) (hτ : 0<τ)
    (hk : 0<Fintype.card ι) (hB : 0≤B) (hp : 0≤p)
    (start : Point (ι:=ι) ε) (K : ℕ) {C R : ℕ}
    (hE : ∀ x hx, Bounded (E x hx) C R) :
    Bounded (terminal L F E hτ hk hB hp start K)
      (K*(C+24*Fintype.card ι+29)+4) (K*R) := by
  have h := MSCountedBoundedProcess.output_bounded
    (config F hτ hk hB hp start)
    (fun x => RealRAM.MSPoint.terminalTest L x.val)
    (fun x => RealRAM.MSPoint.terminalTest_value L x.val) (rawStep L F E)
    (B:=C+12*Fintype.card ι+13) (D:=12*Fintype.card ι+9)
    (fun x => (RealRAM.MSPoint.terminalTest_cost L x.val).le)
    (fun x _ => rawStep_bounded L F E hE x) K
  convert h using 1 <;> ring

open MSManuscriptNumericalHalfPhase
variable (offset : selfAdjoint (Matrix n n ℂ)) (A : ι→Matrix n n ℂ)
  (hA : ∀ i,(A i).IsHermitian)

def output (L : Table ι) (F : EpochFactory offset A hA ε p)
    (E : ∀ x hx, Implementation (F.sample x hx)) (hp : 0≤p)
    (hk : 0<Fintype.card ι) (start : Point (ι:=ι) ε) :
    Implementation (MSManuscriptNumericalHalfPhase.output offset A hA ε p F hp hk start) := by
  let f : Option (Point (ι:=ι) ε) → Counted (Option (Point (ι:=ι) ε)) := fun x =>
    match x with
    | none => ⟨none,1⟩
    | some x => let y := RealRAM.MSPoint.finish L ε x; ⟨some y.value,y.cost+1⟩
  have hf : (fun x => (f x).value)=Option.map (MSManuscriptNumericalHalfPhase.finish ε) := by
    funext x
    cases x <;> simp [f,RealRAM.MSPoint.finish_value]
  exact congr (by rw [hf]; rfl)
    (map (terminal L F E epochTime_pos hk epochCost_nonneg hp start epochCalls) f)

theorem output_bounded (L : Table ι) (F : EpochFactory offset A hA ε p)
    (E : ∀ x hx, Implementation (F.sample x hx)) (hp : 0≤p)
    (hk : 0<Fintype.card ι) (start : Point (ι:=ι) ε) {C R : ℕ}
    (hE : ∀ x hx, Bounded (E x hx) C R) :
    Bounded (output offset A hA L F E hp hk start)
      (epochCalls*(C+24*Fintype.card ι+29)+17*Fintype.card ι+15)
      (epochCalls*R) := by
  unfold output
  apply congr_bounded
  have hf : ∀ x : Option (Point (ι:=ι) ε),
      (match x with
      | none => (⟨none,1⟩ : Counted (Option (Point (ι:=ι) ε)))
      | some x => let y := RealRAM.MSPoint.finish L ε x; ⟨some y.value,y.cost+1⟩).cost
      ≤ 17*Fintype.card ι+9 := by
    intro x
    cases x with
    | none => dsimp; omega
    | some x => exact Nat.add_le_add_right (RealRAM.MSPoint.finish_cost L ε x) 1
  have h := map_bounded _ _ (terminal_bounded L F E epochTime_pos hk epochCost_nonneg hp start epochCalls hE) hf
  convert h using 1 <;> ring

end MatrixSpencer.MSCountedHalfPhase
