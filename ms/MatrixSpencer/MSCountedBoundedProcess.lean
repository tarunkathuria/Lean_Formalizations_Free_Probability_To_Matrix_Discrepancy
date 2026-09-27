import MatrixSpencer.MSCountedAdaptive

/-! Runtime composition for the original bounded-progress sampler. Its
terminal test must have a counted implementation equal to the actual test;
its step execution is supplied by the concrete lower-level sampler. The
progress and potential proof fields have no runtime tests. -/

noncomputable section
namespace MatrixSpencer.MSCountedBoundedProcess
open MSManuscriptAdaptive MSCountedSampler
open RealRAM.JacobiIteration (Counted)
variable {State : Type*}
attribute [local instance] Classical.propDecidable

def raw (P : MSManuscriptBoundedProcess.Config State)
    (test : State → Counted Bool) (htest : ∀ s, (test s).value=decide (P.terminal s))
    (E : ∀ s, Implementation (P.step s)) (s : State) :
    Implementation (MSManuscriptBoundedProcess.rawStep P s) := by
  by_cases ht : (test s).value=true
  · have hs : P.terminal s := by simpa only [htest, decide_eq_true_eq] using ht
    exact congr (by simp [MSManuscriptBoundedProcess.rawStep,hs])
      (overhead (pure (some s) 0) ((test s).cost+1))
  · have hs : ¬P.terminal s := by simpa only [htest, decide_eq_true_eq] using ht
    exact congr (by simp [MSManuscriptBoundedProcess.rawStep,hs])
      (overhead (E s) ((test s).cost+1))

theorem raw_bounded (P : MSManuscriptBoundedProcess.Config State)
    (test : State → Counted Bool) (htest : ∀ s, (test s).value=decide (P.terminal s))
    (E : ∀ s, Implementation (P.step s)) {B D R : ℕ}
    (hD : ∀ s, (test s).cost ≤ D)
    (hE : ∀ s, ¬P.terminal s → Bounded (E s) B R) (s : State) :
    Bounded (raw P test htest E s) (B+D+2) R := by
  unfold raw
  split
  · apply congr_bounded
    intro z out cost draws h
    obtain ⟨k,h,rfl⟩ := h
    rcases h with ⟨_,rfl,rfl⟩
    have hd := hD s
    constructor <;> omega
  · rename_i ht
    apply congr_bounded
    intro z out cost draws h
    obtain ⟨k,h,rfl⟩ := h
    have hs : ¬P.terminal s := by simpa only [htest, decide_eq_true_eq] using ht
    have hb := hE s hs _ _ _ _ h
    have hd := hD s
    constructor <;> omega

def stage (P : MSManuscriptBoundedProcess.Config State)
    (test : State → Counted Bool) (htest : ∀ s, (test s).value=decide (P.terminal s))
    (E : ∀ s, Implementation (P.step s)) (k : ℕ)
    (s : MSManuscriptBoundedProcess.Stage P k) :
    Implementation (MSManuscriptBoundedProcess.step P k s) :=
  certify (raw P test htest E s.val) _ (MSManuscriptBoundedProcess.rawStep_sound P k s)

theorem stage_bounded (P : MSManuscriptBoundedProcess.Config State)
    (test : State → Counted Bool) (htest : ∀ s, (test s).value=decide (P.terminal s))
    (E : ∀ s, Implementation (P.step s)) {B D R : ℕ}
    (hD : ∀ s, (test s).cost ≤ D)
    (hE : ∀ s, ¬P.terminal s → Bounded (E s) B R) (k : ℕ)
    (s : MSManuscriptBoundedProcess.Stage P k) :
    Bounded (stage P test htest E k s) (B+D+4) R := by
  exact certify_bounded _ _ _ (raw_bounded P test htest E hD hE s.val)

def run (P : MSManuscriptBoundedProcess.Config State)
    (test : State → Counted Bool) (htest : ∀ s, (test s).value=decide (P.terminal s))
    (E : ∀ s, Implementation (P.step s)) (K : ℕ) :
    Implementation (MSManuscriptBoundedProcess.run P K) :=
  adaptiveRun (stage P test htest E) (MSManuscriptBoundedProcess.initial P) K

theorem run_bounded (P : MSManuscriptBoundedProcess.Config State)
    (test : State → Counted Bool) (htest : ∀ s, (test s).value=decide (P.terminal s))
    (E : ∀ s, Implementation (P.step s)) {B D R : ℕ}
    (hD : ∀ s, (test s).cost ≤ D)
    (hE : ∀ s, ¬P.terminal s → Bounded (E s) B R) (K : ℕ) :
    Bounded (run P test htest E K) (K*(B+D+7)+1) (K*R) := by
  exact adaptiveRun_bounded _ _ (stage_bounded P test htest E hD hE) K

def output (P : MSManuscriptBoundedProcess.Config State)
    (test : State → Counted Bool) (htest : ∀ s, (test s).value=decide (P.terminal s))
    (E : ∀ s, Implementation (P.step s)) (K : ℕ) :
    Implementation (MSManuscriptBoundedProcess.output P K) :=
  map (run P test htest E K) (fun s => ⟨s.map Subtype.val,1⟩)

theorem output_bounded (P : MSManuscriptBoundedProcess.Config State)
    (test : State → Counted Bool) (htest : ∀ s, (test s).value=decide (P.terminal s))
    (E : ∀ s, Implementation (P.step s)) {B D R : ℕ}
    (hD : ∀ s, (test s).cost ≤ D)
    (hE : ∀ s, ¬P.terminal s → Bounded (E s) B R) (K : ℕ) :
    Bounded (output P test htest E K) (K*(B+D+7)+4) (K*R) := by
  have h := MSCountedSampler.map_bounded (run P test htest E K)
    (fun s => (⟨s.map Subtype.val,1⟩ : Counted (Option State)))
    (B := K*(B+D+7)+1) (C := 1) (run_bounded P test htest E hD hE K)
    (fun _ => le_rfl)
  convert h using 1 <;> ring

end MatrixSpencer.MSCountedBoundedProcess
