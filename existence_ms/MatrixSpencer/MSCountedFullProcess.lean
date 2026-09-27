import MatrixSpencer.MSCountedBoundedProcess
import MatrixSpencer.MSManuscriptFullProcess

/-! Cost composition for the actual outer full-coloring process. It executes
at most N+1 successive phases on the chosen history, including both live-set
checks in the source. Probability and output data are unchanged. -/
noncomputable section
namespace MatrixSpencer.MSCountedFullProcess
open MSManuscriptAdaptive MSCountedSampler MSManuscriptFullProcess
open RealRAM.JacobiIteration (Counted)
variable {State : Type*} {live : State→ℕ} {potential : State→ℝ} {B p : ℝ}
attribute [local instance] Classical.propDecidable

def raw (F : Factory live potential B p)
    (test : State → Counted Bool) (htest : ∀x,(test x).value=decide (live x=0))
    (E : ∀x hx,Implementation (F.sample x hx)) (x : State) :
    Implementation (MSManuscriptFullProcess.rawStep F x) := by
  by_cases ht : (test x).value=true
  · have hx : live x=0 := by simpa only [htest,decide_eq_true_eq] using ht
    exact congr (by simp [MSManuscriptFullProcess.rawStep,hx])
      (overhead (pure (some x) 0) ((test x).cost+1))
  · have hx : 0<live x := Nat.pos_of_ne_zero (by simpa only [htest,decide_eq_true_eq] using ht)
    exact congr (by simp [MSManuscriptFullProcess.rawStep,hx])
      (overhead (E x hx) ((test x).cost+1))

theorem raw_bounded (F : Factory live potential B p)
    (test : State → Counted Bool) (htest : ∀x,(test x).value=decide (live x=0))
    (E : ∀x hx,Implementation (F.sample x hx)) {C D R : ℕ}
    (hD : ∀x,(test x).cost≤D) (hE : ∀x hx,Bounded (E x hx) C R) (x : State) :
    Bounded (raw F test htest E x) (C+D+2) R := by
  unfold raw
  split
  · apply congr_bounded
    intro z out cost draws h
    obtain ⟨k,h,rfl⟩ := h
    rcases h with ⟨_,rfl,rfl⟩
    have hd := hD x
    constructor <;> omega
  · apply congr_bounded
    intro z out cost draws h
    obtain ⟨k,h,rfl⟩ := h
    have he := hE _ _ _ _ _ _ h
    have hd := hD x
    constructor <;> omega

def output (F : Factory live potential B p)
    (test : State → Counted Bool) (htest : ∀x,(test x).value=decide (live x=0))
    (E : ∀x hx,Implementation (F.sample x hx)) (hB : 0≤B) (hp : 0≤p)
    (N : ℕ) (hlive : ∀x,live x≤N) (start : State) :
    Implementation (MSManuscriptFullProcess.output F hB hp N hlive start) :=
  MSCountedBoundedProcess.output (config F hB hp N hlive start)
    test (fun s => by simp [config,htest]) (raw F test htest E) (N+1)

theorem output_bounded (F : Factory live potential B p)
    (test : State → Counted Bool) (htest : ∀x,(test x).value=decide (live x=0))
    (E : ∀x hx,Implementation (F.sample x hx)) (hB : 0≤B) (hp : 0≤p)
    (N : ℕ) (hlive : ∀x,live x≤N) (start : State) {C D R : ℕ}
    (hD : ∀x,(test x).cost≤D) (hE : ∀x hx,Bounded (E x hx) C R) :
    Bounded (output F test htest E hB hp N hlive start)
      ((N+1)*(C+2*D+9)+4) ((N+1)*R) := by
  have h := MSCountedBoundedProcess.output_bounded (config F hB hp N hlive start)
    test (fun s => by simp [config,htest]) (raw F test htest E) hD (fun x _ => raw_bounded F test htest E hD hE x) (N+1)
  convert h using 1 <;> ring

end MatrixSpencer.MSCountedFullProcess
