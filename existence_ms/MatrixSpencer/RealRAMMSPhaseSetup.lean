import MatrixSpencer.RealRAMMSRestriction
import MatrixSpencer.MSCountedOriginalPhases

/-! Outer phase data from the stored original coefficient array. The flat
physical family has been materialized by input setup. Each phase computes
its frozen offset, live-label table, restricted family, and starting point. -/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RealRAM.MSPhaseSetup
open JacobiIteration (Counted)
open MSPoint PhaseRestriction
variable {ι n : Type*} [Fintype ι] [LinearOrder ι] [Fintype n] [DecidableEq n]
  {d : ℕ} [Nonempty (Fin d)]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}

structure Data (x : EuclideanSpace ℝ ι) where
  labels : Table (Live x)
  offset : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)
  matrices : Live x→Matrix (Fin d) (Fin d) ℂ
  start : EuclideanSpace ℝ (Live x)

def setup (L : Table ι) (e : Fin d≃n) (A : ι→Matrix n n ℂ)
    (hA : ∀i,(A i).IsHermitian) (x : EuclideanSpace ℝ ι) : Counted (Data (d:=d) x) :=
  let labels := restricted L x
  let H := MSRestriction.offset L 0 (fun i => (A i).submatrix e e) (fun i => (hA i).submatrix e) x
  let family := MSRestriction.family L (fun i => (A i).submatrix e e) x
  let start := MSRestriction.point L x
  ⟨⟨labels.value,H.value,family.value,start.value⟩,labels.cost+H.cost+family.cost+start.cost+5⟩

theorem setup_labels (L : Table ι) (e : Fin d≃n) (A : ι→Matrix n n ℂ)
    (hA : ∀i,(A i).IsHermitian) (x : EuclideanSpace ℝ ι) :
    (setup L e A hA x).value.labels=(restricted L x).value := rfl

theorem setup_offset (L : Table ι) (e : Fin d≃n) (A : ι→Matrix n n ℂ)
    (hA : ∀i,(A i).IsHermitian) (x : EuclideanSpace ℝ ι) :
    (setup L e A hA x).value.offset=MSCountedOriginalPhases.innerH e A hA x := by
  have hz : MSManuscriptMatrixReindex.selfAdjointReindex e (0:selfAdjoint (Matrix n n ℂ))=0 := by
    apply Subtype.ext
    ext i j
    rfl
  change (MSRestriction.offset L 0 (fun i => (A i).submatrix e e) (fun i => (hA i).submatrix e) x).value=_
  rw [MSRestriction.offset_value]
  exact hz ▸ MSRestriction.restrictedOffset_reindex e 0 A hA x

theorem setup_family (L : Table ι) (e : Fin d≃n) (A : ι→Matrix n n ℂ)
    (hA : ∀i,(A i).IsHermitian) (x : EuclideanSpace ℝ ι) :
    (setup L e A hA x).value.matrices=MSCountedOriginalPhases.innerA e A x := rfl

theorem setup_start (L : Table ι) (e : Fin d≃n) (A : ι→Matrix n n ℂ)
    (hA : ∀i,(A i).IsHermitian) (x : EuclideanSpace ℝ ι) :
    (setup L e A hA x).value.start=restrictPoint x := rfl

def setupCost (N d : ℕ) : ℕ := 200*(N+1)*(d+1)^2

theorem setup_cost (L : Table ι) (e : Fin d≃n) (A : ι→Matrix n n ℂ)
    (hA : ∀i,(A i).IsHermitian) (x : EuclideanSpace ℝ ι) :
    (setup L e A hA x).cost≤setupCost (Fintype.card ι) d := by
  have ht:=restricted_cost L x
  have ho:=MSRestriction.offset_cost L 0 (fun i => (A i).submatrix e e) (fun i => (hA i).submatrix e) x
  have hf:=MSRestriction.family_cost L (fun i => (A i).submatrix e e) x
  have hp:=MSRestriction.point_cost L x
  have hn : Fintype.card ι+1≤(Fintype.card ι+1)*(d+1)^2 :=
    Nat.le_mul_of_pos_right _ (by positivity)
  dsimp only [setup]
  unfold setupCost
  nlinarith

end MatrixSpencer.RealRAM.MSPhaseSetup
