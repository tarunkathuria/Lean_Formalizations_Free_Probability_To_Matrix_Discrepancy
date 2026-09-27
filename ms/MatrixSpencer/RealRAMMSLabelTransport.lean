import MatrixSpencer.RealRAMMSLabelTable

/-! Realized coefficient permutation using an explicitly stored ordered
label array. Every forward and inverse array lookup is a finite scan, and
all coordinate/matrix copies are included in the displayed costs. -/
noncomputable section
namespace MatrixSpencer.RealRAM.MSLabelTransport
open JacobiIteration (Counted)
open MSPoint MSLabelTable PhaseRestriction
variable {ι : Type*} [Fintype ι] [LinearOrder ι]
attribute [local instance] Classical.propDecidable

def point (L : Table ι) (x : EuclideanSpace ℝ ι) : Counted (EuclideanSpace ℝ (Fin (Fintype.card ι))) :=
  ⟨WithLp.toLp 2 (fun j => ((lookup L.labels j).value.map (fun i => x i)).getD 0),
    Fintype.card ι*(3*L.labels.length+4)+1⟩

theorem point_value (L : Table ι) (hL : Ordered L) (x : EuclideanSpace ℝ ι) :
    (point L x).value=MSManuscriptCoefficientReindex.point (MSManuscriptCoefficientReindex.enumeration ι) x := by
  ext j
  change ((lookup L.labels j).value.map (fun i => x i)).getD 0=x (MSManuscriptCoefficientReindex.enumeration ι j)
  rw [enumeration_lookup L hL]
  rfl

theorem point_cost (L : Table ι) (x : EuclideanSpace ℝ ι) :
    (point L x).cost=Fintype.card ι*(3*Fintype.card ι+4)+1 := by simp [point,table_length]

def family {d : ℕ} (L : Table ι) (A : ι→Matrix (Fin d) (Fin d) ℂ) :
    Counted (Fin (Fintype.card ι)→Matrix (Fin d) (Fin d) ℂ) :=
  ⟨fun j a b => ((lookup L.labels j).value.map (fun i => A i a b)).getD 0,
    Fintype.card ι*d*d*(3*L.labels.length+6)+1⟩

theorem family_value {d : ℕ} (L : Table ι) (hL : Ordered L) (A : ι→Matrix (Fin d) (Fin d) ℂ) :
    (family L A).value=fun j => A (MSManuscriptCoefficientReindex.enumeration ι j) := by
  funext j a b
  simp only [family,enumeration_lookup L hL,Option.map_some,Option.getD_some]

theorem family_cost {d : ℕ} (L : Table ι) (A : ι→Matrix (Fin d) (Fin d) ℂ) :
    (family L A).cost=Fintype.card ι*d*d*(3*Fintype.card ι+6)+1 := by simp [family,table_length]

def restore (L : Table ι) (x : EuclideanSpace ℝ (Fin (Fintype.card ι))) : Counted (EuclideanSpace ℝ ι) :=
  ⟨WithLp.toLp 2 (fun i =>
    let j := index i L.labels
    if h : j.value<Fintype.card ι then x ⟨j.value,h⟩ else 0),
    Fintype.card ι*(6*L.labels.length+6)+1⟩

theorem restore_value (L : Table ι) (hL : Ordered L) (x : EuclideanSpace ℝ (Fin (Fintype.card ι))) :
    (restore L x).value=MSManuscriptCoefficientReindex.point (MSManuscriptCoefficientReindex.enumeration ι).symm x := by
  ext i
  change (if h : (index i L.labels).value<Fintype.card ι then x ⟨(index i L.labels).value,h⟩ else 0)=
    x ((MSManuscriptCoefficientReindex.enumeration ι).symm i)
  simp only [enumeration_inverse L hL,Fin.isLt,↓reduceDIte]
  exact congrArg x (Fin.ext (enumeration_inverse L hL i))

theorem restore_cost (L : Table ι) (x : EuclideanSpace ℝ (Fin (Fintype.card ι))) :
    (restore L x).cost=Fintype.card ι*(6*Fintype.card ι+6)+1 := by simp [restore,table_length]

/-- Scalar tests and copies lifting a stored live-coordinate point. -/
def lift (L : Table ι) (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ (Live x)) :
    Counted (EuclideanSpace ℝ ι) :=
  ⟨WithLp.toLp 2 (fun i => if h : x i=1 ∨ x i = -1 then x i
    else y ⟨i,by simpa only [mem_frozenCoordinates,IsSign] using h⟩),10*L.labels.length+1⟩

theorem lift_value (L : Table ι) (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ (Live x)) :
    (lift L x y).value=liftPoint x y := by
  ext i
  simp only [lift,liftPoint,mem_frozenCoordinates,IsSign]

theorem lift_cost (L : Table ι) (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ (Live x)) :
    (lift L x y).cost=10*Fintype.card ι+1 := by simp [lift,table_length]

def restoreLift (L : Table ι) (x : EuclideanSpace ℝ ι)
    (y : EuclideanSpace ℝ (Fin (Fintype.card (Live x)))) : Counted (EuclideanSpace ℝ ι) :=
  let tab := restricted L x
  let y' := restore tab.value y
  let z := lift L x y'.value
  ⟨z.value,tab.cost+y'.cost+z.cost+2⟩

theorem restoreLift_value (L : Table ι) (hL : Ordered L) (x : EuclideanSpace ℝ ι)
    (y : EuclideanSpace ℝ (Fin (Fintype.card (Live x)))) :
    (restoreLift L x y).value=liftPoint x
      (MSManuscriptCoefficientReindex.point (MSManuscriptCoefficientReindex.enumeration (Live x)).symm y) := by
  simp only [restoreLift,lift_value,restore_value _ (restricted_ordered L hL x)]

theorem restoreLift_cost (L : Table ι) (x : EuclideanSpace ℝ ι)
    (y : EuclideanSpace ℝ (Fin (Fintype.card (Live x)))) :
    (restoreLift L x y).cost≤30*(Fintype.card ι+1)^2 := by
  have hk : Fintype.card (Live x)≤Fintype.card ι := Fintype.card_subtype_le _
  have hp := Nat.mul_self_le_mul_self hk
  simp only [restoreLift,restricted_cost,restore_cost,lift_cost]
  nlinarith

end MatrixSpencer.RealRAM.MSLabelTransport
