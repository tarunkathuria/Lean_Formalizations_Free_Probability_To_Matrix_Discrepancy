import MatrixSpencer.MSManuscriptNumericalSamplerMovement
import Mathlib.Data.List.NodupEquivFin
import MatrixSpencer.MSManuscriptNumericalLDL

/-! Ordered positive-pivot enumeration for the actual LDL sampling data.
Both directions of the index equivalence are list lookup/search on the computed
finite list. No positive-weight branch is selected by an existence proof. -/
open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.MSManuscriptNumericalSamplerData
variable {d : ℕ}

def labels (Q : Matrix (Fin d) (Fin d) ℝ) : List (Fin d) :=
  (List.finRange d).filter (fun j => decide (0<MSManuscriptNumericalLDL.pivot Q j))
def count (Q : Matrix (Fin d) (Fin d) ℝ) := (labels Q).length

theorem labels_nodup (Q : Matrix (Fin d) (Fin d) ℝ) : (labels Q).Nodup :=
  (List.nodup_finRange d).filter _
theorem mem_labels (Q : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) :
    j∈labels Q↔0<KSEighthManuscriptLDL.pivot Q j := by simp [labels]

def indexEquiv (Q : Matrix (Fin d) (Fin d) ℝ) : Fin (count Q) ≃ MSManuscriptNumericalSampler.Index Q :=
  ((labels_nodup Q).getEquiv (labels Q)).trans
    { toFun := fun j => ⟨j.val,(mem_labels Q j.val).mp j.property⟩
      invFun := fun j => ⟨j.val,(mem_labels Q j.val).mpr j.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

abbrev Draws (Q : Matrix (Fin d) (Fin d) ℝ) := Fin (count Q) × Bool

def drawEquiv (Q : Matrix (Fin d) (Fin d) ℝ) : Draws Q ≃ MSManuscriptNumericalSampler.Draws Q :=
  Equiv.prodCongr (indexEquiv Q) (Equiv.refl Bool)
def selectedLabel (Q : Matrix (Fin d) (Fin d) ℝ) (s : Draws Q) : Fin d := (labels Q).get s.1

@[simp] theorem selectedLabel_eq (Q : Matrix (Fin d) (Fin d) ℝ) (s : Draws Q) :
    selectedLabel Q s=(drawEquiv Q s).1.val := rfl

def columnEnergy (Q : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) : ℝ :=
  ∑i,(MSManuscriptNumericalLDL.lowerColumn Q j i)^2

def weight (Q : Matrix (Fin d) (Fin d) ℝ) (s : Draws Q) :=
  MSManuscriptNumericalLDL.pivot Q (selectedLabel Q s) * columnEnergy Q (selectedLabel Q s) /
    (2*realTrace Q)
def increment (Q : Matrix (Fin d) (Fin d) ℝ) (s : Draws Q) : EuclideanSpace ℝ (Fin d) :=
  let j := selectedLabel Q s
  let v := (Real.sqrt (realTrace Q)/Real.sqrt (columnEnergy Q j)) •
    (WithLp.toLp 2 (MSManuscriptNumericalLDL.lowerColumn Q j) : EuclideanSpace ℝ (Fin d))
  if s.2 then v else -v

@[simp] theorem columnEnergy_eq (Q : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) :
    columnEnergy Q j=MSManuscriptNumericalSampler.columnEnergy Q j := by
  simp only [columnEnergy,MSManuscriptNumericalLDL.lowerColumn_eq]
  rfl

@[simp] theorem weight_eq (Q : Matrix (Fin d) (Fin d) ℝ) (s : Draws Q) :
    weight Q s=MSManuscriptNumericalSampler.weight Q (drawEquiv Q s) := by
  simp only [weight,MSManuscriptNumericalLDL.pivot_eq,columnEnergy_eq,selectedLabel_eq]
  rfl

@[simp] theorem increment_eq (Q : Matrix (Fin d) (Fin d) ℝ) (s : Draws Q) :
    increment Q s=MSManuscriptNumericalSampler.increment Q (drawEquiv Q s) := by
  simp only [increment,MSManuscriptNumericalLDL.lowerColumn_eq,columnEnergy_eq,selectedLabel_eq]
  rfl

/-- All divisions and square roots used for an enumerated sampling branch have
strictly positive scalar operands. Zero LDL pivots were removed by the list. -/
theorem denominators_positive (Q : Matrix (Fin d) (Fin d) ℝ) (hq : 0<realTrace Q) (s : Draws Q) :
    0<2*realTrace Q ∧ 0<Real.sqrt (columnEnergy Q (selectedLabel Q s)) ∧
      0<MSManuscriptNumericalLDL.pivot Q (selectedLabel Q s) := by
  have hp : 0<KSEighthManuscriptLDL.pivot Q (selectedLabel Q s) := by
    rw [selectedLabel_eq]
    exact (drawEquiv Q s).1.property
  refine ⟨by positivity,?_,?_⟩
  · rw [columnEnergy_eq]
    exact Real.sqrt_pos.mpr (MSManuscriptNumericalSampler.columnEnergy_pos Q ⟨selectedLabel Q s,hp⟩)
  · simpa only [MSManuscriptNumericalLDL.pivot_eq] using hp

theorem weight_pos (Q : Matrix (Fin d) (Fin d) ℝ) (hq : 0<realTrace Q) (s : Draws Q) : 0<weight Q s := by
  rw [weight_eq]
  exact MSManuscriptNumericalSampler.weight_pos Q hq _
theorem weight_sum (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosSemidef) (hq : 0<realTrace Q) :
    (∑s : Draws Q,weight Q s)=1 := by
  simp only [weight_eq]
  rw [(drawEquiv Q).sum_comp]
  exact MSManuscriptNumericalSampler.weight_sum Q hQ hq

def sample (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosSemidef) (hq : 0<realTrace Q) :
    MSManuscriptAdaptive.Sampler (EuclideanSpace ℝ (Fin d)) where
  Draws := Draws Q
  fintypeDraws := inferInstance
  weight := weight Q
  value := increment Q
  weight_nonneg := fun s => (weight_pos Q hq s).le
  weight_sum := weight_sum Q hQ hq

theorem mean_zero (Q : Matrix (Fin d) (Fin d) ℝ) : (∑s : Draws Q,weight Q s • increment Q s)=0 := by
  simp only [weight_eq,increment_eq]
  exact ((drawEquiv Q).sum_comp (fun s => MSManuscriptNumericalSampler.weight Q s •
    MSManuscriptNumericalSampler.increment Q s)).trans (MSManuscriptNumericalSampler.mean_zero Q)

theorem covariance (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosSemidef) (hq : 0<realTrace Q) :
    (∑s : Draws Q,weight Q s • realRankOne (WithLp.ofLp (increment Q s)))=Q := by
  simp only [weight_eq,increment_eq]
  exact ((drawEquiv Q).sum_comp (fun s => MSManuscriptNumericalSampler.weight Q s •
    realRankOne (WithLp.ofLp (MSManuscriptNumericalSampler.increment Q s)))).trans
      (MSManuscriptNumericalSampler.covariance Q hQ hq)

theorem increment_norm_sq (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosSemidef) (s : Draws Q) :
    ‖increment Q s‖^2=realTrace Q := by
  rw [increment_eq]
  exact MSManuscriptNumericalSampler.increment_norm_sq Q (realTrace_nonneg hQ) _

theorem increment_mem_range (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosSemidef) (s : Draws Q) :
    increment Q s ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) Q).toLinearMap := by
  rw [increment_eq]
  exact MSManuscriptNumericalSampler.increment_mem_range Q hQ _

theorem count_le (Q : Matrix (Fin d) (Fin d) ℝ) : count Q≤d := by
  exact (List.length_filter_le _ _).trans_eq List.length_finRange

end MatrixSpencer.MSManuscriptNumericalSamplerData
