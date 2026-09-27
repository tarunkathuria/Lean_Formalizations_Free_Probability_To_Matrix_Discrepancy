import MatrixSpencer.DyadicSDPAffineData
import MatrixSpencer.DyadicSDPAffineObjective
import MatrixSpencer.DyadicSDPProgramSize

/-! End-to-end exact, polynomial-size affine real SDP representation of the
rectangular dyadic owner potential. This module links the actual coefficient
arrays, affine objective, attained optimum, and program-size ledger. -/
open Matrix Set
open scoped BigOperators InnerProductSpace MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.DyadicOwnerSDP
open DyadicSDPCoordinates
variable {n ι : Type*} [Fintype n] [LinearOrder n] [Fintype ι] [DecidableEq ι]

def center (a : n) : selfAdjoint (Matrix n n ℂ) := by
  letI : Nonempty n := ⟨a⟩
  exact ⟨maximallyMixed, maximallyMixed_posDef.isHermitian⟩

theorem center_trace (a : n) : realTrace (center a : Matrix n n ℂ)=1 := by
  letI : Nonempty n := ⟨a⟩
  exact maximallyMixed_mem_densitySet.2

/-- A finite family of real symmetric affine matrix inequalities on explicitly
indexed real variables. -/
def feasible (m : ℕ) (a : n) (A : ι → Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) : Set (Space m a) :=
  DyadicSDPAffineData.target m a A hA C hC (center a)

/-- The objective is exactly a constant plus a real coordinate dot product. -/
def objective (m : ℕ) (a : n) (H : Matrix n n ℂ) (θ : ℝ) : Space m a → ℝ :=
  DyadicSDPAffineObjective.objective m a H θ (center a)

theorem feasible_eq (m : ℕ) (a : n) (A : ι → Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) :
    feasible m a A hA C hC = DyadicSDPAffineObjective.target m a (covarianceSource A C) (center a) := by
  ext x
  exact DyadicSDPAffineData.target_iff m a A hA C hC (center a) (center_trace a) x

theorem convex_feasible (m : ℕ) (a : n) (A : ι → Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) : Convex ℝ (feasible m a A hA C hC) :=
  DyadicSDPAffineData.convex_target m a A hA C hC (center a)

/-- The concrete real SDP attains exactly the owner potential. Its hypotheses
are the original Hermitian atoms, PSD covariance, positive Tsallis weight,
and positive dyadic depth; no optimizer or source-rank certificate is assumed. -/
theorem exists_maximizer (m : ℕ) (a : n) (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (hm : 1≤m) {θ : ℝ} (hθ : 0<θ) :
    ∃x : Space m a, x ∈ feasible m a A hA C hC ∧
      objective m a H θ x=dyadicOwnerPotential H A C m θ ∧
      ∀y ∈ feasible m a A hA C hC, objective m a H θ y≤objective m a H θ x := by
  rw [feasible_eq]
  exact DyadicSDPAffineObjective.owner_exists_maximizer m a H A hA hC (center a) (center_trace a) hm hθ

theorem sSup_eq (m : ℕ) (a : n) (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (hm : 1≤m) {θ : ℝ} (hθ : 0<θ) :
    sSup (objective m a H θ '' feasible m a A hA C hC)=dyadicOwnerPotential H A C m θ := by
  rw [feasible_eq]
  exact DyadicSDPAffineObjective.owner_sSup_eq m a H A hA hC (center a) (center_trace a) hm hθ

/-- The count is of the actual finite coefficient arrays and variable space
used in `feasible`, rather than a separate abstract model. -/
theorem actual_size_bounds (m : ℕ) (a : n) :
    dimension m a=DyadicSDPProgramSize.variableCount m (Fintype.card n) ∧
    Fintype.card (DyadicSDPAffineData.Constraint m)=DyadicSDPProgramSize.constraintCount m ∧
    DyadicSDPAffineData.matrixSize n=DyadicSDPProgramSize.blockOrder (Fintype.card n) ∧
    Fintype.card (DyadicSDPAffineData.Constraint m) * (dimension m a+1) *
      (DyadicSDPAffineData.matrixSize n)^2 =
        16*(2*m+1)*(m+3)*(Fintype.card n)^4 := by
  have hv := dimension_eq m a
  have hc := DyadicSDPAffineData.constraint_count m
  have hb : DyadicSDPAffineData.matrixSize n=4*Fintype.card n := DyadicSDPAffineData.matrixSize_eq
  refine ⟨hv,hc,hb,?_⟩
  rw [hv,hc,hb]
  letI : Nonempty n:=⟨a⟩
  exact DyadicSDPProgramSize.denseCoefficients_eq m Fintype.card_pos


theorem rectangular_size_bounds {N D : ℕ} (hN : 1≤N) (hD : 1≤D) (a : Fin (2*D)) :
    let m := RectangularTunedParameters.depth N D
    dimension m a ≤ 4*(2*D+5)*D^2 ∧
    Fintype.card (DyadicSDPAffineData.Constraint m) ≤ 4*D+5 ∧
    DyadicSDPAffineData.matrixSize (Fin (2*D))=8*D ∧
    Fintype.card (DyadicSDPAffineData.Constraint m) * (dimension m a+1) *
      (DyadicSDPAffineData.matrixSize (Fin (2*D)))^2 ≤ 256*(4*D+5)*(2*D+5)*D^4 := by
  dsimp only
  have h:=actual_size_bounds (RectangularTunedParameters.depth N D) a
  simp only [Fintype.card_fin] at h
  rw [h.1,h.2.1,h.2.2.1]
  exact DyadicSDPProgramSize.rectangular_sizes hN hD


theorem rectangular_exists_maximizer {N D : ℕ} (hN : 1≤N) (hND : N≤D)
    (a : Fin (2*D)) (H : Matrix (Fin (2*D)) (Fin (2*D)) ℂ)
    (A : Fin N → Matrix (Fin (2*D)) (Fin (2*D)) ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : Matrix (Fin N) (Fin N) ℝ) (hC : C.PosSemidef) :
    let m:=RectangularTunedParameters.depth N D
    let θ:=RectangularTunedParameters.weight N D
    ∃x : Space m a, x ∈ feasible m a A hA C hC ∧
      objective m a H θ x=dyadicOwnerPotential H A C m θ ∧
      ∀y ∈ feasible m a A hA C hC, objective m a H θ y≤objective m a H θ x :=
  exists_maximizer _ a H A hA C hC (RectangularTunedParameters.depth_positive N D)
    (RectangularTunedParameters.weight_positive hN hND)

end MatrixSpencer.DyadicOwnerSDP
