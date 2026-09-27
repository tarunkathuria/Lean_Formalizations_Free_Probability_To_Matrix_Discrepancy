import MatrixSpencer.KSConvexValueOracle

/-! Mathematical value specifications for the existence proof.
The value is a real supremum. Its correctness is proved whenever the
supplied affine program has an attained maximum; no runtime is asserted. -/
open Set
open scoped InnerProductSpace
noncomputable section
namespace ExistenceKS.ExactValue
open MatrixSpencer
open MatrixSpencer.KSFullManuscriptAffinePSD

def value {ℓ k : ℕ} (D : Data ℓ k) (c : Space ℓ) (offset : ℝ) : ℝ :=
  sSup ((fun x => offset + ⟪c,x⟫_ℝ) '' target D)

theorem value_eq_of_maximum {ℓ k : ℕ}
    (D : Data ℓ k) (c : Space ℓ) (offset : ℝ)
    (x : Space ℓ) (hx : x ∈ target D)
    (hmax : ∀ y ∈ target D, offset + ⟪c,y⟫_ℝ ≤ offset + ⟪c,x⟫_ℝ) :
    value D c offset = offset + ⟪c,x⟫_ℝ := by
  have hgreatest : IsGreatest ((fun y => offset + ⟪c,y⟫_ℝ) '' target D)
      (offset + ⟪c,x⟫_ℝ) := by
    refine ⟨⟨x,hx,rfl⟩,?_⟩
    rintro z ⟨y,hy,rfl⟩
    exact hmax y hy
  exact hgreatest.csSup_eq

def specification : KSConvexValueOracle.Solver where
  report D c offset _ := value D c offset
  accuracy D c offset ν hν x hx hmax := by
    rw [value_eq_of_maximum D c offset x hx hmax, sub_self, abs_zero]
    exact hν.le

theorem specification_exists : Nonempty KSConvexValueOracle.Solver :=
  ⟨specification⟩

/-- The exact specification evaluates the actual owner potential.
Attainment and equality with the affine SDP are supplied by the proved
program materialization theorem. The accuracy argument is irrelevant here. -/
theorem ownerReport_exact {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (hd : 0 < d)
    {θ : ℝ} (hθ : 0 < θ) (ν : ℝ) :
    KSConvexValueOracle.ownerReport specification a H A hA C hC hd θ ν =
      ownerPotential H A C θ := by
  obtain ⟨x,hx,hval,hmax⟩ := OwnerSDPProgramSize.exists_maximizer a H A hA C hC
    (KSFullManuscriptCenterData.densityCenter hd) 0
    (KSFullManuscriptStrictFeasible.density_trace hd) hθ
  change value (KSConvexValueOracle.ownerData a A hA C hC hd)
    (KSFullManuscriptAffineObjective.coefficient a H θ)
    (KSFullManuscriptAffineObjective.offset H θ
      (KSFullManuscriptCenterData.densityCenter hd) 0) = ownerPotential H A C θ
  exact (value_eq_of_maximum _ _ _ x hx hmax).trans hval


end ExistenceKS.ExactValue
