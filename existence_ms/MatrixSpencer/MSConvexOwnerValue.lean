import MatrixSpencer.KSPolynomialConvexSolver

/-! The square-walk value-query interface, instantiated by the permitted
convex solver on the actual direct owner SDP. Invalid inputs receive zero;
all queries in the walk are proved Hermitian/PSD, so the counted evaluator
uses the direct SDP expression without executing those proof-only guards. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSConvexOwnerValue

class Oracle where
  report : {ι : Type} → [Fintype ι] → [DecidableEq ι] → {d : ℕ} →
    Matrix (Fin d) (Fin d) ℂ → (ι → Matrix (Fin d) (Fin d) ℂ) →
      Matrix ι ι ℝ → ℝ → (0<d) → ℝ → ℝ
  accuracy : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ} [Nonempty (Fin d)]
    (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {θ ν : ℝ}
    (hθ : 0<θ) (hν : 0<ν) (hd : 0<d),
      |report H A C θ hd ν-ownerPotential H A C θ|≤ν

variable {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}

def report [Oracle] (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (C : Matrix ι ι ℝ) (θ : ℝ) (hd : 0<d) (ν : ℝ) : ℝ :=
  Oracle.report H A C θ hd ν

theorem report_accuracy [Oracle] [Nonempty (Fin d)]
    (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {θ ν : ℝ}
    (hθ : 0<θ) (hν : 0<ν) (hd : 0<d) :
    |report H A C θ hd ν-ownerPotential H A C θ|≤ν :=
  Oracle.accuracy H hH A hA hC hθ hν hd

def Oracle.ofSolver (O : KSConvexValueOracle.Solver) : Oracle where
  report H A C θ hd ν := by
    classical
    exact if hA : ∀i,(A i).IsHermitian then
      if hC : C.PosSemidef then
        KSConvexValueOracle.ownerReport O ⟨0,hd⟩ H A hA C hC hd θ ν
      else 0
    else 0
  accuracy := by
    intro ι _ _ d _ H _ A hA C hC θ ν hθ hν hd
    rw [dif_pos hA,dif_pos hC]
    exact KSConvexValueOracle.ownerReport_accuracy O ⟨0,hd⟩ H A hA _ hC hd hθ hν

theorem report_ofSolver (O : KSConvexValueOracle.Solver)
    (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀i,(A i).IsHermitian) (C : Matrix ι ι ℝ) (hC : C.PosSemidef)
    (θ : ℝ) (hd : 0<d) (ν : ℝ) :
    @report ι _ _ d (Oracle.ofSolver O) H A C θ hd ν =
      KSConvexValueOracle.ownerReport O ⟨0,hd⟩ H A hA C hC hd θ ν := by
  simp only [report,Oracle.ofSolver,dif_pos hA,dif_pos hC]

end MatrixSpencer.MSConvexOwnerValue
