import MatrixSpencer.RectangularRidgeConvexValue
import MatrixSpencer.RectangularRidgeTangentParameters
import MatrixSpencer.RectangularRidgeCertificate

/-! The saved supporting tangent and anchored certificate from accurate
values of explicit mixed SDPs. The saved density occurs only in the proof;
the report evaluates two perturbed zero-source programs and scalar arithmetic. -/

open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.RectangularRidgeSolverCertificate
open RectangularRidgeTangentValues RectangularRidgeCertificate
variable {d : ℕ} [Nonempty (Fin d)]
local instance ridgeSolverCertificateCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
local instance ridgeSolverCertificateSpace : NormedSpace ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) := inferInstance
set_option maxHeartbeats 400000

def emptyFamily : Empty → Matrix (Fin d) (Fin d) ℂ := fun _ => 0

theorem emptyFamily_hermitian (i : Empty) : (emptyFamily (d:=d) i).IsHermitian := Matrix.isHermitian_zero

theorem emptyKraus : covarianceKraus (emptyFamily (d:=d)) (0 : Matrix Empty Empty ℝ)=emptyFamily := by
  funext i
  exact Empty.elim i

def baseReport (O : RectangularRidgeConvexValue.Solver) (m : ℕ) (hm : 1≤m) (a : Fin d)
    (H : Matrix (Fin d) (Fin d) ℂ) (θ κ ν : ℝ) : ℝ :=
  RectangularRidgeConvexValue.report O m hm a H emptyFamily emptyFamily_hermitian
    0 Matrix.PosSemidef.zero θ κ ν

theorem baseReport_accuracy (O : RectangularRidgeConvexValue.Solver)
    (m : ℕ) (hm : 1≤m) (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    {θ κ ν : ℝ} (hθ : 0<θ) (hκ : 0≤κ) (hν : 0<ν) :
    |baseReport O m hm a H θ κ ν-
      RectangularRidgePotential.potential H emptyFamily m θ κ|≤ν := by
  have hh := RectangularRidgeConvexValue.report_accuracy O m hm a H emptyFamily
    emptyFamily_hermitian 0 Matrix.PosSemidef.zero hθ hκ hν
  rwa [emptyKraus] at hh

def tangentReport (O : RectangularRidgeConvexValue.Solver) (m : ℕ) (hm : 1≤m) (a : Fin d)
    (H X : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) (θ κ R ε : ℝ) : ℝ :=
  RectangularRidgeTangentValues.report
    (fun K => baseReport O m hm a K θ κ (precision κ R ε)) H X κ R ε

/-- The actual two-query report of Tr(Sstar X), with no supplied curvature,
Taylor, or optimizer approximation hypothesis. -/
theorem tangentReport_accuracy (O : RectangularRidgeConvexValue.Solver)
    (m : ℕ) (hm : 1≤m) (a : Fin d)
    (H X : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    {θ κ R ε : ℝ} (hθ : 0<θ) (hκ : 0<κ) (hR : 0≤R) (hε : 0<ε)
    (hX : Real.sqrt (realTrace ((X : Matrix (Fin d) (Fin d) ℂ)*(X : Matrix (Fin d) (Fin d) ℂ)))≤R) :
    |tangentReport O m hm a H X θ κ R ε-
      realTrace (density (H : Matrix (Fin d) (Fin d) ℂ) m θ κ*(X : Matrix (Fin d) (Fin d) ℂ))|≤ε/3 := by
  apply RectangularRidgeTangentValues.report_accuracy H X emptyFamily m hm hθ hκ hR hε hX
  · exact baseReport_accuracy O m hm a _ hθ hκ.le (precision_pos hκ hε)
  · exact baseReport_accuracy O m hm a _ hθ hκ.le (precision_pos hκ hε)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def certificateReport (O : RectangularRidgeConvexValue.Solver) (m : ℕ) (hm : 1≤m) (a : Fin d)
    (Hstar H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (θ κ R ε : ℝ) : ℝ :=
  RectangularRidgeConvexValue.report O m hm a H A hA C hC θ κ (ε/6)-
    baseReport O m hm a Hstar θ κ (ε/6)-
      tangentReport O m hm a Hstar (H-Hstar) θ κ R ε

/-- Four SDP calls certify the nonnegative anchored potential, with the
actual saved supporting density from the mixed objective. -/
theorem certificateReport_accuracy (O : RectangularRidgeConvexValue.Solver)
    (m : ℕ) (hm : 1≤m) (a : Fin d)
    (Hstar H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef)
    {θ κ R ε : ℝ} (hθ : 0<θ) (hκ : 0<κ) (hR : 0≤R) (hε : 0<ε)
    (hX : Real.sqrt (realTrace (((H-Hstar : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) :
      Matrix (Fin d) (Fin d) ℂ)*((H-Hstar : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) :
      Matrix (Fin d) (Fin d) ℂ)))≤R) :
    |certificateReport O m hm a Hstar H A hA C hC θ κ R ε-
      certificate (Hstar : Matrix (Fin d) (Fin d) ℂ) A m θ κ H C|≤ε := by
  have hν : 0<ε/6 := by positivity
  have ho := RectangularRidgeConvexValue.report_accuracy O m hm a H A hA C hC hθ hκ.le hν
  have hb := baseReport_accuracy O m hm a Hstar hθ hκ.le hν
  have ht := tangentReport_accuracy O m hm a Hstar (H-Hstar) hθ hκ hR hε hX
  have he := empty_potential_eq_base (Hstar : Matrix (Fin d) (Fin d) ℂ) m θ κ
  change RectangularRidgePotential.potential (Hstar : Matrix (Fin d) (Fin d) ℂ)
    emptyFamily m θ κ = _ at he
  rw [he] at hb
  rw [←RectangularRidgeCovarianceCalculus.ownerPotential_eq_densityPotential m
    (H : Matrix (Fin d) (Fin d) ℂ) A hA hC] at ho
  unfold certificateReport certificate tangent
  change |(_-_)-_|≤ε
  change |baseReport O m hm a Hstar θ κ (ε/6)-
    regularizedBasePotential (Hstar : Matrix (Fin d) (Fin d) ℂ)
      (RectangularRidgeCovarianceCalculus.regularizer m θ κ)|≤ε/6 at hb
  change |tangentReport O m hm a Hstar (H-Hstar) θ κ R ε-
    realTrace (density (Hstar : Matrix (Fin d) (Fin d) ℂ) m θ κ*
      ((H : Matrix (Fin d) (Fin d) ℂ)-(Hstar : Matrix (Fin d) (Fin d) ℂ)))|≤ε/3 at ht
  change |RectangularRidgeConvexValue.report O m hm a H A hA C hC θ κ (ε/6)-
    regularizedOwnerPotential (H : Matrix (Fin d) (Fin d) ℂ) A C
      (RectangularRidgeCovarianceCalculus.regularizer m θ κ)|≤ε/6 at ho
  apply abs_le.mpr
  constructor <;> linarith [(abs_le.mp ho).1,(abs_le.mp ho).2,
    (abs_le.mp hb).1,(abs_le.mp hb).2,(abs_le.mp ht).1,(abs_le.mp ht).2]

end MatrixSpencer.RectangularRidgeSolverCertificate
