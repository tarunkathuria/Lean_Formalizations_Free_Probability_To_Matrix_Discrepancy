import MatrixSpencer.RectangularRidgeSquareJetIdentities

/-!
# Actual dyadic-root line jets

The curve is the actual positive dyadic root of an affine Hermitian line.
All jet identities derive from its genuine square equation near a positive
center. Scalar parameter bounds are proved separately below.
-/

open Matrix Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.RectangularRidgeActualRootJets
open RectangularRidgeRootJetBounds RectangularRidgeSquareJetIdentities
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance ridgeActualRootJetsCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance ridgeActualRootJetsRealSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

abbrev Herm := selfAdjoint (Matrix n n ℂ)

def line (S X : Herm (n := n)) (t : ℝ) : Herm (n := n) := S + t • X

def path (m : ℕ) (S X : Herm (n := n)) (t : ℝ) : Herm (n := n) :=
  hermitianDyadicRoot m (line S X t)

def matrixPath (m : ℕ) (S X : Herm (n := n)) (t : ℝ) : Matrix n n ℂ :=
  path m S X t

def jet (r m : ℕ) (S X : Herm (n := n)) : Herm (n := n) :=
  iteratedDeriv r (path m S X) 0

lemma contDiff_line (S X : Herm (n := n)) : ContDiff ℝ ∞ (line S X) := by
  unfold line
  fun_prop

lemma contDiffAt_path (m : ℕ) (S X : Herm (n := n))
    (hS : (S : Matrix n n ℂ).PosDef) : ContDiffAt ℝ ∞ (path m S X) 0 := by
  have hr : ContDiffAt ℝ ∞ (hermitianDyadicRoot m) (line S X 0) := by
    simpa [line] using contDiffAt_hermitianDyadicRoot m S hS
  exact hr.comp 0 (contDiff_line S X).contDiffAt

lemma contDiffAt_matrixPath (m : ℕ) (S X : Herm (n := n))
    (hS : (S : Matrix n n ℂ).PosDef) : ContDiffAt ℝ ∞ (matrixPath m S X) 0 :=
  (hermitianInclusion (n := n)).contDiff.contDiffAt.comp 0 (contDiffAt_path m S X hS)

lemma jet_coe (r m : ℕ) (S X : Herm (n := n)) (hS : (S : Matrix n n ℂ).PosDef) :
    (jet r m S X : Matrix n n ℂ) = iteratedDeriv r (matrixPath m S X) 0 := by
  symm
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change iteratedFDeriv ℝ r ((hermitianInclusion (n := n)) ∘ path m S X) 0 (fun _ => 1) = _
  rw [(hermitianInclusion (n := n)).iteratedFDeriv_comp_left (contDiffAt_path m S X hS)
    (WithTop.coe_le_coe.mpr (show (r : ℕ∞) ≤ ⊤ from le_top))]
  rfl

lemma path_zero (m : ℕ) (S X : Herm (n := n)) : path m S X 0 = hermitianDyadicRoot m S := by
  simp [path, line]

lemma matrixPath_zero (m : ℕ) (S X : Herm (n := n)) :
    matrixPath m S X 0 = dyadicRoot m (S : Matrix n n ℂ) := by
  simp only [matrixPath, path_zero, hermitianDyadicRoot_coe]

lemma square_eventually (m : ℕ) (S X : Herm (n := n))
    (hS : (S : Matrix n n ℂ).PosDef) :
    (fun t => matrixPath (m + 1) S X t * matrixPath (m + 1) S X t) =ᶠ[𝓝 0]
      matrixPath m S X := by
  have hline : Tendsto (line S X) (𝓝 0) (𝓝 S) := by
    simpa only [line, zero_smul, add_zero] using ((contDiff_line S X).continuous.continuousAt (x := 0)).tendsto
  filter_upwards [hline.eventually (eventually_posDef_of_posDef S hS)] with t ht
  simp only [matrixPath, path, hermitianDyadicRoot_coe]
  change dyadicRoot (m + 1) (line S X t : Matrix n n ℂ) *
    dyadicRoot (m + 1) (line S X t : Matrix n n ℂ) = dyadicRoot m (line S X t : Matrix n n ℂ)
  exact (by simpa only [pow_two] using dyadicRoot_succ_square m ht.posSemidef)

lemma square_jet_two (m : ℕ) (S X : Herm (n := n))
    (hS : (S : Matrix n n ℂ).PosDef) :
    (jet 2 m S X : Matrix n n ℂ) =
      (jet 2 (m + 1) S X : Matrix n n ℂ) * dyadicRoot (m + 1) (S : Matrix n n ℂ) +
        (2 : ℝ) • ((jet 1 (m + 1) S X : Matrix n n ℂ) * (jet 1 (m + 1) S X : Matrix n n ℂ)) +
        dyadicRoot (m + 1) (S : Matrix n n ℂ) * (jet 2 (m + 1) S X : Matrix n n ℂ) := by
  have he := (square_eventually m S X hS).iteratedDeriv_eq 2
  rw [square_second ((contDiffAt_matrixPath (m + 1) S X hS).of_le (WithTop.coe_le_coe.mpr (show (4 : ℕ∞) ≤ ⊤ from le_top)))] at he
  simpa only [← jet_coe _ _ S X hS, matrixPath_zero] using he.symm

lemma square_jet_three (m : ℕ) (S X : Herm (n := n))
    (hS : (S : Matrix n n ℂ).PosDef) :
    (jet 3 m S X : Matrix n n ℂ) =
      (jet 3 (m + 1) S X : Matrix n n ℂ) * dyadicRoot (m + 1) (S : Matrix n n ℂ) +
        (3 : ℝ) • ((jet 2 (m + 1) S X : Matrix n n ℂ) * (jet 1 (m + 1) S X : Matrix n n ℂ)) +
        (3 : ℝ) • ((jet 1 (m + 1) S X : Matrix n n ℂ) * (jet 2 (m + 1) S X : Matrix n n ℂ)) +
        dyadicRoot (m + 1) (S : Matrix n n ℂ) * (jet 3 (m + 1) S X : Matrix n n ℂ) := by
  have he := (square_eventually m S X hS).iteratedDeriv_eq 3
  rw [square_third ((contDiffAt_matrixPath (m + 1) S X hS).of_le (WithTop.coe_le_coe.mpr (show (4 : ℕ∞) ≤ ⊤ from le_top)))] at he
  simpa only [← jet_coe _ _ S X hS, matrixPath_zero] using he.symm

lemma square_jet_four (m : ℕ) (S X : Herm (n := n))
    (hS : (S : Matrix n n ℂ).PosDef) :
    (jet 4 m S X : Matrix n n ℂ) =
      (jet 4 (m + 1) S X : Matrix n n ℂ) * dyadicRoot (m + 1) (S : Matrix n n ℂ) +
        (4 : ℝ) • ((jet 3 (m + 1) S X : Matrix n n ℂ) * (jet 1 (m + 1) S X : Matrix n n ℂ)) +
        (6 : ℝ) • ((jet 2 (m + 1) S X : Matrix n n ℂ) * (jet 2 (m + 1) S X : Matrix n n ℂ)) +
        (4 : ℝ) • ((jet 1 (m + 1) S X : Matrix n n ℂ) * (jet 3 (m + 1) S X : Matrix n n ℂ)) +
        dyadicRoot (m + 1) (S : Matrix n n ℂ) * (jet 4 (m + 1) S X : Matrix n n ℂ) := by
  have he := (square_eventually m S X hS).iteratedDeriv_eq 4
  rw [square_fourth ((contDiffAt_matrixPath (m + 1) S X hS).of_le (WithTop.coe_le_coe.mpr (show (4 : ℕ∞) ≤ ⊤ from le_top)))] at he
  simpa only [← jet_coe _ _ S X hS, matrixPath_zero] using he.symm

lemma jet_one_eq (m : ℕ) (S X : Herm (n := n))
    (hS : (S : Matrix n n ℂ).PosDef) :
    jet 1 m S X = fderiv ℝ (hermitianDyadicRoot m) S X := by
  have hl : HasDerivAt (line S X) X 0 := by
    simpa [line] using (hasDerivAt_const (0 : ℝ) S).add ((hasDerivAt_id (0 : ℝ)).smul_const X)
  have hr := (hasStrictFDerivAt_hermitianDyadicRoot m S hS).hasFDerivAt
  have hr' : HasFDerivAt (hermitianDyadicRoot m) (fderiv ℝ (hermitianDyadicRoot m) S)
      (line S X 0) := by simpa [line, hr.fderiv] using hr
  simpa only [jet, iteratedDeriv_one, path, Function.comp_def] using
    (hr'.comp_hasDerivAt 0 hl).deriv

lemma jet_one_norm_le (m : ℕ) (S X : Herm (n := n))
    (hS : (S : Matrix n n ℂ).PosDef) {μ : ℝ} (hμ : 0 < μ)
    (hfloor : μ • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ)) (hX : ‖X‖ ≤ 1) :
    ‖jet 1 m S X‖ ≤ μ ^ (exponent m - 1) := by
  rw [jet_one_eq m S X hS]
  have hd := derivative_norm_le m S hS hμ hfloor
  rw [← fderiv_hermitianDyadicRoot m S hS] at hd
  exact ((fderiv ℝ (hermitianDyadicRoot m) S).le_opNorm X).trans
    ((mul_le_mul hd hX (norm_nonneg _) (Real.rpow_nonneg hμ.le _)).trans_eq (mul_one _))

end MatrixSpencer.RectangularRidgeActualRootJets
