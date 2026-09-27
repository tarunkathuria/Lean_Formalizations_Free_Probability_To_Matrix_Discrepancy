import MatrixSpencer.RealRAMKSNormReport
import Mathlib.LinearAlgebra.Matrix.Spectrum

/-! Exact real symmetric EVD as an additional unit-cost primitive. The
spectral theorem proves its contract, not a scalar-RAM implementation.
Inherited scans and orthogonal-matrix lemmas run no Jacobi rotations.
The fixed spectral basis specifies deterministic choices at multiplicities. -/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace SeamlessKS.ExactEVD
open MatrixSpencer MatrixSpencer.KSJacobiRayleigh MatrixSpencer.KSRayleighAccuracy
open MatrixSpencer.RealRAM
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
attribute [local instance] Classical.propDecidable
variable {m : ℕ}

def basis (A : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  if h : A.IsSymm then ((show A.IsHermitian from h).eigenvectorUnitary : Matrix _ _ ℝ) else 1

def diagonal (A : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  (basis A)ᵀ * A * basis A

theorem basis_left (A : Matrix (Fin m) (Fin m) ℝ) : (basis A)ᵀ * basis A = 1 := by
  unfold basis
  split_ifs with h
  · exact unitary.coe_star_mul_self (show A.IsHermitian from h).eigenvectorUnitary
  · simp

theorem basis_right (A : Matrix (Fin m) (Fin m) ℝ) : basis A * (basis A)ᵀ = 1 := by
  unfold basis
  split_ifs with h
  · exact unitary.coe_mul_star_self (show A.IsHermitian from h).eigenvectorUnitary
  · simp

theorem diagonal_exact (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsSymm) :
    diagonalPart (diagonal A) = diagonal A := by
  have he := (show A.IsHermitian from hA).star_mul_self_mul_eq_diagonal
  have hd : diagonal A = Matrix.diagonal (show A.IsHermitian from hA).eigenvalues := by
    simpa [diagonal,basis,hA,Function.comp_def] using he
  rw [hd]
  simp [diagonalPart]

/-- The extended machine's EVD rule; not a scalar arithmetic instruction. -/
inductive Executes (A : Matrix (Fin m) (Fin m) ℝ) :
    (Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin m) ℝ) → ℕ → Prop
  | evd (hA : A.IsSymm) : Executes A (diagonal A,basis A) 1

def compute (A : Matrix (Fin m) (Fin m) ℝ) : Counted
    (Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin m) ℝ) :=
  ⟨(diagonal A,basis A),1⟩

theorem compute_execution (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsSymm) :
    Executes A (compute A).value (compute A).cost := .evd hA

def output (A : Matrix (Fin m) (Fin m) ℝ) (hm : 0<m) : EuclideanSpace ℝ (Fin m) :=
  basisColumn (basis A) (minimumDiagonal (diagonal A) hm)

theorem output_norm (A : Matrix (Fin m) (Fin m) ℝ) (hm : 0<m) : ‖output A hm‖=1 :=
  basisColumn_norm _ (basis_left A) _

theorem output_minimal (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsSymm) (hm : 0<m)
    (v : EuclideanSpace ℝ (Fin m)) (hv : ‖v‖=1) :
    realRayleigh A (output A hm) ≤ realRayleigh A v := by
  let w := Matrix.toEuclideanCLM (𝕜:=ℝ) (basis A)ᵀ v
  have hw : ‖w‖=1 := by
    simpa [w,hv] using orthogonal_preserves_norm (basis A)ᵀ
      (by simpa using basis_right A) v
  have he : Matrix.toEuclideanCLM (𝕜:=ℝ) (basis A) w=v := by
    change (Matrix.toEuclideanCLM (𝕜:=ℝ) (basis A) *
      Matrix.toEuclideanCLM (𝕜:=ℝ) (basis A)ᵀ) v=v
    rw [←map_mul,basis_right,map_one,ContinuousLinearMap.one_apply]
  have hl := diagonalRayleigh_lower (diagonal A) (minimumDiagonal (diagonal A) hm)
    (minimumDiagonal_le _ hm) w hw
  rw [diagonal_exact A hA] at hl
  rw [output,basisColumn_Rayleigh]
  simpa only [diagonal,realRayleigh_conjugation,he] using hl

theorem output_accuracy (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsSymm) (hm : 0<m) :
    realRayleigh A (output A hm) ≤ leastRayleigh A := by
  apply le_csInf (show (unitRayleighValues A).Nonempty from ⟨_,output A hm,output_norm A hm,rfl⟩)
  rintro t ⟨v,hv,rfl⟩
  exact output_minimal A hA hm v hv

def direction (A : Matrix (Fin m) (Fin m) ℝ) (hm : 0<m) : Counted (EuclideanSpace ℝ (Fin m)) :=
  let e := compute A
  let i := JacobiRayleigh.minimum e.value.1 hm
  ⟨basisColumn e.value.2 i.value,e.cost+i.cost+3*m+3⟩

theorem direction_value (A : Matrix (Fin m) (Fin m) ℝ) (hm : 0<m) :
    (direction A hm).value=output A hm := by
  simp only [direction,compute,JacobiRayleigh.minimum_value,output]

theorem direction_cost (A : Matrix (Fin m) (Fin m) ℝ) (hm : 0<m) :
    (direction A hm).cost≤11*m+7 := by
  have h := JacobiRayleigh.minimum_cost (diagonal A) hm
  dsimp only [direction,compute]
  omega

def normReport (A : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  KSJacobiNorm.maxAbsDiagonal (diagonal A)

theorem normReport_exact (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsSymm) :
    normReport A=‖A‖ := by
  have hn := KSJacobiNorm.orthogonal_conjugation_norm A (basis A) (basis_left A) (basis_right A)
  have hl := KSJacobiNorm.maxAbsDiagonal_le_norm (diagonal A)
  have hu := KSJacobiNorm.diagonalPart_norm_le (diagonal A)
  rw [diagonal_exact A hA] at hu
  change ‖diagonal A‖=‖A‖ at hn
  exact (le_antisymm hl hu).trans hn

def norm (A : Matrix (Fin m) (Fin m) ℝ) : Counted ℝ :=
  let e := compute A
  let q := KSNormReport.maximum e.value.1
  ⟨q.value,e.cost+q.cost+1⟩

theorem norm_value (A : Matrix (Fin m) (Fin m) ℝ) : (norm A).value=normReport A := by
  simp only [norm,compute,KSNormReport.maximum_value,normReport]

theorem norm_cost (A : Matrix (Fin m) (Fin m) ℝ) : (norm A).cost≤14*m+9 := by
  have h := KSNormReport.maximum_cost (diagonal A)
  dsimp only [norm,compute]
  omega
end SeamlessKS.ExactEVD
