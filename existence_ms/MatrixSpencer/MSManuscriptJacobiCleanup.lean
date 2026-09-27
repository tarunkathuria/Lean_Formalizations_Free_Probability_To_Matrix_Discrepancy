import MatrixSpencer.MSManuscriptCleanupFloor
import MatrixSpencer.MSManuscriptCleanupCount


open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.MSManuscriptJacobiCleanup
open MSManuscriptCleanupParameters MSManuscriptSchurCleanup MSManuscriptCleanupFloor
open KSJacobiRayleigh KSJacobiIteration
variable {d : ℕ}

private theorem real_conjTranspose (U : Matrix (Fin d) (Fin d) ℝ) : U.conjTranspose = Uᵀ := by
  ext i j
  simp

def rotated (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) := finalMatrix G (tolerance d δ)
def basis (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) := finalBasis G (tolerance d δ)
def output (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) :=
  basis G δ * runScan (rotated G δ) δ d * (basis G δ)ᵀ
abbrev Retained (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) := High (rotated G δ) δ
def retainedMatrix (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) := reduced (rotated G δ) δ

theorem basis_transpose_mul (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) :
    (basis G δ)ᵀ * basis G δ = 1 := accumulatedBasis_transpose_mul G _
theorem basis_mul_transpose (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) :
    basis G δ * (basis G δ)ᵀ = 1 := accumulatedBasis_mul_transpose G _
theorem rotated_eq (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) :
    rotated G δ = (basis G δ)ᵀ * G * basis G δ := run_eq_conjugation G _

theorem rotated_posSemidef (G : Matrix (Fin d) (Fin d) ℝ) (hG : G.PosSemidef) (δ : ℝ) :
    (rotated G δ).PosSemidef := by
  rw [rotated_eq]
  simpa only [real_conjTranspose] using hG.conjTranspose_mul_mul_same (basis G δ)

theorem rotated_floor (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ)
    (hf : δ • (1 : Matrix (Fin d) (Fin d) ℝ) ≤ G) : δ • (1 : Matrix (Fin d) (Fin d) ℝ) ≤ rotated G δ := by
  have h := (Matrix.le_iff.mp hf).conjTranspose_mul_mul_same (basis G δ)
  apply Matrix.le_iff.mpr
  simpa only [real_conjTranspose,Matrix.mul_sub,Matrix.sub_mul,
    Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,basis_transpose_mul,←rotated_eq] using h

theorem rotated_diagonal_floor (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ)
    (hf : δ • (1 : Matrix (Fin d) (Fin d) ℝ) ≤ G) (a : Fin d) : δ ≤ rotated G δ a a := by
  have h := KSEighthManuscriptLDL.diagonal_nonneg (Matrix.le_iff.mp (rotated_floor G δ hf)) a
  simpa using h

theorem offDiagonal_entry_sq_le (G : Matrix (Fin d) (Fin d) ℝ) (a b : Fin d) (hab : a≠b) :
    (G a b)^2 ≤ KSJacobiStep.offDiagonalEnergy G := by
  have hi := Finset.single_le_sum (s := Finset.univ)
    (f := fun j : Fin d => if a=j then (0:ℝ) else (G a j)^2)
    (fun j _ => by dsimp; split_ifs <;> positivity) (Finset.mem_univ b)
  have hj := Finset.single_le_sum (s := Finset.univ)
    (f := fun i : Fin d => ∑ j, if i=j then (0:ℝ) else (G i j)^2)
    (fun i _ => Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)) (Finset.mem_univ a)
  simpa only [if_neg hab] using hi.trans hj

theorem rotated_offDiagonal (G : Matrix (Fin d) (Fin d) ℝ) (hG : G.PosSemidef)
    {δ : ℝ} (hδ : 0 < δ) (a b : Fin d) (hab : a≠b) :
    |rotated G δ a b| ≤ tolerance d δ := by
  have hs : G.IsSymm := by
    simpa only [Matrix.IsHermitian, real_conjTranspose] using hG.isHermitian
  have he := run_energy_accuracy G hs (tolerance_pos d hδ)
  have hent := offDiagonal_entry_sq_le (rotated G δ) a b hab
  have hsq : (rotated G δ a b)^2 ≤ (tolerance d δ)^2 := hent.trans he
  exact (sq_le_sq₀ (abs_nonneg _) (tolerance_pos d hδ).le).mp (by simpa only [sq_abs] using hsq)

theorem output_posSemidef (G : Matrix (Fin d) (Fin d) ℝ) (hG : G.PosSemidef) (δ : ℝ) :
    (output G δ).PosSemidef := by
  simpa only [output,real_conjTranspose] using
    (runScan_posSemidef _ (rotated_posSemidef G hG δ) δ d).mul_mul_conjTranspose_same (basis G δ)

theorem output_le (G : Matrix (Fin d) (Fin d) ℝ) (hG : G.PosSemidef) (δ : ℝ) :
    output G δ ≤ G := by
  have h := (Matrix.le_iff.mp (runScan_le _ (rotated_posSemidef G hG δ) δ d)).mul_mul_conjTranspose_same (basis G δ)
  apply Matrix.le_iff.mpr
  have he : basis G δ * rotated G δ * (basis G δ)ᵀ = G := by
    rw [rotated_eq]
    calc
      _ = (basis G δ * (basis G δ)ᵀ) * G * (basis G δ * (basis G δ)ᵀ) := by noncomm_ring
      _ = G := by rw [basis_mul_transpose,Matrix.one_mul,Matrix.mul_one]
  simpa only [real_conjTranspose,Matrix.mul_sub,Matrix.sub_mul,he,output] using h

theorem retained_floor (G : Matrix (Fin d) (Fin d) ℝ) (hG : G.PosSemidef)
    {δ : ℝ} (hδ : 0 < δ) (hf : δ • (1 : Matrix (Fin d) (Fin d) ℝ) ≤ G) :
    (2*δ) • (1 : Matrix (Retained G δ) (Retained G δ) ℝ) ≤ retainedMatrix G δ :=
  reduced_floor _ (rotated_posSemidef G hG δ) hδ (rotated_diagonal_floor G δ hf)
    (rotated_offDiagonal G hG hδ)

theorem trace_conjugation (G U : Matrix (Fin d) (Fin d) ℝ) (hU : Uᵀ*U=1) :
    realTrace (U*G*Uᵀ)=realTrace G := by
  rw [realTrace_mul_cycle,hU,Matrix.one_mul]

theorem output_trace_loss (G : Matrix (Fin d) (Fin d) ℝ) (hG : G.PosSemidef)
    {δ : ℝ} (hδ : 0 < δ) (hf : δ • (1 : Matrix (Fin d) (Fin d) ℝ) ≤ G) :
    realTrace G-realTrace (output G δ) ≤ 4*δ*(d-Fintype.card (Retained G δ):ℕ) := by
  have hb := runScan_bounds _ (rotated_posSemidef G hG δ) hδ (rotated_diagonal_floor G δ hf)
    (rotated_offDiagonal G hG hδ) d le_rfl
  have hc := MSManuscriptCleanupCount.count_add_high (rotated G δ) δ
  have he : removedCount (rotated G δ) δ d = d-Fintype.card (Retained G δ) := by
    change removedCount (rotated G δ) δ d + Fintype.card (Retained G δ) = d at hc
    omega
  have htr : realTrace (rotated G δ)=realTrace G := by
    rw [rotated_eq]
    exact trace_conjugation G (basis G δ)ᵀ (by simpa using basis_mul_transpose G δ)
  simpa only [output,trace_conjugation _ _ (basis_transpose_mul G δ),htr,he] using hb.trace

end MatrixSpencer.MSManuscriptJacobiCleanup
