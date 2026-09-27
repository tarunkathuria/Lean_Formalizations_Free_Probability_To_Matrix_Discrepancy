import MatrixSpencer.KSEighthCountedHessian
import MatrixSpencer.RealRAMLDL


open Matrix Set
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSEighthCountedMovement
open RealRAM RealRAM.JacobiIteration KSEighthLiveEnumeration
variable {N m : ℕ}
set_option maxRecDepth 4096

def physical (x : Fin N → ℝ) (Q : Matrix (Fin (count x)) (Fin (count x)) ℝ) :
    Counted (Matrix (Fin (count x)) (Fin (count x)) ℝ) :=
  let l := KSEighthCountedHessian.liveLabels x
  ⟨fun i j =>
    Real.sqrt (1-(KSEighthManuscriptMovement.livePoint x i)^2)*Q i j*
      Real.sqrt (1-(KSEighthManuscriptMovement.livePoint x j)^2),
    l.cost+(count x)^2*(12*N+40)+1⟩

theorem physical_value (x : Fin N → ℝ) (Q : Matrix (Fin (count x)) (Fin (count x)) ℝ) :
    (physical x Q).value=KSEighthManuscriptMovement.physicalCovariance x Q := by
  ext i j
  simp [physical,KSEighthManuscriptMovement.physicalCovariance,KSSymmetricProgress.scaledCovariance,
    Matrix.diagonal_mul,Matrix.mul_diagonal]

theorem physical_cost (x : Fin N → ℝ) (Q : Matrix (Fin (count x)) (Fin (count x)) ℝ) :
    (physical x Q).cost≤100*(N+1)^3 := by
  have hl := KSEighthCountedHessian.liveLabels_cost x
  have hk := KSEighthManuscriptMovement.count_le x
  dsimp only [physical]
  calc
    _ ≤ 23*N+2+N^2*(12*N+40)+1 := by gcongr
    _ ≤ _ := by nlinarith [Nat.zero_le (N^2),Nat.zero_le (N^3)]

def factorInput (P : Mat m) : LDL.Registers m → ℝ
  | .inl (.inl (_,ij)) => P ij.1 ij.2
  | _ => 0

@[simp] theorem factorInput_matrix (P : Mat m) :
    ConstraintScan.matrix (factorInput P ∘ Sum.inl) 0=P := rfl

def factor (P : Mat m) : Counted ((Fin m → ℝ) × (Fin m → Fin m → ℝ)) :=
  let w := (LDL.program m).run (factorInput P)
  ⟨(fun j=>w (.inr (.inl j)),fun j i=>w (.inr (.inr (j,i)))),
    (LDL.program m).cost (factorInput P)+10*(m+1)^3+1⟩

theorem factor_pivot (P : Mat m) (j : Fin m) :
    (factor P).value.1 j=KSEighthManuscriptLDL.pivot P j := by
  simpa only [factor,factorInput_matrix,Sum.elim_inl,MSManuscriptNumericalLDL.pivot_eq] using
    LDL.program_output (factorInput P) (.inl j)

theorem factor_column (P : Mat m) (j i : Fin m) :
    (factor P).value.2 j i=KSEighthManuscriptLDL.lowerColumn P j i := by
  simpa only [factor,factorInput_matrix,Sum.elim_inr,MSManuscriptNumericalLDL.lowerColumn_eq] using
    LDL.program_output (factorInput P) (.inr (j,i))

theorem factor_cost (P : Mat m) : (factor P).cost≤80*(m+1)^5 := by
  have hp := ((LDL.program m).cost_le_bound (factorInput P)).trans (LDL.program_bound m)
  have h3 : (m+1)^3≤(m+1)^5 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : 1≤(m+1)^5 := Nat.one_le_pow 5 _ (by omega)
  dsimp only [factor]
  omega

theorem factor_execution (P : Mat m) :
    ∃k≤60*(m+1)^5,Program.Executes (LDL.program m) (factorInput P)
      ((LDL.program m).run (factorInput P)) k := by
  obtain ⟨k,hk,he⟩ := Program.safe_execution_bounded (LDL.program m) (factorInput P)
    (LDL.program_safe _)
  exact ⟨k,hk.trans (LDL.program_bound m),he⟩

def sample (P : Mat m) (z : Fin m × Bool) : Counted (EuclideanSpace ℝ (Fin m)) :=
  let f := factor P
  let u := Real.sqrt ((m:ℝ)*f.value.1 z.1)
  ⟨WithLp.toLp 2 (fun i => if z.2 then u*f.value.2 z.1 i else -(u*f.value.2 z.1 i)),
    f.cost+30*m+20⟩

theorem sample_value (P : Mat m) (z : Fin m × Bool) :
    (sample P z).value=KSEighthManuscriptSampler.increment P z := by
  ext i
  simp only [sample,factor_pivot,factor_column,KSEighthManuscriptSampler.increment,
    KSEighthManuscriptSampler.unsigned]
  cases z.2 <;> simp

theorem sample_cost (P : Mat m) (z : Fin m × Bool) :
    (sample P z).cost≤130*(m+1)^5 := by
  have hf := factor_cost P
  have hm : m≤(m+1)^5 := by
    have hh := Nat.pow_le_pow_right (n:=m+1) (by omega) (show 1≤5 by omega)
    simp only [pow_one] at hh
    omega
  have h1 : 1≤(m+1)^5 := Nat.one_le_pow 5 _ (by omega)
  dsimp only [sample]
  omega

def proposal (x : Fin N → ℝ) (Q : Matrix (Fin (count x)) (Fin (count x)) ℝ)
    (h : ℝ) (z : Fin (count x) × Bool) : Counted (Fin N → ℝ) :=
  let p := physical x Q
  let s := sample p.value z
  ⟨fun i=>x i+h*extend x s.value i,p.cost+s.cost+N*(12*N+30)+2⟩

theorem proposal_value (x : Fin N → ℝ) (Q : Matrix (Fin (count x)) (Fin (count x)) ℝ)
    (h : ℝ) (z : Fin (count x) × Bool) :
    (proposal x Q h z).value=KSEighthManuscriptMovement.proposal x Q h z := by
  funext i
  simp only [proposal,physical_value,sample_value,KSEighthManuscriptMovement.proposal,
    KSEighthManuscriptMovement.increment]
  rfl

def costBudget (N : ℕ) : ℕ := 100*(N+1)^3+130*(N+1)^5+N*(12*N+30)+2

theorem proposal_cost (x : Fin N → ℝ) (Q : Matrix (Fin (count x)) (Fin (count x)) ℝ)
    (h : ℝ) (z : Fin (count x) × Bool) :
    (proposal x Q h z).cost≤costBudget N := by
  have hp := physical_cost x Q
  have hs := sample_cost (physical x Q).value z
  have hk := KSEighthManuscriptMovement.count_le x
  have hs' : (sample (physical x Q).value z).cost≤130*(N+1)^5 := by
    apply hs.trans
    gcongr
  dsimp only [proposal,costBudget]
  omega

end MatrixSpencer.KSEighthCountedMovement
