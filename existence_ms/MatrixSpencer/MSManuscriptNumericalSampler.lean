import MatrixSpencer.KSEighthManuscriptLDL
import MatrixSpencer.CovarianceSampler


open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.MSManuscriptNumericalSampler
open KSEighthManuscriptLDL
variable {d : ℕ}

def columnEnergy (Q : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) : ℝ := ∑ i, (lowerColumn Q j i)^2
def mass (Q : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) : ℝ := pivot Q j*columnEnergy Q j
abbrev Index (Q : Matrix (Fin d) (Fin d) ℝ) := {j : Fin d // 0<pivot Q j}
abbrev Draws (Q : Matrix (Fin d) (Fin d) ℝ) := Index Q × Bool

def scale (Q : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) : ℝ :=
  Real.sqrt (realTrace Q)/Real.sqrt (columnEnergy Q j)
def weight (Q : Matrix (Fin d) (Fin d) ℝ) (s : Draws Q) : ℝ := mass Q s.1.val/(2*realTrace Q)
def increment (Q : Matrix (Fin d) (Fin d) ℝ) (s : Draws Q) : EuclideanSpace ℝ (Fin d) :=
  if s.2 then scale Q s.1.val • WithLp.toLp 2 (lowerColumn Q s.1.val)
  else -(scale Q s.1.val • WithLp.toLp 2 (lowerColumn Q s.1.val))

theorem columnEnergy_nonneg (Q : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) : 0≤columnEnergy Q j :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem lowerColumn_diagonal (Q : Matrix (Fin d) (Fin d) ℝ) (j : Index Q) :
    lowerColumn Q j.val j.val=1 := by
  change pivot Q j.val/pivot Q j.val=1
  exact div_self j.property.ne'

theorem columnEnergy_pos (Q : Matrix (Fin d) (Fin d) ℝ) (j : Index Q) : 0<columnEnergy Q j.val := by
  have h := Finset.single_le_sum (s := Finset.univ) (f := fun i => (lowerColumn Q j.val i)^2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ j.val)
  dsimp only at h
  rw [lowerColumn_diagonal] at h
  norm_num at h
  exact lt_of_lt_of_le (by norm_num : (0:ℝ)<1) h

theorem columnEnergy_eq_norm_sq (Q : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) :
    columnEnergy Q j=‖(WithLp.toLp 2 (lowerColumn Q j) : EuclideanSpace ℝ (Fin d))‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs]
  rfl

theorem mass_eq_trace_term (Q : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) : mass Q j=realTrace (term Q j) := by
  rw [term,realTrace_smul]
  simp only [mass,columnEnergy,realTrace,Matrix.trace,Matrix.diag,Matrix.vecMulVec_apply,pow_two]
  rfl

theorem sum_mass (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosSemidef) : ∑ j,mass Q j=realTrace Q := by
  simp_rw [mass_eq_trace_term]
  rw [←realTrace_sum, sum_terms hQ]

private theorem sum_positive (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosSemidef)
    {E : Type*} [AddCommMonoid E] (f : Fin d → E) (hf : ∀ j,pivot Q j=0→f j=0) :
    (∑ j : Index Q,f j.val)=∑ j,f j := by
  classical
  have h := Fintype.sum_subtype_add_sum_subtype (fun j : Fin d => 0<pivot Q j) f
  have hz : (∑ j : {j : Fin d // ¬0<pivot Q j},f j.val)=0 := by
    apply Finset.sum_eq_zero
    intro j _
    exact hf j.val (le_antisymm (not_lt.mp j.property) (pivot_nonneg hQ j.val))
  simpa only [hz,add_zero] using h

theorem weight_pos (Q : Matrix (Fin d) (Fin d) ℝ) (hq : 0<realTrace Q) (s : Draws Q) :
    0<weight Q s := by
  exact div_pos (mul_pos s.1.property (columnEnergy_pos Q s.1)) (mul_pos (by norm_num) hq)

theorem weight_sum (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosSemidef) (hq : 0<realTrace Q) :
    (∑ s : Draws Q,weight Q s)=1 := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [weight,Fintype.sum_bool]
  have he (j : Index Q) : mass Q j.val/(2*realTrace Q)+mass Q j.val/(2*realTrace Q)=mass Q j.val/realTrace Q := by ring
  simp only [he,←Finset.sum_div]
  rw [sum_positive Q hQ (mass Q) (by intro j hj; simp [mass,hj]),sum_mass Q hQ]
  exact div_self hq.ne'

theorem mean_zero (Q : Matrix (Fin d) (Fin d) ℝ) :
    (∑ s : Draws Q,weight Q s • increment Q s)=0 := by
  classical
  rw [Fintype.sum_prod_type]
  simp [weight,increment]

theorem scale_sq_energy (Q : Matrix (Fin d) (Fin d) ℝ) (hq : 0≤realTrace Q) (j : Index Q) :
    (scale Q j.val)^2*columnEnergy Q j.val=realTrace Q := by
  rw [scale,div_pow,Real.sq_sqrt hq,Real.sq_sqrt (columnEnergy_pos Q j).le]
  exact div_mul_cancel₀ _ (columnEnergy_pos Q j).ne'

theorem increment_norm_sq (Q : Matrix (Fin d) (Fin d) ℝ) (hq : 0≤realTrace Q) (s : Draws Q) :
    ‖increment Q s‖^2=realTrace Q := by
  have he := scale_sq_energy Q hq s.1
  rw [columnEnergy_eq_norm_sq] at he
  rcases s with ⟨j,b⟩
  cases b <;> simpa only [increment,Bool.false_eq_true,↓reduceIte,norm_neg,norm_smul,
    Real.norm_eq_abs,mul_pow,sq_abs] using he

theorem increment_rankOne (Q : Matrix (Fin d) (Fin d) ℝ) (s : Draws Q) :
    realRankOne (WithLp.ofLp (increment Q s))=
      (scale Q s.1.val)^2 • realRankOne (lowerColumn Q s.1.val) := by
  rcases s with ⟨j,b⟩
  cases b <;> simp [increment,realRankOne_neg,realRankOne_smul]

theorem covariance (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosSemidef) (hq : 0<realTrace Q) :
    (∑ s : Draws Q,weight Q s • realRankOne (WithLp.ofLp (increment Q s)))=Q := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [weight,increment_rankOne,Fintype.sum_bool,smul_smul,←add_smul]
  have he (j : Index Q) :
      mass Q j.val/(2*realTrace Q)*(scale Q j.val)^2+
        mass Q j.val/(2*realTrace Q)*(scale Q j.val)^2=pivot Q j.val := by
    have hs := scale_sq_energy Q hq.le j
    have hmul := congrArg (fun z : ℝ => 2*pivot Q j.val*z) hs
    unfold mass
    field_simp
    nlinarith only [hmul]
  simp only [he]
  change (∑ j : Index Q,term Q j.val)=Q
  rw [sum_positive Q hQ (term Q) (by intro j hj; simp [term,hj]),sum_terms hQ]

theorem lowerColumn_mem_range (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosSemidef) (j : Fin d) :
    (WithLp.toLp 2 (lowerColumn Q j) : EuclideanSpace ℝ (Fin d)) ∈
      LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) Q).toLinearMap := by
  have hr := posSemidef_range_le_of_le (residual_posSemidef hQ j) hQ (residual_le hQ j)
  apply hr
  refine ⟨(pivot Q j)⁻¹ • EuclideanSpace.single j 1,?_⟩
  apply WithLp.ofLp_injective
  change residual Q j *ᵥ ((pivot Q j)⁻¹ • (Pi.single j 1 : Fin d → ℝ)) = lowerColumn Q j
  rw [Matrix.mulVec_smul, Matrix.mulVec_single_one]
  ext i
  change (pivot Q j)⁻¹ * residual Q j i j = residual Q j i j / pivot Q j
  ring

theorem increment_mem_range (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosSemidef) (s : Draws Q) :
    increment Q s ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) Q).toLinearMap := by
  have h := lowerColumn_mem_range Q hQ s.1.val
  unfold increment
  split_ifs
  · exact Submodule.smul_mem _ _ h
  · exact Submodule.neg_mem _ (Submodule.smul_mem _ _ h)

end MatrixSpencer.MSManuscriptNumericalSampler
