import MatrixSpencer.KSOptimizerFloor
import MatrixSpencer.FidelityBounds


open Matrix Set Filter
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator Topology
noncomputable section
namespace MatrixSpencer.KSFullManuscriptRegularizationBias
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}

theorem trace_square_mul_inv_le {A D : Matrix n n ℂ}
    (hA : A.PosDef) (hD : D.PosDef) (hAD : A ≤ D) :
    realTrace (A*A*D⁻¹) ≤ realTrace A := by
  have hi := KSOptimizerFloor.inverse_order hA hD hAD
  have hAA : (A*A).PosSemidef := by
    simpa only [hA.isHermitian.eq] using Matrix.posSemidef_conjTranspose_mul_self A
  have ht := realTrace_mul_nonneg hAA (Matrix.le_iff.mp hi)
  letI : Invertible A := hA.isUnit.invertible
  rw [Matrix.mul_sub, realTrace_sub, Matrix.mul_assoc, Matrix.mul_inv_of_invertible,
    Matrix.mul_one] at ht
  linarith

theorem trace_sqrt_subadd_posDef {X Y : Matrix n n ℂ}
    (hX : X.PosDef) (hY : Y.PosDef) :
    realTrace (CFC.sqrt (X+Y)) ≤ realTrace (CFC.sqrt X)+realTrace (CFC.sqrt Y) := by
  let A := CFC.sqrt X
  let B := CFC.sqrt Y
  have hA : A.PosDef := hX.posDef_sqrt
  have hB : B.PosDef := hY.posDef_sqrt
  have hD : (A+B).PosDef := hA.add_posSemidef hB.posSemidef
  have h1 := trace_square_mul_inv_le hA hD
    (le_add_of_nonneg_right hB.posSemidef.nonneg)
  have h2 := trace_square_mul_inv_le hB hD
    (le_add_of_nonneg_left hA.posSemidef.nonneg)
  have hXX : A*A=X := CFC.sqrt_mul_sqrt_self X hX.posSemidef.nonneg
  have hYY : B*B=Y := CFC.sqrt_mul_sqrt_self Y hY.posSemidef.nonneg
  rw [hXX] at h1
  rw [hYY] at h2
  have hsum := hX.posSemidef.add hY.posSemidef
  have ht := transportCost_lower_bound (S := X+Y) Matrix.PosSemidef.one
    (CFC.sqrt_nonneg (X+Y)).posSemidef.isHermitian hD
    (show CFC.sqrt (X+Y)*1*CFC.sqrt (X+Y)=X+Y by
      rw [Matrix.mul_one, CFC.sqrt_mul_sqrt_self _ hsum.nonneg])
  simp only [transportCost, Matrix.one_mul, Matrix.add_mul, realTrace_add] at ht
  linarith

theorem trace_sqrt_subadd {X Y : Matrix n n ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    realTrace (CFC.sqrt (X+Y)) ≤ realTrace (CFC.sqrt X)+realTrace (CFC.sqrt Y) := by
  have hxpos : ∀ᶠ r : ℝ in 𝓝[Ioi 0] 0, (regularize X r).PosSemidef := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (regularize_posDef hX hr).posSemidef
  have hypos : ∀ᶠ r : ℝ in 𝓝[Ioi 0] 0, (regularize Y r).PosSemidef := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (regularize_posDef hY hr).posSemidef
  have hspos : ∀ᶠ r : ℝ in 𝓝[Ioi 0] 0, (regularize X r+regularize Y r).PosSemidef := by
    filter_upwards [hxpos,hypos] with r hr hs
    exact hr.add hs
  have hx := continuous_realTrace.continuousAt.tendsto.comp
    (tendsto_matrix_sqrt_of_psd (regularize_tendsto X) hxpos hX)
  have hy := continuous_realTrace.continuousAt.tendsto.comp
    (tendsto_matrix_sqrt_of_psd (regularize_tendsto Y) hypos hY)
  have hs := continuous_realTrace.continuousAt.tendsto.comp
    (tendsto_matrix_sqrt_of_psd ((regularize_tendsto X).add (regularize_tendsto Y)) hspos (hX.add hY))
  apply le_of_tendsto_of_tendsto hs (hx.add hy)
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact trace_sqrt_subadd_posDef (regularize_posDef hX hr) (regularize_posDef hY hr)

theorem fidelity_source_subadd {S M T : Matrix n n ℂ}
    (hM : M.PosSemidef) (hT : T.PosSemidef) :
    fidelity S (M+T) ≤ fidelity S M+fidelity S T := by
  have hroot := (CFC.sqrt_nonneg S).posSemidef.isHermitian.eq
  have hm : (CFC.sqrt S*M*CFC.sqrt S).PosSemidef := by
    simpa only [hroot] using hM.conjTranspose_mul_mul_same (CFC.sqrt S)
  have ht : (CFC.sqrt S*T*CFC.sqrt S).PosSemidef := by
    simpa only [hroot] using hT.conjTranspose_mul_mul_same (CFC.sqrt S)
  simpa only [fidelity, fidelityCore, Matrix.mul_add, Matrix.add_mul] using trace_sqrt_subadd hm ht

/-- The exact uniform source bias (O8), including singular densities and sources. -/
theorem source_regularization_error {S M : Matrix n n ℂ}
    (hS : S.PosSemidef) (htrace : realTrace S = 1) (hM : M.PosSemidef)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    0 ≤ 2*fidelity S (M+ρ • 1)-2*fidelity S M ∧
      2*fidelity S (M+ρ • 1)-2*fidelity S M ≤
        2*Real.sqrt (ρ*(Fintype.card n : ℝ)) := by
  have hρI : (ρ • (1 : Matrix n n ℂ)).PosSemidef := Matrix.PosSemidef.one.smul hρ
  have hm := fidelity_mono hS hS hM (hM.add hρI) le_rfl
    (le_add_of_nonneg_right hρI.nonneg)
  have hu := fidelity_source_subadd (S := S) hM hρI
  have hb := fidelity_le_sqrt_trace_mul hS hρI
  rw [htrace, one_mul, realTrace_smul] at hb
  have hone : realTrace (1 : Matrix n n ℂ) = (Fintype.card n : ℝ) := by
    simp [realTrace, Matrix.trace]
  rw [hone] at hb
  constructor <;> linarith

def regularization (d : ℕ) (ν : ℝ) : ℝ := ν^2/(16*(d : ℝ))

theorem regularization_pos {d : ℕ} (hd : 0 < d) {ν : ℝ} (hν : 0 < ν) :
    0 < regularization d ν := by unfold regularization; positivity

theorem regularization_budget {d : ℕ} (hd : 0 < d) {ν : ℝ} (hν : 0 ≤ ν) :
    2*Real.sqrt (regularization d ν*(d : ℝ)) = ν/2 := by
  have hn : (d : ℝ) ≠ 0 := (Nat.cast_pos.mpr hd).ne'
  have he : regularization d ν*(d : ℝ) = (ν/4)^2 := by
    unfold regularization
    field_simp
    <;> ring
  rw [he, Real.sqrt_sq (by positivity : 0 ≤ ν/4)]
  ring

/-- The source perturbation consumes half the requested value-error budget. -/
theorem source_regularization_precision {S M : Matrix n n ℂ}
    (hS : S.PosSemidef) (htrace : realTrace S = 1) (hM : M.PosSemidef)
    (hn : 0 < Fintype.card n) {ν : ℝ} (hν : 0 < ν) :
    |2*fidelity S (M+regularization (Fintype.card n) ν • 1)-2*fidelity S M| ≤ ν/2 := by
  have h := source_regularization_error hS htrace hM (regularization_pos hn hν).le
  rw [abs_of_nonneg h.1]
  simpa only [regularization_budget hn hν.le] using h.2

/-- Maximizing over an unchanged feasible set preserves a uniform positive bias. -/
theorem supremum_bias {α : Type*} [Nonempty α] (f g : α → ℝ) {B : ℝ}
    (hf : BddAbove (Set.range f)) (hfg : ∀ x, f x ≤ g x)
    (hgf : ∀ x, g x ≤ f x+B) :
    sSup (Set.range f) ≤ sSup (Set.range g) ∧
      sSup (Set.range g) ≤ sSup (Set.range f)+B := by
  have hg : BddAbove (Set.range g) := by
    obtain ⟨c,hc⟩ := hf
    refine ⟨c+B, ?_⟩
    rintro y ⟨x,rfl⟩
    exact (hgf x).trans (add_le_add_right (hc (Set.mem_range_self x)) B)
  constructor
  · apply csSup_le (Set.range_nonempty f)
    rintro y ⟨x,rfl⟩
    exact (hfg x).trans (le_csSup hg (Set.mem_range_self x))
  · apply csSup_le (Set.range_nonempty g)
    rintro y ⟨x,rfl⟩
    exact (hgf x).trans (add_le_add_right (le_csSup hf (Set.mem_range_self x)) B)

/-- A regularized-SDP report accurate to ν/2 is accurate to ν for the
unregularized value when (O8)--(O9) supply the other half. -/
theorem report_error {report regularized original ν : ℝ}
    (hreport : |report-regularized| ≤ ν/2)
    (hbias : |regularized-original| ≤ ν/2) : |report-original| ≤ ν := by
  calc
    _ = |(report-regularized)+(regularized-original)| := by congr 1; ring
    _ ≤ |report-regularized|+|regularized-original| := abs_add_le _ _
    _ ≤ ν := by linarith

end MatrixSpencer.KSFullManuscriptRegularizationBias
