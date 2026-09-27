import RadialKS.FrameFormula
import MatrixSpencer.RealRAMLinearAlgebra
import MatrixSpencer.RealRAMJacobiIteration
import MatrixSpencer.RealRAMProgram

/-! Executed scalar circuits for the Householder frame. Square roots and
divisions carry their validity proofs; a frame is not an extra primitive. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace RadialKS.FrameArithmetic
open MatrixSpencer.RealRAM
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
open RadialBasis (Space)
variable {m : ℕ}

def normExpr (m : ℕ) : Expr (Fin m) := .sqrt (dotExpr m id id)

theorem normExpr_eval (z : Space m) :
    (normExpr m).eval (WithLp.ofLp z) = ‖z‖ := by
  rw [normExpr, Expr.eval, dotExpr_eval]
  have hs : (∑ i, z i * z i) = ‖z‖ ^ 2 := by
    have hh := (EuclideanSpace.norm_sq_eq z).symm
    simp only [Real.norm_eq_abs, sq_abs] at hh
    simpa only [pow_two] using hh
  simp only [id_eq, PiLp.ofLp_apply]
  rw [hs, Real.sqrt_sq (norm_nonneg z)]

theorem normExpr_valid (z : Space m) : (normExpr m).Valid (WithLp.ofLp z) := by
  refine ⟨dotExpr_valid _ _ _ _, ?_⟩
  rw [dotExpr_eval]
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (z i))

theorem normExpr_cost (m : ℕ) : (normExpr m).cost = 4 * m + 2 := by
  simp [normExpr, Expr.cost, dotExpr_cost]

def normalizedExpr (m : ℕ) (i : Fin m) : Expr (Fin m) :=
  .div (.input i) (normExpr m)

theorem normalizedExpr_eval (z : Space m) (i : Fin m) :
    (normalizedExpr m i).eval (WithLp.ofLp z) = Frame.unitVector z i := by
  simp only [normalizedExpr, Expr.eval, normExpr_eval, Frame.unitVector, PiLp.smul_apply,
    smul_eq_mul, PiLp.ofLp_apply, div_eq_mul_inv, mul_comm]

theorem normalizedExpr_valid (z : Space m) (hz : z ≠ 0) (i : Fin m) :
    (normalizedExpr m i).Valid (WithLp.ofLp z) := by
  refine ⟨trivial, normExpr_valid z, ?_⟩
  rw [normExpr_eval]
  exact norm_ne_zero_iff.mpr hz

theorem normalizedExpr_cost (m : ℕ) (i : Fin m) :
    (normalizedExpr m i).cost = 4 * m + 4 := by
  simp only [normalizedExpr, Expr.cost, normExpr_cost]
  omega

theorem normalization_execution (z : Space m) (hz : z ≠ 0) (i : Fin m) :
    Expr.Executes (WithLp.ofLp z) (normalizedExpr m i) (Frame.unitVector z i) (4 * m + 4) := by
  simpa only [normalizedExpr_eval, normalizedExpr_cost] using
    Expr.executes_of_valid _ _ (normalizedExpr_valid z hz i)

def normal (z : Space (m + 1)) : Space (m + 1) :=
  Frame.unitVector z - RadialBasis.target (Frame.unitVector z)

def reflectionExpr (m : ℕ) (i j : Fin m) : Expr (Fin m) :=
  .sub (.constant (if i = j then 1 else 0))
    (.div (.mul (.constant 2) (.mul (.input i) (.input j))) (dotExpr m id id))

theorem reflectionExpr_eval (u : Space m) (i j : Fin m) :
    (reflectionExpr m i j).eval (WithLp.ofLp u) =
      (if i = j then 1 else 0) - 2 * u i * u j / ‖u‖ ^ 2 := by
  simp only [reflectionExpr, Expr.eval, dotExpr_eval, PiLp.ofLp_apply, id_eq]
  have hs : (∑ k, u k * u k) = ‖u‖ ^ 2 := by
    have hh := (EuclideanSpace.norm_sq_eq u).symm
    simp only [Real.norm_eq_abs, sq_abs] at hh
    simpa only [pow_two] using hh
  rw [hs]
  split_ifs <;> norm_num <;> ring

theorem reflectionExpr_valid (u : Space m) (hu : u ≠ 0) (i j : Fin m) :
    (reflectionExpr m i j).Valid (WithLp.ofLp u) := by
  refine ⟨trivial, ⟨trivial, trivial, trivial⟩, dotExpr_valid _ _ _ _, ?_⟩
  rw [dotExpr_eval]
  simp only [id_eq, PiLp.ofLp_apply]
  have hs : (∑ k, u k * u k) = ‖u‖ ^ 2 := by
    have hh := (EuclideanSpace.norm_sq_eq u).symm
    simp only [Real.norm_eq_abs, sq_abs] at hh
    simpa only [pow_two] using hh
  rw [hs]
  exact pow_ne_zero _ (norm_ne_zero_iff.mpr hu)

theorem reflectionExpr_cost (m : ℕ) (i j : Fin m) :
    (reflectionExpr m i j).cost = 4 * m + 9 := by
  simp only [reflectionExpr, Expr.cost, dotExpr_cost]
  omega

theorem normal_ne_zero (z : Space (m + 1)) (hz : z ≠ 0) : normal z ≠ 0 := by
  have hd := FrameFormula.householder_denominator (Frame.unitVector z) (Frame.unitVector_norm z hz)
  intro h
  change 2 ≤ ‖normal z‖ ^ 2 at hd
  rw [h, norm_zero] at hd
  norm_num at hd

theorem reflection_execution (z : Space (m + 1)) (hz : z ≠ 0) (i j : Fin (m + 1)) :
    Expr.Executes (WithLp.ofLp (normal z)) (reflectionExpr (m + 1) i j)
      ((if i = j then 1 else 0) - 2 * normal z i * normal z j / ‖normal z‖ ^ 2)
      (4 * (m + 1) + 9) := by
  simpa only [reflectionExpr_eval, reflectionExpr_cost] using
    Expr.executes_of_valid _ _ (reflectionExpr_valid (normal z) (normal_ne_zero z hz) i j)

def normalExpr (m : ℕ) (i : Fin (m + 1)) : Expr (Fin (m + 1) ⊕ Unit) :=
  .add (.input (.inl i)) (if i = 0 then .input (.inr ()) else .constant 0)

def normalInput (q : Space (m + 1)) : Fin (m + 1) ⊕ Unit → ℝ :=
  Sum.elim (WithLp.ofLp q) (fun _ => RadialBasis.sign q)

theorem normalExpr_eval (q : Space (m + 1)) (i : Fin (m + 1)) :
    (normalExpr m i).eval (normalInput q) = (q - RadialBasis.target q) i := by
  by_cases hi : i = 0
  · subst i
    simp [normalExpr, Expr.eval, normalInput, RadialBasis.target]
  · simp [normalExpr, Expr.eval, normalInput, RadialBasis.target, hi]

theorem normalExpr_valid (q : Space (m + 1)) (i : Fin (m + 1)) :
    (normalExpr m i).Valid (normalInput q) := by
  unfold normalExpr
  split_ifs <;> exact ⟨trivial, trivial⟩

theorem normalExpr_cost (m : ℕ) (i : Fin (m + 1)) : (normalExpr m i).cost = 3 := by
  unfold normalExpr
  split_ifs <;> rfl

theorem pad_single (j : Fin m) : RadialBasis.pad (EuclideanSpace.single j (1 : ℝ)) =
    EuclideanSpace.single j.succ 1 := by
  ext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [RadialBasis.pad, EuclideanSpace.single_apply, Ne.symm (Fin.succ_ne_zero j)]
  · simp [RadialBasis.pad, EuclideanSpace.single_apply, Pi.single_apply]

theorem computed_column (z : Space (m + 1)) (i : Fin (m + 1)) (j : Fin m) :
    (reflectionExpr (m + 1) i j.succ).eval (WithLp.ofLp (normal z)) =
      FrameFormula.columns (RadialBasis.embedding (Frame.unitVector z)) i j := by
  rw [reflectionExpr_eval]
  change _ = RadialBasis.reflection (Frame.unitVector z)
    (RadialBasis.pad (EuclideanSpace.single j 1)) i
  rw [pad_single, RadialBasis.reflection_formula, EuclideanSpace.inner_single_right]
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, EuclideanSpace.single_apply,
    starRingEnd_apply, star_trivial, one_mul]
  change _ = (if i = j.succ then 1 else 0) -
    (2 * normal z j.succ / ‖normal z‖ ^ 2) * normal z i
  ring

theorem zero_test (z : Space m) : (normExpr m).eval (WithLp.ofLp z) = 0 ↔ z = 0 := by
  rw [normExpr_eval, norm_eq_zero]

theorem norm_execution (z : Space m) :
    Expr.Executes (WithLp.ofLp z) (normExpr m) ‖z‖ (4*m+2) := by
  simpa only [normExpr_eval, normExpr_cost] using
    Expr.executes_of_valid _ _ (normExpr_valid z)

theorem scalar_execution (z : Space (m+1)) (hz : z ≠ 0) :
    (∀ i, Expr.Executes (WithLp.ofLp z) (normalizedExpr (m+1) i)
      (Frame.unitVector z i) (4*(m+1)+4)) ∧
    (∀ i, Expr.Executes (normalInput (Frame.unitVector z)) (normalExpr m i)
      (normal z i) 3) ∧
    (∀ i j, Expr.Executes (WithLp.ofLp (normal z)) (reflectionExpr (m+1) i j)
      ((if i=j then 1 else 0)-2*normal z i*normal z j/‖normal z‖^2) (4*(m+1)+9)) := by
  refine ⟨normalization_execution z hz, ?_, reflection_execution z hz⟩
  intro i
  simpa only [normalExpr_eval, normalExpr_cost, normal] using
    Expr.executes_of_valid _ _ (normalExpr_valid (Frame.unitVector z) i)

def signProgram : Program (Fin 2) :=
  .branchLE (.constant 0) (.input 0) (.assign 1 (.constant 1)) (.assign 1 (.constant (-1)))

theorem signProgram_value (q : Space (m+1)) :
    signProgram.run ![q 0, 0] 1 = RadialBasis.sign q := by
  simp only [signProgram, Program.run, Expr.eval, Matrix.cons_val_zero,
    Function.update_self, RadialBasis.sign]
  split_ifs <;> norm_num at * <;> linarith

theorem signProgram_execution (q : Space (m+1)) :
    Program.Executes signProgram ![q 0, 0] (signProgram.run ![q 0, 0]) 5 := by
  have hs : signProgram.Safe ![q 0, 0] := by
    simp [signProgram, Program.Safe, Expr.Valid]
  have hc : signProgram.cost ![q 0, 0] = 5 := by
    simp [signProgram, Program.cost, Expr.cost]
  simpa only [hc] using Program.executes_of_safe _ _ hs

end RadialKS.FrameArithmetic
