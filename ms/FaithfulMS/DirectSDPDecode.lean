import FaithfulMS.DirectSDP
import MatrixSpencer.RealRAMSDPChart

/-! Literal scalar circuits for reading the density and objective from an
optimizing primal SDP point. The trace-one density chart uses a diagonal sum,
not a spectral basis computation. -/
open Matrix
open scoped BigOperators InnerProductSpace MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace FaithfulMS.DirectSDPDecode
open MatrixSpencer RealRAM
open RealRAM.JacobiIteration (Counted)
variable {d : ℕ}

abbrev Index (a : Fin d) := KSFullManuscriptTraceCoordinates.Index a
def embedExpr (a : Fin d) (p : Fin d × Fin d) : Expr (Index a) :=
  if h : p ≠ (a,a) then .input ⟨p,h⟩ else .constant 0
def completeExpr (a : Fin d) (p : Fin d × Fin d) : Expr (Index a) :=
  .sub (embedExpr a p) (if p=(a,a) then finiteSumExpr (fun i => embedExpr a (i,i)) else .constant 0)
def baseExpr (a : Fin d) (i j : Fin d) : ComplexExpr (Index a) :=
  .real (if i=j then .div (.constant 1) (.constant d) else .constant 0)
def densityExpr (a : Fin d) (i j : Fin d) : ComplexExpr (Index a) :=
  .add (baseExpr a i j) (RealRAM.SDPChart.decodeExpr (completeExpr a) i j)

theorem embed_eval (a : Fin d) (x : Index a → ℝ) (p : Fin d × Fin d) :
    (embedExpr a p).eval x = KSFullManuscriptTraceCoordinates.embed a x p := by
  unfold embedExpr KSFullManuscriptTraceCoordinates.embed
  split <;> simp [Expr.eval]

theorem complete_eval (a : Fin d) (x : Index a → ℝ) (p : Fin d × Fin d) :
    (completeExpr a p).eval x = KSFullManuscriptTraceCoordinates.complete a x p := by
  unfold completeExpr KSFullManuscriptTraceCoordinates.complete
  split <;> simp [Expr.eval, embed_eval, finiteSumExpr_eval]

theorem density_eval (a : Fin d) (x : Index a → ℝ) (hd : 0 < d) (i j : Fin d) :
    (densityExpr a i j).eval x =
      ((KSFullManuscriptCenterData.densityCenter hd : Matrix (Fin d) (Fin d) ℂ) +
        (KSFullManuscriptTraceCoordinates.linear a x : Matrix (Fin d) (Fin d) ℂ)) i j := by
  have hb : (baseExpr a i j).eval x =
      (KSFullManuscriptCenterData.densityCenter hd : Matrix (Fin d) (Fin d) ℂ) i j := by
    by_cases hij : i=j <;>
      simp [baseExpr, hij, Expr.eval, KSFullManuscriptCenterData.densityCenter,
        KSFullManuscriptStrictFeasible.density, Matrix.one_apply]
  simp only [densityExpr, ComplexExpr.eval_add, hb, RealRAM.SDPChart.decodeExpr_eval,
    complete_eval, Matrix.add_apply]
  rfl

theorem density_valid (a : Fin d) (x : Index a → ℝ) (hd : 0 < d) (i j : Fin d) :
    (densityExpr a i j).Valid x := by
  have he (p : Fin d × Fin d) : (embedExpr a p).Valid x := by
    unfold embedExpr; split <;> trivial
  apply ComplexExpr.valid_add
  · apply ComplexExpr.valid_real
    split
    · exact ⟨trivial, trivial, by simp only [Expr.eval]; exact_mod_cast hd.ne'⟩
    · trivial
  · apply RealRAM.SDPChart.decodeExpr_valid
    intro p
    refine ⟨he p, ?_⟩
    split
    · exact finiteSumExpr_valid _ _ (fun i => he (i,i))
    · trivial

theorem density_cost (a : Fin d) (i j : Fin d) :
    (densityExpr a i j).cost ≤ 4*d+14 := by
  have he (p : Fin d × Fin d) : (embedExpr a p).cost = 1 := by
    unfold embedExpr; split <;> rfl
  have hc (p : Fin d × Fin d) : (completeExpr a p).cost ≤ 2*d+3 := by
    unfold completeExpr
    split <;> simp only [Expr.cost, he, finiteSumExpr_cost, Fintype.card_fin,
      Finset.sum_const, Finset.card_univ, smul_eq_mul] <;> omega
  have hb : (baseExpr a i j).cost ≤ 4 := by
    unfold baseExpr; split <;> norm_num [ComplexExpr.cost_real, Expr.cost]
  have hh := RealRAM.SDPChart.decodeExpr_cost (completeExpr a) (2*d+3) hc i j
  rw [densityExpr, ComplexExpr.cost_add]
  omega

def density (a : Fin d) (x : Index a → ℝ) : Counted (Matrix (Fin d) (Fin d) ℂ) :=
  ⟨fun i j => (densityExpr a i j).eval x,
    ∑ i : Fin d, ∑ j : Fin d, ((densityExpr a i j).cost + 2)⟩

theorem density_value (a : Fin d) (x : Index a → ℝ) (hd : 0 < d) :
    (density a x).value =
      (KSFullManuscriptCenterData.densityCenter hd : Matrix (Fin d) (Fin d) ℂ) +
        (KSFullManuscriptTraceCoordinates.linear a x : Matrix (Fin d) (Fin d) ℂ) := by
  funext i j
  exact density_eval a x hd i j

theorem density_execution (a : Fin d) (x : Index a → ℝ) (hd : 0 < d) (i j : Fin d) :
    Expr.Executes x (densityExpr a i j).re ((density a x).value i j).re (densityExpr a i j).re.cost ∧
    Expr.Executes x (densityExpr a i j).im ((density a x).value i j).im (densityExpr a i j).im.cost :=
  ComplexExpr.executes _ _ (density_valid a x hd i j)

theorem density_cost_le (a : Fin d) (x : Index a → ℝ) :
    (density a x).cost ≤ d*d*(4*d+16) := by
  calc
    _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, (4*d+16) := by
      change (∑ i : Fin d, ∑ j : Fin d, ((densityExpr a i j).cost + 2)) ≤ _
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have h := density_cost a i j
      omega
    _ = _ := by simp [Nat.mul_assoc]

variable {ℓ : ℕ}
def affineInput (c x : KSFullManuscriptAffinePSD.Space ℓ) (offset : ℝ) :
    Option (Fin ℓ × Bool) → ℝ
  | none => offset
  | some (i,b) => if b then x i else c i
def affineExpr (ℓ : ℕ) : Expr (Option (Fin ℓ × Bool)) :=
  .add (.input none) (finiteSumExpr (fun i => .mul (.input (some (i,false))) (.input (some (i,true)))))
def affine (c x : KSFullManuscriptAffinePSD.Space ℓ) (offset : ℝ) : Counted ℝ :=
  ⟨(affineExpr ℓ).eval (affineInput c x offset), (affineExpr ℓ).cost + 1⟩

theorem affine_value (c x : KSFullManuscriptAffinePSD.Space ℓ) (offset : ℝ) :
    (affine c x offset).value = offset + ⟪c,x⟫_ℝ := by
  simp only [affine, affineExpr, Expr.eval, finiteSumExpr_eval, affineInput,
    Bool.false_eq_true, ↓reduceIte, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, star_trivial]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem affine_execution (c x : KSFullManuscriptAffinePSD.Space ℓ) (offset : ℝ) :
    Expr.Executes (affineInput c x offset) (affineExpr ℓ)
      (affine c x offset).value (affineExpr ℓ).cost := by
  apply Expr.executes_of_valid
  exact ⟨trivial, finiteSumExpr_valid _ _ (fun _ => ⟨trivial,trivial⟩)⟩

theorem affine_cost (c x : KSFullManuscriptAffinePSD.Space ℓ) (offset : ℝ) :
    (affine c x offset).cost = 4*ℓ+4 := by
  simp [affine, affineExpr, Expr.cost, finiteSumExpr_cost]
  omega

end FaithfulMS.DirectSDPDecode
