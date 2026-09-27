import HigherRankKSRuntime.Tangent.FrameArithmetic

/-! Counted evaluation of the identity/Householder frame. The scalar
evaluation and nonzero-denominator contracts are proved in FrameArithmetic. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace HigherRankKSRuntime.Tangent.RuntimeFrame
open MatrixSpencer.RealRAM
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
open RadialBasis (Space)
open FrameArithmetic

def normalCompute {m : ℕ} (z : Space (m + 1)) : Counted (Space (m + 1)) :=
  let q : Space (m + 1) := WithLp.toLp 2 (fun i =>
    (normalizedExpr (m + 1) i).eval (WithLp.ofLp z))
  ⟨WithLp.toLp 2 (fun i => (normalExpr m i).eval (normalInput q)),
    (m + 1) * (4 * (m + 1) + 5) + (m + 1) * 8 + 10⟩

theorem normalCompute_value {m : ℕ} (z : Space (m + 1)) :
    (normalCompute z).value = normal z := by
  have hq : (WithLp.toLp 2 (fun i =>
      (normalizedExpr (m + 1) i).eval (WithLp.ofLp z)) : Space (m + 1)) = Frame.unitVector z := by
    ext i
    exact normalizedExpr_eval z i
  unfold normalCompute
  rw [hq]
  ext i
  exact normalExpr_eval (Frame.unitVector z) i

def compute : {m : ℕ} → (z : Space m) →
    Counted (Matrix (Fin m) (Fin (Frame.canonical m z).rank) ℝ)
  | 0, _ => ⟨fun i => Fin.elim0 i, 1⟩
  | m + 1, z =>
    if hz : z = 0 then
      ⟨fun i j => if i.val = j.val then 1 else 0, (normExpr (m + 1)).cost + 5*(m + 1)^2 + 10⟩
    else
      let u := normalCompute z
      ⟨fun i j =>
        let j' : Fin m := ⟨j.val, by simpa only [Frame.canonical, dif_neg hz, Frame.atNonzero] using j.isLt⟩
        (reflectionExpr (m + 1) i j'.succ).eval (WithLp.ofLp u.value),
        (normExpr (m + 1)).cost + u.cost + (m + 1) * m * (4 * (m + 1) + 14) + 10⟩

theorem compute_value {m : ℕ} (z : Space m) :
    (compute z).value = FrameFormula.columns (Frame.canonical m z).embed := by
  cases m with
  | zero => ext i; exact Fin.elim0 i
  | succ m =>
    have transport (F G : Frame z) (h : F=G) (i : Fin (m+1)) (j : Fin F.rank) :
        FrameFormula.columns F.embed i j =
          FrameFormula.columns G.embed i (Fin.cast (congrArg Frame.rank h) j) := by
      cases h
      rfl
    by_cases hz : z=0
    · have hc : Frame.canonical (m+1) z=Frame.atZero z hz := by simp [Frame.canonical,hz]
      ext i j
      rw [transport _ _ hc]
      simp only [compute,dif_pos hz]
      simp [Frame.atZero, FrameFormula.columns, EuclideanSpace.single_apply, Fin.ext_iff]
    · have hc : Frame.canonical (m+1) z=Frame.atNonzero z hz := by simp [Frame.canonical,hz]
      ext i j
      rw [transport _ _ hc]
      simp only [compute,dif_neg hz,normalCompute_value]
      exact computed_column z i (Fin.cast (congrArg Frame.rank hc) j)

theorem compute_cost {m : ℕ} (z : Space m) : (compute z).cost ≤ 100 * (m + 1)^4 := by
  cases m with
  | zero => norm_num [compute]
  | succ m =>
    by_cases hz : z = 0
    all_goals simp only [compute, hz, ↓reduceDIte, normExpr_cost, normalCompute]
    all_goals
      have h1 : m+1 ≤ m+2 := by omega
      have h2 : (m+2)^3 ≤ (m+2)^4 := Nat.pow_le_pow_right (by omega) (by omega)
      have hp : (m+1)*m*(4*(m+1)+14) ≤ 18*(m+2)^3 := by
        calc _ ≤ (m+2)*(m+2)*(18*(m+2)) := by gcongr <;> omega
             _ = _ := by ring
      have hq : (m+1)*(4*(m+1)+5) ≤ 9*(m+2)^2 := by
        calc _ ≤ (m+2)*(9*(m+2)) := by gcongr <;> omega
             _ = _ := by ring
      have h24 : (m+2)^2 ≤ (m+2)^4 := Nat.pow_le_pow_right (by omega) (by omega)
      have h14 : m+2 ≤ (m+2)^4 := Nat.le_self_pow (by omega) _
      nlinarith

theorem rank_le {m : ℕ} (z : Space m) : (Frame.canonical m z).rank ≤ m := by
  cases m with
  | zero => exact le_rfl
  | succ m =>
    by_cases hz : z = 0
    all_goals simp [Frame.canonical, hz, Frame.atZero, Frame.atNonzero]

end HigherRankKSRuntime.Tangent.RuntimeFrame
