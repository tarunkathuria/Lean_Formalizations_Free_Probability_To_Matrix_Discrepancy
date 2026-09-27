import RadialKS.RuntimePolynomial
import SeamlessKS.RuntimeEmpty


open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace FaithfulKS
open MatrixSpencer MatrixSpencer.KSPolynomialConvexSolver
open MatrixSpencer.RealRAM.JacobiIteration (Counted)

def compute (P : PolynomialSolver) {N d : ℕ} (v : Fin N → Fin d → ℂ)
    (hp : ∑ i, KSRankOne.atom (v i) = 1) : Counted (Fin N → ℝ) :=
  if hd : 0 < d then
    letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    let r := RadialKS.RuntimeRun.compute P v hd hp
    ⟨r.value, r.cost + 1⟩
  else ⟨SeamlessKS.RuntimeEmpty.output N, 2*N+1⟩

/-- The zero branch executes the actual scalar writes; the other branch
executes exactly the SDP-query, restricted-EVD, and rounding loop. -/
def Executes (P : PolynomialSolver) {N d : ℕ} (v : Fin N → Fin d → ℂ)
    (hp : ∑ i, KSRankOne.atom (v i) = 1) (result : Fin N → ℝ) (cost : ℕ) : Prop :=
  if hd : 0 < d then
    letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    ∃ c, RadialKS.RuntimeRun.Executes P v hd hp result c ∧ cost = c+1
  else
    MatrixSpencer.RealRAM.Program.Executes (SeamlessKS.RuntimeEmpty.program N)
      (SeamlessKS.RuntimeEmpty.input N) result (2*N) ∧ cost = 2*N+1

def polynomial (P : PolynomialSolver) : MvPolynomial (Fin 2) ℕ :=
  RadialKS.RuntimePolynomial.polynomial P + 2 * MvPolynomial.X 0 + 1

theorem eval_polynomial (P : PolynomialSolver) (N d : ℕ) :
    MvPolynomial.eval ![N,d] (polynomial P) =
      RadialKS.RuntimeRun.costBound P N d + 2*N+1 := by
  simp [polynomial, RadialKS.RuntimePolynomial.eval_polynomial]

theorem compute_executes (P : PolynomialSolver) {N d : ℕ}
    (v : Fin N → Fin d → ℂ) (hp : ∑ i, KSRankOne.atom (v i) = 1) :
    Executes P v hp (compute P v hp).value (compute P v hp).cost := by
  by_cases hd : 0 < d
  · letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
    simp only [Executes, compute, dif_pos hd]
    exact ⟨_, RadialKS.RuntimeRun.compute_execution P v hd hp, rfl⟩
  · simp only [Executes, compute, dif_neg hd]
    exact ⟨SeamlessKS.RuntimeEmpty.execution N, trivial⟩

theorem compute_cost (P : PolynomialSolver) {N d : ℕ}
    (v : Fin N → Fin d → ℂ) (hp : ∑ i, KSRankOne.atom (v i) = 1) :
    (compute P v hp).cost ≤ MvPolynomial.eval ![N,d] (polynomial P) := by
  rw [eval_polynomial]
  by_cases hd : 0 < d
  · letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
    have h := RadialKS.RuntimeRun.execution_cost P v hd hp
      (RadialKS.RuntimeRun.compute_execution P v hd hp)
    simp only [compute, dif_pos hd]
    omega
  · simp only [compute, dif_neg hd]
    omega

theorem compute_correct (P : PolynomialSolver) {N d : ℕ}
    (v : Fin N → Fin d → ℂ) (hp : ∑ i, KSRankOne.atom (v i) = 1)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hsize : ∀ i, ‖(WithLp.toLp 2 (v i) : EuclideanSpace ℂ (Fin d))‖^2 ≤ ε) :
    (∀ i, (compute P v hp).value i = 1 ∨ (compute P v hp).value i = -1) ∧
      ‖∑ i, (compute P v hp).value i • KSRankOne.atom (v i)‖ ≤
        35 * Real.sqrt ε := by
  by_cases hd : 0 < d
  · letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
    have hnorm : ∀ i, ‖KSRankOne.atom (v i)‖ ≤ ε := by
      intro i
      simpa only [KSRankOne.atom_norm, KSRankOne.realTrace_atom_eq_norm_sq] using hsize i
    simp only [compute, dif_pos hd, RadialKS.RuntimeRun.compute_value]
    exact ⟨RadialKS.Run.output_signs P.solver v hd hp,
      RadialKS.Run.output_norm_le P.solver v hd hp hε hnorm⟩
  · have hz : d = 0 := Nat.eq_zero_of_not_pos hd
    subst d
    simp only [compute, dif_neg (by omega : ¬0<0)]
    refine ⟨fun _ => Or.inl rfl, ?_⟩
    have he : (∑ i, SeamlessKS.RuntimeEmpty.output N i • KSRankOne.atom (v i)) =
        (0 : Matrix (Fin 0) (Fin 0) ℂ) := Subsingleton.elim _ _
    rw [he, norm_zero]
    positivity

/-- One polynomial is fixed before the dimensions and matrix entries vary.
Its bound applies to the same computed signing whose discrepancy is certified. -/
theorem polynomial_runtime_and_correctness (P : PolynomialSolver) :
    ∃ q : MvPolynomial (Fin 2) ℕ, ∀ (N d : ℕ)
      (v : Fin N → Fin d → ℂ)
      (hp : (∑ i, (fun a b => v i a * star (v i b) : Matrix (Fin d) (Fin d) ℂ)) = (1 : Matrix (Fin d) (Fin d) ℂ))
      (ε : ℝ), 0 ≤ ε →
      (∀ i, ‖(WithLp.toLp 2 (v i) : EuclideanSpace ℂ (Fin d))‖^2 ≤ ε) →
      ∃ cost, Executes P v hp (compute P v hp).value cost ∧
        cost ≤ MvPolynomial.eval ![N,d] q ∧
        (∀ i, (compute P v hp).value i = 1 ∨ (compute P v hp).value i = -1) ∧
        ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
          (∑ i, ((compute P v hp).value i : ℂ) •
            (fun a b => v i a * star (v i b) : Matrix (Fin d) (Fin d) ℂ))‖
          ≤ 35 * Real.sqrt ε := by
  refine ⟨polynomial P, ?_⟩
  intro N d v hp ε hε hsize
  have hs := compute_correct P v hp hε hsize
  refine ⟨(compute P v hp).cost, compute_executes P v hp, compute_cost P v hp, hs.1, ?_⟩
  convert hs.2 using 1

end FaithfulKS
