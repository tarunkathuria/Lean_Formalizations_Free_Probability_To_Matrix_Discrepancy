import HigherRankKSRuntime.RuntimeSDPEncoding
import AugmentedHigherRankKS.RuntimeParameters

/-! Uniform polynomial bounds for the explicit SDP sizes and the solver
calls at the algorithm's actual accuracy. -/
namespace HigherRankKSRuntime.SDPValue
open AugmentedHigherRankKS.RuntimeParameters

theorem variableCount_le (N d k : ℕ) :
    variableCount N d k ≤ 100*(N+d+k+1)^4 := by
  let b := N+d+k+1
  have hN : N ≤ b := by dsimp [b]; omega
  have hd : d ≤ b := by dsimp [b]; omega
  have hk : k+1 ≤ b := by dsimp [b]; omega
  have hb : 1 ≤ b := by dsimp [b]; omega
  have h2 : b^2 ≤ b^4 := Nat.pow_le_pow_right hb (by omega)
  have hprod : N*(k+1)*d^2 ≤ b*b*b^2 := by gcongr
  have hsq : (4*d)^2 ≤ (4*b)^2 := by gcongr
  dsimp [variableCount]
  change _ ≤ 100*b^4
  nlinarith

theorem pencilOrder_le (N d k : ℕ) :
    pencilOrder N d k ≤ 60*(N+d+k+1)^3 := by
  let b := N+d+k+1
  have hN : N ≤ b := by dsimp [b]; omega
  have hd : d ≤ b := by dsimp [b]; omega
  have hk : k+1 ≤ b := by dsimp [b]; omega
  have hb : 1 ≤ b := by dsimp [b]; omega
  have hb3 : b ≤ b^3 := by simpa using Nat.pow_le_pow_right hb (show 1≤3 by omega)
  have hone3 : 1 ≤ b^3 := Nat.one_le_pow 3 b hb
  have hprod : 2*N*(3*k+1)*d ≤ 2*b*(3*b)*b := by gcongr <;> omega
  have hprod2 : 4*N*d^2 ≤ 4*b*b^2 := by gcongr
  dsimp [pencilOrder]
  change _ ≤ 60*b^3
  nlinarith

theorem dataSize_le (N d k : ℕ) :
    dataSize N d k ≤ 400000*(N+d+k+1)^10 := by
  let b := N+d+k+1
  have hb : 1 ≤ b := by dsimp [b]; omega
  have hv := variableCount_le N d k
  have hp := pencilOrder_le N d k
  change variableCount N d k ≤ 100*b^4 at hv
  change pencilOrder N d k ≤ 60*b^3 at hp
  have hone4 : 1 ≤ b^4 := Nat.one_le_pow 4 b hb
  have h4 : b^4 ≤ b^10 := Nat.pow_le_pow_right hb (by omega)
  have hprod : (variableCount N d k+1)*(pencilOrder N d k)^2 ≤
      (101*b^4)*(60*b^3)^2 := by gcongr <;> omega
  have he : (101*b^4)*(60*b^3)^2 = 363600*b^10 := by ring
  rw [he] at hprod
  dsimp [dataSize]
  change _ ≤ 400000*b^10
  omega

noncomputable def solverMajorant (O : Solver) (z : Dimensions) : ℝ :=
  (O.coefficient+1)*(400000*size z^10+(accuracy z)⁻¹+2)^O.degree

theorem solverMajorant_poly (O : Solver) : Poly (solverMajorant O) := by
  apply Controlled.mul
  · exact controlled_const (by positivity : (0:ℝ)<O.coefficient+1)
  · apply Controlled.pow
    apply Controlled.add size_one
    · apply Controlled.add size_one
      · exact (controlled_const (by norm_num : (0:ℝ)<400000)).mul (size_poly.pow 10)
      · exact accuracy_poly.inv
    · exact controlled_const (by norm_num : (0:ℝ)<2)

theorem report_cost_le_majorant (O : Solver) {N d k : ℕ}
    (P : Program N d) (z : Dimensions) (hz : z ∈ Domain)
    (hN : (N:ℝ) = z.N) (hd : (d:ℝ) = z.D) (hk : (k:ℝ) ≤ z.q) :
    ((O.report (k:=k) P (accuracy z)).cost:ℝ) ≤ solverMajorant O z := by
  have hν := accuracy_poly.positive z hz
  have hw := O.work_bound (k:=k) P (accuracy z) hν
  have hw' : ((O.report (k:=k) P (accuracy z)).cost:ℝ) ≤
      O.coefficient*((dataSize N d k:ℝ)+(⌈(accuracy z)⁻¹⌉₊:ℝ)+1)^O.degree := by
    exact_mod_cast hw
  have hdata : (dataSize N d k:ℝ) ≤ 400000*(N+d+k+1:ℝ)^10 := by
    exact_mod_cast dataSize_le N d k
  have hbase : (N+d+k+1:ℝ) ≤ size z := by dsimp [size]; rw [hN,hd]; linarith
  have hdata' : (dataSize N d k:ℝ) ≤ 400000*size z^10 := by
    exact hdata.trans (by gcongr)
  have hceil : (⌈(accuracy z)⁻¹⌉₊:ℝ) ≤ (accuracy z)⁻¹+1 :=
    (Nat.ceil_lt_add_one (inv_nonneg.mpr hν.le)).le
  apply hw'.trans
  unfold solverMajorant
  have hh : (dataSize N d k:ℝ)+(⌈(accuracy z)⁻¹⌉₊:ℝ)+1 ≤
      400000*size z^10+(accuracy z)⁻¹+2 := by linarith
  apply mul_le_mul (by linarith) (pow_le_pow_left₀ (by positivity) hh _)
    (by positivity) (by positivity)

/-- A fixed polynomial in the dimensions bounds every value query. Its
degree may depend on the permitted solver, never on the input or rank. -/
theorem solver_uniform_polynomial (O : Solver) :
    ∃ C : ℝ, ∃ p : ℕ, 0 < C ∧ ∀ (N d k : ℕ) (P : Program N d)
      (z : Dimensions), z ∈ Domain → (N:ℝ)=z.N → (d:ℝ)=z.D →
      (k:ℝ)≤z.q → z.q≤4*z.D →
      ((O.report (k:=k) P (accuracy z)).cost:ℝ) ≤ C*(1+N+d)^p := by
  obtain ⟨C,p,hC,hp⟩ := (solverMajorant_poly O).input_polynomial
  refine ⟨C,p,hC,fun N d k P z hz hN hd hk hq => ?_⟩
  have hh := (report_cost_le_majorant O P z hz hN hd hk).trans ((hp z hz hq).1)
  simpa only [← hN,← hd] using hh

end HigherRankKSRuntime.SDPValue
