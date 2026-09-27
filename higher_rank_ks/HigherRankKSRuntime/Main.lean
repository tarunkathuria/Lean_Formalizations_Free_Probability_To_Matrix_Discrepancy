import HigherRankKSRuntime.RuntimeProgram

/-! Public end-to-end higher-rank Kadison--Singer algorithm. The input
assumptions below are the matrix assumptions and the explicitly permitted
finite-SDP solver. EVD is an instruction in the real-arithmetic model.
All local analysis, parameter selection, finite execution, and polynomial
work are discharged in the proof, not supplied to this endpoint. -/
open Matrix MatrixSpencer
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace HigherRankKSRuntime
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
variable {N d r : ℕ}
set_option maxHeartbeats 800000

/-- The zero-dimensional branch writes one constant sign per owner. -/
def trivialSigning (N : ℕ) : Counted (Fin N → ℝ) := ⟨fun _ => 1,2*N+1⟩

/-- The public algorithm. Its proof arguments certify the literal input
conditions; they introduce no additional computational or analytic data. -/
def solve (O : SDPValue.Solver) (A : Fin N → SDPValue.Mat d)
    (hr : 1≤r) (hA : ∀ i,(A i).PosSemidef) (hs : ∑ i,A i=1)
    (hrank : ∀ i,(A i).rank≤r) : Counted (Fin N → ℝ) :=
  let branch := if hd : 0<d then
    if hN : 0<N then RuntimeProgram.positive O A hN hd hr hA hs hrank
    else trivialSigning N
  else trivialSigning N
  ⟨branch.value,branch.cost+2⟩

theorem signedSum_eq (A : Fin N → SDPValue.Mat d) (σ : Fin N → ℝ) :
    HigherRankKS.signedSum A σ=∑ i,σ i • A i := by
  apply Finset.sum_congr rfl
  intro i _
  ext j k
  simp only [Matrix.smul_apply,Complex.real_smul,smul_eq_mul]

/-- One sign per original matrix, with the advertised dimension-free bound. -/
theorem solve_correct (O : SDPValue.Solver) (A : Fin N → SDPValue.Mat d)
    (hr : 1≤r) (hA : ∀ i,(A i).PosSemidef) (hs : ∑ i,A i=1)
    (hrank : ∀ i,(A i).rank≤r) {ε : ℝ} (hε : 0≤ε)
    (hnorm : ∀ i,‖Matrix.toEuclideanCLM (𝕜:=ℂ) (A i)‖≤ε) :
    let out := solve O A hr hA hs hrank
    (∀ i,out.value i=1 ∨ out.value i= -1) ∧
      ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (HigherRankKS.signedSum A out.value)‖ ≤
        min 1 (10000*Real.sqrt (ε*Real.log (2*(r:ℝ)))) := by
  by_cases hd : 0<d
  · letI : NeZero d := ⟨hd.ne'⟩
    have hN : 0<N := by
      by_contra hn
      have hz : N=0 := by omega
      subst N
      simpa using hs
    simp only [solve,dif_pos hd,dif_pos hN]
    have hh := RuntimeProgram.positive_correct O A hN hd hr hA hs hrank hε hnorm
    refine ⟨hh.1,?_⟩
    change ‖HigherRankKS.signedSum A _‖ ≤ _
    rw [signedSum_eq]
    exact hh.2
  · have hd0 : d=0 := by omega
    subst d
    simp only [solve,dif_neg hd]
    refine ⟨fun _ => Or.inl rfl,?_⟩
    have hz : HigherRankKS.signedSum A (trivialSigning N).value=0 := Subsingleton.elim _ _
    rw [hz,map_zero,norm_zero]
    exact le_min zero_le_one (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))

/-- The exponent and coefficient are fixed once the permitted solver is
fixed. Neither depends on epsilon, rank, entries, a successful run, or any
condition number. -/
theorem solve_polynomial (O : SDPValue.Solver) :
    ∃ C : ℝ, ∃ e : ℕ, 0<C ∧ ∀ (N d r : ℕ) (A : Fin N → SDPValue.Mat d)
      (hr : 1≤r) (hA : ∀ i,(A i).PosSemidef) (hs : ∑ i,A i=1)
      (hrank : ∀ i,(A i).rank≤r),
      ((solve O A hr hA hs hrank).cost:ℝ) ≤ C*(1+N+d)^e := by
  obtain ⟨C,e,hC,hp⟩ := RuntimeProgram.positive_polynomial O
  refine ⟨C+3,e+1,by positivity,fun N d r A hr hA hs hrank => ?_⟩
  have hb : (1:ℝ)≤1+N+d := by linarith [Nat.cast_nonneg (α:=ℝ) N,Nat.cast_nonneg (α:=ℝ) d]
  have he : (1+N+d:ℝ)^e≤(1+N+d:ℝ)^(e+1) :=
    pow_le_pow_right₀ hb (by omega)
  have he1 : (1+N+d:ℝ)≤(1+N+d:ℝ)^(e+1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hb (show 1≤e+1 by omega)
  have htriv : ((trivialSigning N).cost+2:ℝ)≤(C+3)*(1+N+d)^ (e+1) := by
    simp only [trivialSigning,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    nlinarith [Nat.cast_nonneg (α:=ℝ) d,pow_nonneg (show 0≤(1+N+d:ℝ) by positivity) (e+1)]
  by_cases hd : 0<d
  · by_cases hN : 0<N
    · simp only [solve,dif_pos hd,dif_pos hN,Nat.cast_add,Nat.cast_ofNat]
      have hpos := hp N d r A hN hd hr hA hs hrank
      have hmajor := mul_le_mul_of_nonneg_left he hC.le
      have hone := one_le_pow₀ hb (n:=e+1)
      nlinarith
    · simpa only [solve,dif_pos hd,dif_neg hN,Nat.cast_add,Nat.cast_ofNat] using htriv
  · simpa only [solve,dif_neg hd,Nat.cast_add,Nat.cast_ofNat] using htriv

/-- Complete theorem: literal input hypotheses imply an executed signing
and a uniform polynomial real-arithmetic work bound. -/
theorem algorithmic (O : SDPValue.Solver) :
    ∃ C : ℝ, ∃ e : ℕ, 0<C ∧
    ∀ (N d r : ℕ) (ε : ℝ) (hr : 1≤r) (hε : 0≤ε)
      (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
      (hA : ∀ i,(A i).PosSemidef) (hsum : ∑ i,A i=1)
      (hnorm : ∀ i,‖Matrix.toEuclideanCLM (𝕜:=ℂ) (A i)‖≤ε)
      (hrank : ∀ i,Matrix.rank (A i)≤r),
      let out := solve O A hr hA hsum hrank
      (∀ i,out.value i=1 ∨ out.value i= -1) ∧
      ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (HigherRankKS.signedSum A out.value)‖≤
        min 1 (10000*Real.sqrt (ε*Real.log (2*(r:ℝ)))) ∧
      (out.cost:ℝ)≤C*(1+N+d)^e := by
  obtain ⟨C,e,hC,hp⟩ := solve_polynomial O
  refine ⟨C,e,hC,fun N d r ε hr hε A hA hsum hnorm hrank => ?_⟩
  have hc := solve_correct O A hr hA hsum hrank hε hnorm
  exact ⟨hc.1,hc.2,hp N d r A hr hA hsum hrank⟩

end HigherRankKSRuntime
