import HigherRankKSRuntime.RuntimeSolverWork
import HigherRankKSRuntime.RuntimeStateReport
import HigherRankKSRuntime.RuntimeInputNormalization
import HigherRankKSRuntime.NextEventCost

/-! A fixed polynomial envelope for the actual finite controller. Ceilings,
all scalar report construction, and a linear number of reserve epochs are
included. The solver's coefficient and degree are fixed independently of
input, rank, and requested accuracy. -/
noncomputable section
namespace HigherRankKSRuntime.RuntimeWork
open AugmentedHigherRankKS AugmentedHigherRankKS.RuntimeParameters
open MatrixSpencer.RealRAM.JacobiIteration (Counted)

/-- Uniform cost of a cached report, including its scalar center assembly. -/
def reportBudget (O : SDPValue.Solver) (N d k : ℕ) (p : Dimensions) : ℕ :=
  O.coefficient*(SDPValue.dataSize N d k+⌈(accuracy p)⁻¹⌉₊+1)^O.degree+
    1004*(N+1)*(d+1)^2

def fuel (p : Dimensions) : ℕ := ⌈eventBound p⌉₊+1

/-- This allowance covers the fixed-degree preprocessing, reset, live-mass
norm evaluation and final rounding work separately from controller events. -/
def scalarWork (N d k : ℕ) : ℕ := 100000*(N+d+k+1)^6

def totalWork (O : SDPValue.Solver) (N d k : ℕ) (p : Dimensions) : ℕ :=
  2*scalarWork N d k+N*(fuel p*NextEvent.eventWork N (reportBudget O N d k p)+3*scalarWork N d k)

def reportMajorant (O : SDPValue.Solver) (p : Dimensions) : ℝ :=
  SDPValue.solverMajorant O p+1004*size p^3

def totalMajorant (O : SDPValue.Solver) (p : Dimensions) : ℝ :=
  1000000*size p^10*((eventBound p+2)*(reportMajorant O p+1)+1)

private theorem pc (c : ℝ) (hc : 0<c) : Poly (fun _ => c) := controlled_const hc
private theorem pa {f g : Dimensions → ℝ} (hf : Poly f) (hg : Poly g) :
    Poly (fun p => f p+g p) := Controlled.add size_one hf hg

theorem reportMajorant_poly (O : SDPValue.Solver) : Poly (reportMajorant O) :=
  pa (SDPValue.solverMajorant_poly O) ((pc 1004 (by norm_num)).mul (size_poly.pow 3))

theorem totalMajorant_poly (O : SDPValue.Solver) : Poly (totalMajorant O) :=
  ((pc 1000000 (by norm_num)).mul (size_poly.pow 10)).mul
    (pa ((pa eventBound_poly (pc 2 (by norm_num))).mul
      (pa (reportMajorant_poly O) (pc 1 (by norm_num)))) (pc 1 (by norm_num)))

theorem report_cost (O : SDPValue.Solver) {N d : ℕ}
    (A B : Fin N → SDPValue.Mat d) (k : ℕ) (x₀ : Fin N → ℝ)
    (p : Dimensions) (hp : p ∈ Domain) (z : EpochState (Fin N)) :
    (RuntimeStateReport.report O A B k x₀ (theta p) (accuracy p) z).cost ≤ reportBudget O N d k p :=
  RuntimeStateReport.report_cost O A B k x₀ (theta p) (accuracy_poly.positive p hp) z

theorem next_cost (O : SDPValue.Solver) {N d : ℕ}
    (A B : Fin N → SDPValue.Mat d) (k : ℕ) (x₀ : Fin N → ℝ)
    (p : Dimensions) (hp : p ∈ Domain) (z : EpochState (Fin N)) :
    (NextEvent.compute (RuntimeStateReport.report O A B k x₀ (theta p) (accuracy p))
      (a p) (prep p) (walk p) (stencil p) (p0 p) (rho p) (zeta p) z).cost ≤
      NextEvent.eventWork N (reportBudget O N d k p) :=
  NextEvent.compute_work _ _ _ _ _ _ _ _ z (fun y => report_cost O A B k x₀ p hp y)

/-- The ceiling used for finite fuel costs at most two more than its real
analytic bound. -/
theorem fuel_le (p : Dimensions) (hp : p ∈ Domain) : (fuel p : ℝ)≤eventBound p+2 := by
  have hh := (Nat.ceil_lt_add_one (eventBound_poly.positive p hp).le).le
  simp only [fuel,Nat.cast_add,Nat.cast_one]
  linarith

/-- The explicit event-work expression has fixed degree in owner count. -/
theorem eventWork_le (N Q : ℕ) :
    (NextEvent.eventWork N Q : ℝ) ≤ 10000*(N+1:ℝ)^5*(Q+1) := by
  have h : 0 ≤ 10000*(N+1:ℝ)^5*(Q+1)-(NextEvent.eventWork N Q : ℝ) := by
    simp only [NextEvent.eventWork,NextEvent.walkWork,NextEvent.queryWork,
      Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
    ring_nf
    positivity
  linarith

theorem dimensions_le_size {N d k : ℕ} (p : Dimensions) (hp : p ∈ Domain)
    (hN : (N:ℝ)=p.N) (hd : (d:ℝ)=p.D) (hk : (k:ℝ)≤p.q) :
    (N+d+k+1:ℝ)≤size p ∧ (N+1:ℝ)≤size p ∧ (d+1:ℝ)≤size p ∧ (N:ℝ)≤size p := by
  rcases hp with ⟨hpN,hpd,hpq⟩
  dsimp [size]
  rw [hN,hd]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem solver_budget_le (O : SDPValue.Solver) {N d k : ℕ}
    (p : Dimensions) (hp : p ∈ Domain)
    (hN : (N:ℝ)=p.N) (hd : (d:ℝ)=p.D) (hk : (k:ℝ)≤p.q) :
    (O.coefficient*(SDPValue.dataSize N d k+⌈(accuracy p)⁻¹⌉₊+1)^O.degree : ℝ) ≤
      SDPValue.solverMajorant O p := by
  have hν := accuracy_poly.positive p hp
  have hdata : (SDPValue.dataSize N d k:ℝ)≤400000*(N+d+k+1:ℝ)^10 := by
    exact_mod_cast SDPValue.dataSize_le N d k
  have hs := (dimensions_le_size p hp hN hd hk).1
  have hdata' : (SDPValue.dataSize N d k:ℝ)≤400000*size p^10 := hdata.trans (by gcongr)
  have hceil : (⌈(accuracy p)⁻¹⌉₊:ℝ)≤(accuracy p)⁻¹+1 :=
    (Nat.ceil_lt_add_one (inv_nonneg.mpr hν.le)).le
  have hb : (SDPValue.dataSize N d k:ℝ)+(⌈(accuracy p)⁻¹⌉₊:ℝ)+1 ≤
      400000*size p^10+(accuracy p)⁻¹+2 := by linarith
  unfold SDPValue.solverMajorant
  exact mul_le_mul (by linarith : (O.coefficient:ℝ)≤O.coefficient+1)
    (pow_le_pow_left₀ (by positivity) hb O.degree) (by positivity) (by positivity)

theorem reportBudget_le (O : SDPValue.Solver) {N d k : ℕ}
    (p : Dimensions) (hp : p ∈ Domain)
    (hN : (N:ℝ)=p.N) (hd : (d:ℝ)=p.D) (hk : (k:ℝ)≤p.q) :
    (reportBudget O N d k p:ℝ)≤reportMajorant O p := by
  have hs := dimensions_le_size p hp hN hd hk
  have hscalar : 1004*(N+1:ℝ)*(d+1:ℝ)^2 ≤ 1004*size p^3 := by
    calc _ ≤ 1004*size p*(size p)^2 := by gcongr <;> linarith [size_one p hp]
         _ = _ := by ring
  have hh := add_le_add (solver_budget_le O p hp hN hd hk) hscalar
  simpa only [reportBudget,reportMajorant,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] using hh

theorem scalarWork_le {N d k : ℕ} (p : Dimensions) (hp : p ∈ Domain)
    (hN : (N:ℝ)=p.N) (hd : (d:ℝ)=p.D) (hk : (k:ℝ)≤p.q) :
    (scalarWork N d k:ℝ)≤100000*size p^6 := by
  have hs := (dimensions_le_size p hp hN hd hk).1
  simp only [scalarWork,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
  gcongr

theorem totalWork_le (O : SDPValue.Solver) {N d k : ℕ}
    (p : Dimensions) (hp : p ∈ Domain)
    (hN : (N:ℝ)=p.N) (hd : (d:ℝ)=p.D) (hk : (k:ℝ)≤p.q) :
    (totalWork O N d k p:ℝ)≤totalMajorant O p := by
  have hs := dimensions_le_size p hp hN hd hk
  have hR := reportBudget_le O p hp hN hd hk
  have hsize := size_one p hp
  have hsize0 : 0 ≤ size p := by linarith
  have hsN := hs.2.2.2
  have hsNp := hs.2.1
  have hE : (NextEvent.eventWork N (reportBudget O N d k p):ℝ) ≤
      10000*size p^5*(reportMajorant O p+1) :=
    (eventWork_le N _).trans (by gcongr)
  have hF := fuel_le p hp
  have hS := scalarWork_le p hp hN hd hk
  have hfp := eventBound_poly.positive p hp
  have hRp := (reportMajorant_poly O).positive p hp
  have h5 : size p^5 ≤ size p^9 := pow_le_pow_right₀ hsize (by omega)
  have h6 : size p^6 ≤ size p^9 := pow_le_pow_right₀ hsize (by omega)
  have h9 : size p^9 ≤ size p^10 := pow_le_pow_right₀ hsize (by omega)
  have hwork : (totalWork O N d k p:ℝ) ≤
      2*(100000*size p^6)+size p*((eventBound p+2)*(10000*size p^5*(reportMajorant O p+1))+3*(100000*size p^6)) := by
    simp only [totalWork,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    gcongr
  apply hwork.trans
  unfold totalMajorant
  have hterm : size p*(eventBound p+2)*(10000*size p^5*(reportMajorant O p+1)) ≤
      10000*size p^10*((eventBound p+2)*(reportMajorant O p+1)) := by
    calc _ = 10000*size p^6*((eventBound p+2)*(reportMajorant O p+1)) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right
           (mul_le_mul_of_nonneg_left (h6.trans h9) (by norm_num)) (by positivity)
  have hterm2 : size p*(3*(100000*size p^6)) ≤300000*size p^10 := by
    calc _ = 300000*size p^7 := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left
           (pow_le_pow_right₀ hsize (show 7≤10 by omega)) (by norm_num)
  have hterm3 : 2*(100000*size p^6) ≤200000*size p^10 := by
    have hh := mul_le_mul_of_nonneg_left (h6.trans h9) (by norm_num : (0:ℝ)≤200000)
    nlinarith
  have hn : 0 ≤ size p^10*((eventBound p+2)*(reportMajorant O p+1)) := by positivity
  nlinarith

/-- The actual EVD factorization, maximum norm and discarded-owner scan
all fit the fixed-degree scalar preprocessing allowance. -/
theorem preprocessing_cost {N d : ℕ} (A : Fin N → SDPValue.Mat d) (η : ℝ) (k : ℕ) :
    (InputFactors.factors A).cost+(RuntimeInputNormalization.epsilon A).cost+
      (RuntimeInputNormalization.discard A η).cost ≤ scalarWork N d k := by
  let b := N+d+k+1
  have hb : 1≤b := by dsimp [b]; omega
  have hNb : N+1≤b := by dsimp [b]; omega
  have hdb : d+1≤b := by dsimp [b]; omega
  have hprod : (N+1)*(d+1)^3≤b^4 := by
    calc _ ≤ b*b^3 := by gcongr
         _ = _ := by ring
  have hprod1 : 1≤(N+1)*(d+1)^3 := Nat.mul_pos (by omega) (pow_pos (by omega) 3)
  have hNprod : N*(d+1)^3≤(N+1)*(d+1)^3 := by gcongr; omega
  have hfactor := InputFactors.factors_cost A
  have heps := RuntimeInputNormalization.epsilon_cost A
  have hdiscard := RuntimeInputNormalization.discard_cost A η
  have hsum : (InputFactors.factors A).cost+(RuntimeInputNormalization.epsilon A).cost+
      (RuntimeInputNormalization.discard A η).cost ≤ 12221*((N+1)*(d+1)^3) := by nlinarith
  have hpow : b^4≤b^6 := Nat.pow_le_pow_right hb (by omega)
  exact hsum.trans ((Nat.mul_le_mul_left 12221 hprod).trans (by dsimp [scalarWork]; change _≤100000*b^6; nlinarith))

theorem reset_cost_le (N d k : ℕ) : 10*N+1≤scalarWork N d k := by
  have hb : 1≤N+d+k+1 := by omega
  have hN : N+1≤N+d+k+1 := by omega
  have hp : N+d+k+1≤(N+d+k+1)^6 := Nat.le_self_pow (by omega) _
  unfold scalarWork
  omega

/-- The total counted-work allowance is bounded by one polynomial in the
original owner count and physical dimension. -/
theorem uniform_polynomial (O : SDPValue.Solver) :
    ∃ C : ℝ, ∃ e : ℕ, 0<C ∧ ∀ (N d k : ℕ) (p : Dimensions),
      p∈Domain → (N:ℝ)=p.N → (d:ℝ)=p.D → (k:ℝ)≤p.q → p.q≤4*p.D →
      (totalWork O N d k p:ℝ)≤C*(1+N+d)^e := by
  obtain ⟨C,e,hC,hb⟩ := (totalMajorant_poly O).input_polynomial
  refine ⟨C,e,hC,fun N d k p hp hN hd hk hq => ?_⟩
  have hh := (totalWork_le O p hp hN hd hk).trans ((hb p hp hq).1)
  simpa only [←hN,←hd] using hh

end HigherRankKSRuntime.RuntimeWork
