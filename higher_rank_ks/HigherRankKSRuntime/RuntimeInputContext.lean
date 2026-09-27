import HigherRankKSRuntime.RuntimeGlobal
import HigherRankKSRuntime.RuntimeParameterSetup
import HigherRankKS.InputBounds

/-! All internal runtime parameters and their invariants are produced from
the literal matrix input. No local analytic or progress certificate is an
input to this construction. -/
open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace HigherRankKSRuntime.RuntimeInputContext
open AugmentedHigherRankKS RuntimeParameters GlobalEpochs RuntimeGlobal
open RuntimeInputNormalization
variable {N d r : ℕ}
set_option maxHeartbeats 800000

def makeWithFactors (A B : Fin N → SDPValue.Mat d)
    (hB : B=(InputFactors.factors A).value) (hN : 0 < N) (hd : 0 < d) (hr : 1 ≤ r)
    (hA : ∀ i,(A i).PosSemidef) (hs : ∑ i,A i=1)
    (hrank : ∀ i,(A i).rank ≤ r) : Context N d := by
  letI : NeZero d := ⟨hd.ne'⟩
  let p := (RuntimeParameterSetup.setup N d r).value.1
  let k := (RuntimeParameterSetup.setup N d r).value.2
  have hsetup := RuntimeParameterSetup.setup_spec hN hd hr
  refine ⟨A,B,hB,rankBound r d,p,k,(epsilon A).value,hd,hsetup.1,hsetup.2.1,hsetup.2.2.1,
    hsetup.2.2.2.2.1,hsetup.2.2.2.1,hA,hs.le,
    epsilon_nonneg A (fun i => (hA i).isHermitian),epsilon_le_one A hA hs.le,?_,
    norm_le_epsilon A (fun i => (hA i).isHermitian),atom_rank_le_rankBound A hrank,
    hsetup.2.2.2.2.2.2.2.2.1⟩
  rw [hsetup.2.1]
  exact epsilon_lower A hA hs hN

/-- The compatibility constructor specializes to the canonical cached array. -/
def make (A : Fin N → SDPValue.Mat d) (hN : 0 < N) (hd : 0 < d) (hr : 1 ≤ r)
    (hA : ∀ i,(A i).PosSemidef) (hs : ∑ i,A i=1)
    (hrank : ∀ i,(A i).rank ≤ r) : Context N d :=
  makeWithFactors A (InputFactors.factors A).value rfl hN hd hr hA hs hrank

theorem makeWithFactors_eq (A B : Fin N → SDPValue.Mat d)
    (hB : B=(InputFactors.factors A).value) (hN : 0 < N) (hd : 0 < d) (hr : 1 ≤ r)
    (hA : ∀ i,(A i).PosSemidef) (hs : ∑ i,A i=1)
    (hrank : ∀ i,(A i).rank ≤ r) :
    makeWithFactors A B hB hN hd hr hA hs hrank=make A hN hd hr hA hs hrank := by
  subst B
  rfl

theorem make_rank_scale (A : Fin N → SDPValue.Mat d) (hN : 0 < N) (hd : 0 < d)
    (hr : 1 ≤ r) (hA : ∀ i,(A i).PosSemidef) (hs : ∑ i,A i=1)
    (hrank : ∀ i,(A i).rank≤r) :
    (make A hN hd hr hA hs hrank).p.q ≤ 2*HigherRankKS.logRank r :=
  (RuntimeParameterSetup.setup_spec hN hd hr).2.2.2.2.2.2.2.1

theorem make_rank_dimension (A : Fin N → SDPValue.Mat d) (hN : 0 < N) (hd : 0 < d)
    (hr : 1 ≤ r) (hA : ∀ i,(A i).PosSemidef) (hs : ∑ i,A i=1)
    (hrank : ∀ i,(A i).rank≤r) :
    (make A hN hd hr hA hs hrank).p.q ≤ 4*(make A hN hd hr hA hs hrank).p.D := by
  have hh := (RuntimeParameterSetup.setup_spec hN hd hr).2.2.2.2.2.2.1
  exact hh

theorem make_k_bound (A : Fin N → SDPValue.Mat d) (hN : 0 < N) (hd : 0 < d)
    (hr : 1 ≤ r) (hA : ∀ i,(A i).PosSemidef) (hs : ∑ i,A i=1)
    (hrank : ∀ i,(A i).rank≤r) :
    ((make A hN hd hr hA hs hrank).k:ℝ) ≤ (make A hN hd hr hA hs hrank).p.q :=
  (RuntimeParameterSetup.setup_spec hN hd hr).2.2.2.2.2.1

theorem make_epsilon_le (A : Fin N → SDPValue.Mat d) (hN : 0 < N) (hd : 0 < d)
    (hr : 1 ≤ r) (hA : ∀ i,(A i).PosSemidef) (hs : ∑ i,A i=1)
    (hrank : ∀ i,(A i).rank≤r) {ε : ℝ} (hε : 0 ≤ ε) (hb : ∀ i,‖A i‖ ≤ ε) :
    (make A hN hd hr hA hs hrank).ε ≤ ε :=
  epsilon_le A (fun i => (hA i).isHermitian) hε hb

/-- The executed output has the advertised bound in the original supplied
epsilon and rank, even though its parameters use the computed atom norm. -/
theorem execute_discrepancy (O : SDPValue.Solver) (A : Fin N → SDPValue.Mat d)
    (hN : 0 < N) (hd : 0 < d) (hr : 1 ≤ r) (hA : ∀ i,(A i).PosSemidef)
    (hs : ∑ i,A i=1) (hrank : ∀ i,(A i).rank≤r)
    {ε : ℝ} (hε : 0 ≤ ε) (hb : ∀ i,‖A i‖ ≤ ε) (testWork roundWork : ℕ) :
    let c := make A hN hd hr hA hs hrank
    let out := RuntimeGlobal.execute c O testWork roundWork
    (∀ i,out.value.val i=1 ∨ out.value.val i= -1) ∧
    ‖∑ i,out.value.val i • A i‖ ≤ min 1 (10000*Real.sqrt (ε*Real.log (2*(r:ℝ)))) := by
  letI : NeZero d := ⟨hd.ne'⟩
  let c := make A hN hd hr hA hs hrank
  let out := RuntimeGlobal.execute c O testWork roundWork
  have hex := RuntimeGlobal.execute_spec c O testWork roundWork
  refine ⟨hex.1,le_min ?_ ?_⟩
  · exact HigherRankKS.center_norm_le_one A hA hs.le (HigherRankKS.real_signing_mem_cube hex.1)
  · have hlog : 0 ≤ Real.log (2*(r:ℝ)) := by
      apply Real.log_nonneg
      have hr' : (1:ℝ)≤r := by exact_mod_cast hr
      linarith
    have hscale := runtime_log_conversion hr (by linarith [c.domain.2.2])
      (make_rank_scale A hN hd hr hA hs hrank) c.epsilon_nonneg
    have heps := make_epsilon_le A hN hd hr hA hs hrank hε hb
    have hroot := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right heps hlog)
    have hh := hex.2.1.trans hscale
    change ‖∑ i,out.value.val i • A i‖ ≤ _ at hh
    nlinarith [Real.sqrt_nonneg (ε*Real.log (2*(r:ℝ)))]

end HigherRankKSRuntime.RuntimeInputContext
