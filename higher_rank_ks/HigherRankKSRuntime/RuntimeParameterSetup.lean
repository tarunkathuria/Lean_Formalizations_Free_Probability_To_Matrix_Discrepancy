import HigherRankKSRuntime.RuntimeInputNormalization
import AugmentedHigherRankKS.RuntimeRankParameter

/-! Rank clamping and dyadic exponent selection by a counted arithmetic loop.
The algorithm computes the SDP exponent alongside q; it never evaluates a
logarithm or relies on an existential choice of an exponent. -/
noncomputable section
namespace HigherRankKSRuntime.RuntimeParameterSetup
open AugmentedHigherRankKS RuntimeParameters HigherRankKS
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
open RuntimeInputNormalization (rankBound rankBound_one rankBound_le rankBound_le_supplied)
set_option maxHeartbeats 800000

/-- The scalar comparison/doubling/squaring loop, with an explicit exponent
counter. Five operations cover the old four-operation update and k←k+1. -/
def run (r : ℕ) : ℕ → RuntimeRankParameter.State → ℕ →
    (RuntimeRankParameter.State × ℕ) × ℕ
  | 0,s,k => ((s,k),0)
  | fuel+1,s,k =>
      if 2*r ≤ s.threshold then ((s,k),1)
      else let next := run r fuel (RuntimeRankParameter.advance s) (k+1)
           (next.1,next.2+5)

theorem run_state (r fuel : ℕ) (s : RuntimeRankParameter.State) (k : ℕ) :
    (run r fuel s k).1.1 = (RuntimeRankParameter.run r fuel s).1 := by
  induction fuel generalizing s k with
  | zero => rfl
  | succ fuel ih =>
      simp only [run,RuntimeRankParameter.run]
      split_ifs
      · rfl
      · exact ih _ _

theorem run_exponent (r fuel : ℕ) (s : RuntimeRankParameter.State) (k : ℕ)
    (hk : 1 ≤ k) (hq : s.q=2^k) :
    1 ≤ (run r fuel s k).1.2 ∧
      (run r fuel s k).1.1.q = 2^(run r fuel s k).1.2 := by
  induction fuel generalizing s k with
  | zero => exact ⟨hk,hq⟩
  | succ fuel ih =>
      simp only [run]
      split_ifs
      · exact ⟨hk,hq⟩
      · exact ih _ _ (by omega) (by
          dsimp only [RuntimeRankParameter.advance]
          rw [hq,pow_succ]
          omega)

theorem run_cost (r fuel : ℕ) (s : RuntimeRankParameter.State) (k : ℕ) :
    (run r fuel s k).2 ≤ 5*fuel := by
  induction fuel generalizing s k with
  | zero => simp [run]
  | succ fuel ih =>
      simp only [run]
      split_ifs
      · dsimp; omega
      · dsimp
        have hh := ih (RuntimeRankParameter.advance s) (k+1)
        omega

/-- Return q and k with q=2^k, using only the clamped rank. Two additional
comparisons account for clamping; constants and field access are charged too. -/
def choose (r d : ℕ) : Counted (ℕ × ℕ) :=
  let bound := rankBound r d
  let out := run bound (4*bound+1) RuntimeRankParameter.initial 1
  ⟨(out.1.1.q,out.1.2),out.2+8⟩

theorem choose_q_eq (r d : ℕ) :
    (choose r d).value.1 = (RuntimeRankParameter.choose (rankBound r d)).1.q := by
  dsimp only [choose,RuntimeRankParameter.choose]
  rw [run_state]

theorem logRank_mono {r s : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s) :
    logRank r ≤ logRank s := by
  unfold logRank
  exact Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (by positivity : 0 < 2*(r:ℝ)) (by exact_mod_cast (show 2*r ≤ 2*s by omega))

/-- The returned exponent is computed, and the rank logarithm occurs only
in the mathematical bound on the returned value. -/
theorem choose_spec {r d : ℕ} (hr : 1 ≤ r) (hd : 1 ≤ d) :
    let q := (choose r d).value.1
    let k := (choose r d).value.2
    1 ≤ k ∧ q=2^k ∧ k ≤ q ∧ 2 ≤ q ∧ q ≤ 4*d ∧
      (q:ℝ) ≤ 2*logRank r ∧
      0 < (1:ℝ)/q ∧ (1:ℝ)/q ≤ 1/2 ∧
      ((rankBound r d):ℝ)^((1:ℝ)/q) ≤ 2 ∧
      (choose r d).cost ≤ 20*d+13 := by
  obtain ⟨hk,hq⟩ := run_exponent (rankBound r d) (4*rankBound r d+1)
    RuntimeRankParameter.initial 1 (by decide) (by decide)
  change 1 ≤ (choose r d).value.2 at hk
  change (choose r d).value.1 = 2^(choose r d).value.2 at hq
  have hs := RuntimeRankParameter.choose_correct (rankBound_one r d)
  rw [←choose_q_eq r d] at hs
  obtain ⟨h2,_,_,hlog,hbound,hpos,hhalf,hrpow,_⟩ := hs
  have hbd := rankBound_le (r:=r) hd
  have hsup := rankBound_le_supplied (d:=d) hr
  refine ⟨hk,hq,?_,h2,by omega,?_,hpos,hhalf,hrpow,?_⟩
  · rw [hq]
    exact (choose r d).value.2.lt_two_pow_self.le
  · exact hlog.trans (mul_le_mul_of_nonneg_left (logRank_mono (rankBound_one r d) hsup) (by norm_num))
  · have hcost := run_cost (rankBound r d) (4*rankBound r d+1)
      RuntimeRankParameter.initial 1
    dsimp only [choose]
    omega

/-- The runtime parameter tuple and the SDP exponent are assembled from
natural dimensions and the computed rank scale. -/
def setup (N d r : ℕ) : Counted (Dimensions × ℕ) :=
  let out := choose r d
  ⟨(⟨N,d,out.value.1⟩,out.value.2),out.cost+5⟩

theorem setup_spec {N d r : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d) (hr : 1 ≤ r) :
    let p := (setup N d r).value.1
    let k := (setup N d r).value.2
    p ∈ Domain ∧ p.N=N ∧ p.D=d ∧ p.q=(2:ℝ)^k ∧ 1≤k ∧
      (k:ℝ)≤p.q ∧ p.q≤4*d ∧ p.q≤2*logRank r ∧
      ((rankBound r d):ℝ)^((1:ℝ)/2^k)≤2 ∧
      (setup N d r).cost≤20*d+18 := by
  obtain ⟨hk,hq,hkq,h2,hqd,hlog,hpos,hhalf,hrpow,hcost⟩ := choose_spec hr hd
  have hqreal : ((choose r d).value.1:ℝ)=(2:ℝ)^((choose r d).value.2) := by exact_mod_cast hq
  dsimp only [setup]
  refine ⟨⟨?_,?_,?_⟩,rfl,rfl,hqreal,hk,?_,?_,hlog,?_,by omega⟩
  · change (1:ℝ) ≤ (N:ℝ)
    exact_mod_cast hN
  · change (1:ℝ) ≤ (d:ℝ)
    exact_mod_cast hd
  · change (1:ℝ) ≤ ((choose r d).value.1:ℝ)
    exact_mod_cast (show 1 ≤ (choose r d).value.1 by omega)
  · exact_mod_cast hkq
  · exact_mod_cast hqd
  · simpa only [hqreal] using hrpow

end HigherRankKSRuntime.RuntimeParameterSetup
