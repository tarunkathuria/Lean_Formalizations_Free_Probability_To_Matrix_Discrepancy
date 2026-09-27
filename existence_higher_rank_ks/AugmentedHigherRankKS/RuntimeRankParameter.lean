import HigherRankKS.Parameters
import AugmentedHigherRankKS.RuntimeParameters

/-! Rank parameter selection by comparisons and repeated squaring. The
code never evaluates a logarithm. Logarithms occur only in its proof. -/
namespace AugmentedHigherRankKS.RuntimeRankParameter
open HigherRankKS
set_option maxHeartbeats 600000

structure State where
  q : ℕ
  threshold : ℕ
  deriving DecidableEq

def initial : State := ⟨2,4⟩
def advance (s : State) : State := ⟨2*s.q,s.threshold*s.threshold⟩

/-- The second component counts scalar arithmetic operations and tests.
Four operations cover a comparison, doubling, squaring, and loop update. -/
def run (r : ℕ) : ℕ → State → State × ℕ
  | 0,s => (s,0)
  | fuel+1,s => if 2*r ≤ s.threshold then (s,1)
    else let next := run r fuel (advance s); (next.1,next.2+4)

def choose (r : ℕ) : State × ℕ := run r (4*r+1) initial

def Invariant (r : ℕ) (s : State) : Prop :=
  2 ≤ s.q ∧ (∃ k : ℕ, s.q = 2^k) ∧ s.threshold = 2^s.q ∧
    (s.q : ℝ) ≤ 2*logRank r

theorem logRank_le_twice {r : ℕ} (hr : 1 ≤ r) : logRank r ≤ 2*r := by
  unfold logRank
  have hpos : 0 < (2*(r:ℝ)) := by exact_mod_cast (show 0 < 2*r by omega)
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hpos).2
  have hh : 2*r ≤ (2:ℕ)^(2*r) := (2*r).lt_two_pow_self.le
  have hcast : (2:ℝ)*r ≤ (2:ℝ)^(2*r) := by exact_mod_cast hh
  rw [show (2:ℝ)*(r:ℝ) = ((2*r:ℕ):ℝ) by norm_cast, Real.rpow_natCast]
  exact_mod_cast hh

theorem invariant_q_bound {r : ℕ} (hr : 1 ≤ r) {s : State}
    (hs : Invariant r s) : s.q ≤ 4*r := by
  have hlog := logRank_le_twice hr
  have hq : (s.q:ℝ) ≤ 4*r := by linarith [hs.2.2.2]
  exact_mod_cast hq

theorem initial_invariant {r : ℕ} (hr : 1 ≤ r) : Invariant r initial := by
  refine ⟨by decide,⟨1,by decide⟩,by decide,?_⟩
  change (2:ℝ) ≤ 2*logRank r
  linarith [one_le_logRank hr]

theorem advance_invariant {r : ℕ} (hr : 1 ≤ r) {s : State}
    (hs : Invariant r s) (hfail : ¬2*r ≤ s.threshold) : Invariant r (advance s) := by
  obtain ⟨hq,⟨k,hk⟩,hth,hup⟩ := hs
  have hbad : (2:ℝ)^(s.q:ℝ) < 2*r := by
    rw [Real.rpow_natCast]
    have hh : (2:ℕ)^s.q < 2*r := by omega
    exact_mod_cast hh
  have hlog : (s.q:ℝ) < logRank r := by
    unfold logRank
    exact (Real.lt_logb_iff_rpow_lt (by norm_num : (1:ℝ)<2)
      (by positivity : 0 < 2*(r:ℝ))).2 hbad
  refine ⟨by dsimp [advance]; omega,⟨k+1,?_⟩,?_,?_⟩
  · dsimp [advance]
    rw [hk,pow_succ]
    omega
  · dsimp [advance]
    rw [hth,show 2*s.q=s.q+s.q by omega,pow_add]
  · dsimp [advance]
    push_cast
    linarith

theorem run_cost (r fuel : ℕ) (s : State) : (run r fuel s).2 ≤ 4*fuel := by
  induction fuel generalizing s with
  | zero => simp [run]
  | succ fuel ih =>
    simp only [run]
    split_ifs with h
    · dsimp; omega
    · dsimp
      have := ih (advance s)
      omega

theorem run_correct {r : ℕ} (hr : 1 ≤ r) (fuel : ℕ) (s : State)
    (hs : Invariant r s) (hf : 4*r < s.q+fuel) :
    Invariant r (run r fuel s).1 ∧ 2*r ≤ (run r fuel s).1.threshold := by
  induction fuel generalizing s with
  | zero =>
    have := invariant_q_bound hr hs
    omega
  | succ fuel ih =>
    simp only [run]
    split_ifs with h
    · exact ⟨hs,h⟩
    · apply ih (advance s) (advance_invariant hr hs h)
      have hq := hs.1
      dsimp [advance]
      omega

theorem choose_correct {r : ℕ} (hr : 1 ≤ r) :
    let q := (choose r).1.q
    2 ≤ q ∧ (∃ k : ℕ, q=2^k) ∧ logRank r ≤ q ∧
      (q:ℝ) ≤ 2*logRank r ∧ q ≤ 4*r ∧
      0 < (1:ℝ)/q ∧ (1:ℝ)/q ≤ 1/2 ∧
      (r:ℝ)^((1:ℝ)/q) ≤ 2 ∧ (choose r).2 ≤ 16*r+4 := by
  obtain ⟨hi,hgood⟩ := run_correct hr (4*r+1) initial (initial_invariant hr)
    (by dsimp [initial]; omega)
  change Invariant r (choose r).1 at hi
  change 2*r ≤ (choose r).1.threshold at hgood
  have hlog : logRank r ≤ ((choose r).1.q:ℝ) := by
    unfold logRank
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2)
      (by positivity : 0 < 2*(r:ℝ))).2
    rw [Real.rpow_natCast]
    rw [hi.2.2.1] at hgood
    exact_mod_cast hgood
  have hbounds := reciprocal_scale_bounds hi.1
  refine ⟨hi.1,hi.2.1,hlog,hi.2.2.2,invariant_q_bound hr hi,
    hbounds.1,hbounds.2,rank_rpow_reciprocal_le_two hr hi.1 hlog,?_⟩
  have hc := run_cost r (4*r+1) initial
  change (choose r).2 ≤ _ at hc
  nlinarith

end AugmentedHigherRankKS.RuntimeRankParameter
