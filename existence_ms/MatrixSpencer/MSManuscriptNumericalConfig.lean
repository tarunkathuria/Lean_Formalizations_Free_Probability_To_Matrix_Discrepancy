import MatrixSpencer.MSManuscriptNumericalEpochRun

/-! Primitive square-epoch numerical constants and scalar probability budgets.
The supplied EpochConfig contains only original Hermitian contractions,
starting cube data and the explicit margin bound. All preparation and
movement parameters of the numerical run are fixed here. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptNumericalConfig
open MSManuscriptNumericalEpochRun
variable {N d : ℕ}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}

/-- The actual coefficients use regularizer1, floor1/8192 and cap4096/√N. -/
def ofEpochConfig (cfg : EpochConfig (Fin N) (Fin d)) (hd : 0 < d) : Config N d where
  offset := cfg.offset
  atoms := cfg.matrices
  hermitian := cfg.hermitian
  contractions := cfg.contractions
  regularizer := 1
  floor := 1/8192
  threshold := 4096/Real.sqrt (N:ℝ)
  margin := cfg.epsilon
  driftError := 1/10000
  regularizer_pos := by norm_num
  floor_pos := by norm_num
  floor_le_one := by norm_num
  threshold_pos := by
    have hn : 32≤N := by simpa only [Fintype.card_fin] using cfg.count_large
    exact div_pos (by norm_num) (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega)))
  margin_pos := cfg.epsilon_pos
  driftError_pos := by norm_num
  dimension_pos := hd
  count_large := by simpa only [Fintype.card_fin] using cfg.count_large
  start := cfg.start
  start_regular := cfg.start_regular

theorem count_pos (cfg : EpochConfig (Fin N) (Fin d)) : 0<N := by
  have hn : 32≤N := by simpa only [Fintype.card_fin] using cfg.count_large
  omega

theorem sqrt_count_ge_one (cfg : EpochConfig (Fin N) (Fin d)) : 1≤Real.sqrt (N:ℝ) := by
  have hn : (1:ℝ)≤N := by exact_mod_cast count_pos cfg
  simpa using Real.sqrt_le_sqrt hn

theorem margin_budget (cfg : EpochConfig (Fin N) (Fin d)) (hd : 0<d) :
    (N:ℝ)*(ofEpochConfig cfg hd).margin≤1/1000 := by
  simpa only [Fintype.card_fin] using cfg.epsilon_small

theorem response_exact (cfg : EpochConfig (Fin N) (Fin d)) (hd : 0<d)
    (s : MSManuscriptNumericalEpochLedger.State N) :
    MSManuscriptPreparedResponse.responseCap (params (ofEpochConfig cfg hd) s)=770*Real.sqrt (N:ℝ) := by
  have he := MSManuscriptPreparedResponse.responseCap_of_threshold
    (params (ofEpochConfig cfg hd) s) (L := 4096) (count_pos cfg) rfl
  rw [he]
  change (2+12*Real.sqrt (4096:ℝ)/1)*Real.sqrt (N:ℝ)=770*Real.sqrt (N:ℝ)
  norm_num

/-- The actual input-scale moment allowance used in the numerical acceptance proof. -/
theorem joint_budget (cfg : EpochConfig (Fin N) (Fin d)) (hd : 0<d)
    (s : MSManuscriptNumericalEpochLedger.State N) :
    2*Real.sqrt (N:ℝ)+
      (MSManuscriptPreparedResponse.responseCap (params (ofEpochConfig cfg hd) s)+
        (ofEpochConfig cfg hd).driftError)*MSManuscriptNumericalEpochLedger.timeLimit+
      2*(ofEpochConfig cfg hd).margin*N ≤ (151/50:ℝ)*Real.sqrt (N:ℝ) := by
  rw [response_exact]
  have hm := margin_budget cfg hd
  have hs := sqrt_count_ge_one cfg
  change 2*Real.sqrt (N:ℝ)+(770*Real.sqrt (N:ℝ)+1/10000)*(1/1539)+
    2*cfg.epsilon*N≤(151/50:ℝ)*Real.sqrt (N:ℝ)
  change (N:ℝ)*cfg.epsilon≤1/1000 at hm
  nlinarith

theorem dust_budget (cfg : EpochConfig (Fin N) (Fin d)) (hd : 0<d) :
    4*(ofEpochConfig cfg hd).floor*N≤(N:ℝ)/1024 := by
  change 4*(1/8192:ℝ)*N≤(N:ℝ)/1024
  have hn : (0:ℝ)≤N := Nat.cast_nonneg _
  nlinarith

theorem tangent_budget : (N:ℝ)*MSManuscriptNumericalEpochLedger.timeLimit≤N := by
  have hn : (0:ℝ)≤N := Nat.cast_nonneg _
  norm_num only [MSManuscriptNumericalEpochLedger.timeLimit]
  nlinarith

theorem rounding_budget (cfg : EpochConfig (Fin N) (Fin d)) (hd : 0<d) :
    (ofEpochConfig cfg hd).margin*N≤Real.sqrt (N:ℝ)/100 := by
  have hm := margin_budget cfg hd
  have hs := sqrt_count_ge_one cfg
  change cfg.epsilon*N≤Real.sqrt (N:ℝ)/100
  change (N:ℝ)*cfg.epsilon≤1/1000 at hm
  nlinarith

end MatrixSpencer.MSManuscriptNumericalConfig
