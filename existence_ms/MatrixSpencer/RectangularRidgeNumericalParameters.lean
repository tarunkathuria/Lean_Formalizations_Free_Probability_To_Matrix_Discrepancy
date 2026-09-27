import MatrixSpencer.RectangularRidgeParameters

/-! Explicit numerical scales for the ridged rectangular walk. The inequalities
in this file check the scalar budgets, not a supplied derivative bound. The
separate analytic and execution modules must connect these scales to the actual
potential and walk before a total runtime conclusion can be drawn. -/

noncomputable section
namespace MatrixSpencer.RectangularRidgeNumericalParameters
set_option exponentiation.threshold 2048
set_option maxRecDepth 4096

def big (N : ℝ) (a b : ℕ) : ℝ := 2^a * N^b
def small (N : ℝ) (a b : ℕ) : ℝ := (big N a b)⁻¹

lemma big_pos {N : ℝ} (hN : 0 < N) (a b : ℕ) : 0 < big N a b := by
  unfold big
  positivity

lemma small_pos {N : ℝ} (hN : 0 < N) (a b : ℕ) : 0 < small N a b :=
  inv_pos.mpr (big_pos hN a b)

lemma big_one_le {N : ℝ} (hN : 1 ≤ N) (a b : ℕ) : 1 ≤ big N a b := by
  unfold big
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ hN)

lemma big_mono {N : ℝ} (hN : 1 ≤ N) {a b c d : ℕ} (hac : a ≤ c) (hbd : b ≤ d) :
    big N a b ≤ big N c d := by
  unfold big
  exact mul_le_mul (pow_le_pow_right₀ (by norm_num) hac)
    (pow_le_pow_right₀ hN hbd) (by positivity) (by positivity)

lemma small_mono {N : ℝ} (hN : 1 ≤ N) {a b c d : ℕ} (hac : a ≤ c) (hbd : b ≤ d) :
    small N c d ≤ small N a b := by
  exact inv_anti₀ (big_pos (by linarith) a b) (big_mono hN hac hbd)

lemma big_mul (N : ℝ) (a b c d : ℕ) :
    big N a b * big N c d = big N (a+c) (b+d) := by
  simp only [big, pow_add]
  ring

lemma small_mul (N : ℝ) (a b c d : ℕ) :
    small N a b * small N c d = small N (a+c) (b+d) := by
  simp only [small, ← big_mul, mul_inv_rev]
  ring

lemma big_small_cancel {N : ℝ} (hN : 0 < N) (a b c d : ℕ) :
    big N a b * small N (a+c) (b+d) = small N c d := by
  rw [small, ← big_mul, mul_inv_rev]
  have hn := (big_pos hN a b).ne'
  dsimp only [small]
  field_simp

lemma small_le_one {N : ℝ} (hN : 1 ≤ N) (a b : ℕ) : small N a b ≤ 1 := by
  have h := small_mono hN (show 0 ≤ a by omega) (show 0 ≤ b by omega)
  simpa [small, big] using h

lemma small_le_dyadic {N : ℝ} (hN : 1 ≤ N) (a b : ℕ) :
    small N a b ≤ ((2 : ℝ)^a)⁻¹ := by
  have h := small_mono hN (le_refl a) (show 0 ≤ b by omega)
  simpa [small, big] using h

def densityFloor (N : ℝ) : ℝ := small N 10 6
def fourthCap (N : ℝ) : ℝ := big N 1040 200
def covarianceCap (N : ℝ) : ℝ := big N 300 60
def paidCurvature (N : ℝ) : ℝ := big N 300 60
def paidStep (N : ℝ) : ℝ := small N 320 62
def mesh (N : ℝ) : ℝ := small N 540 104
def phaseResponse (N : ℝ) : ℝ := big N 13 3
def selectedEpochs (N : ℝ) : ℝ := big N 22 4
def prefixUpdates (N : ℝ) : ℝ := big N 1120 213
def ownerGrid (N : ℝ) : ℝ := small N 1140 216
def centerGrid (N : ℝ) : ℝ := small N 1150 216
def derivativeAccuracy (N : ℝ) : ℝ := small N 20 2
def differenceStep (N : ℝ) : ℝ := small N 322 62
def valueAccuracy (N : ℝ) : ℝ := small N 346 64

@[simp] theorem mesh_squared (N : ℝ) : mesh N ^ 2 = small N 1080 208 := by
  simpa only [mesh, pow_two] using small_mul N 540 104 540 104

theorem fourth_mesh_budget {N : ℝ} (hN : 0 < N) :
    fourthCap N * mesh N ^ 2 = small N 40 8 := by
  rw [mesh_squared]
  exact big_small_cancel hN 1040 200 40 8

theorem fourth_mesh_budget_le {N : ℝ} (hN : 1 ≤ N) :
    fourthCap N * mesh N ^ 2 ≤ 1 / (2 : ℝ)^40 := by
  rw [fourth_mesh_budget (by linarith)]
  simpa only [one_div] using small_le_dyadic hN 40 8

theorem paidStep_le_floor {N : ℝ} (hN : 1 ≤ N) : paidStep N ≤ (1/8192 : ℝ)/2 := by
  calc
    paidStep N ≤ small N 14 0 := small_mono hN (by omega) (by omega)
    _ = (1/8192 : ℝ)/2 := by norm_num [small, big]

theorem paidStep_curvature_budget {N : ℝ} (hN : 1 ≤ N) :
    2 * paidCurvature N * paidStep N ≤ 1/N := by
  have he := big_small_cancel (by linarith : 0<N) 300 60 20 2
  change paidCurvature N * paidStep N = small N 20 2 at he
  have hm := small_mono hN (show 1 ≤ 20 by omega) (show 1 ≤ 2 by omega)
  have hn : N ≠ 0 := by linarith
  calc
    2 * paidCurvature N * paidStep N = 2 * small N 20 2 := by rw [mul_assoc, he]
    _ ≤ 2 * small N 1 1 := mul_le_mul_of_nonneg_left hm (by norm_num)
    _ = 1/N := by simp [small, big]; field_simp

theorem mesh_time_budget {N : ℝ} (hN : 1 ≤ N) :
    2 * mesh N ^ 2 * phaseResponse N ≤ 1 := by
  have he := big_small_cancel (by linarith : 0<N) 13 3 1067 205
  have hb := small_mono hN (show 1 ≤ 1067 by omega) (show 0 ≤ 205 by omega)
  rw [mesh_squared]
  calc
    2 * small N 1080 208 * phaseResponse N = 2 * small N 1067 205 := by
      unfold phaseResponse
      nlinarith [he]
    _ ≤ 2 * small N 1 0 := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ ≤ 1 := by norm_num [small, big]

theorem mesh_time_le {N B : ℝ} (hN : 1 ≤ N) (hB : 0 < B)
    (hcap : B ≤ phaseResponse N) : mesh N ^ 2 ≤ B⁻¹/2 := by
  have h := mesh_time_budget hN
  have hm := mul_le_mul_of_nonneg_left hcap (by positivity : 0 ≤ 2*mesh N^2)
  apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  rw [inv_eq_one_div]
  apply (le_div_iff₀ hB).mpr
  nlinarith

theorem differenceStep_le_floor {N : ℝ} (hN : 1 ≤ N) :
    differenceStep N ≤ (1/8192 : ℝ)/8 := by
  calc
    differenceStep N ≤ small N 16 0 := small_mono hN (by omega) (by omega)
    _ = (1/8192 : ℝ)/8 := by norm_num [small, big]

theorem differenceStep_accuracy (N : ℝ) :
    differenceStep N = derivativeAccuracy N / (4*covarianceCap N) := by
  unfold differenceStep derivativeAccuracy covarianceCap small big
  simp only [mul_inv_rev]
  norm_num
  ring

theorem valueAccuracy_eq (N : ℝ) :
    valueAccuracy N = derivativeAccuracy N * differenceStep N / 16 := by
  unfold valueAccuracy derivativeAccuracy differenceStep
  rw [small_mul]
  simp only [small, big]
  ring

theorem ownerGrid_accumulation {N m : ℝ} (hN : 1 ≤ N) (hm : m ≤ N) :
    2*m*prefixUpdates N*ownerGrid N ≤ 1/4096 := by
  have he := big_small_cancel (by linarith : 0<N) 1120 213 20 3
  change prefixUpdates N * ownerGrid N = small N 20 3 at he
  have hc := big_small_cancel (by linarith : 0<N) 0 1 20 2
  simp only [big, pow_zero, one_mul, pow_one, zero_add] at hc
  have hb := small_le_dyadic hN 20 2
  calc
    2*m*prefixUpdates N*ownerGrid N = 2*m*small N 20 3 := by rw [mul_assoc, mul_assoc, he]; ring
    _ ≤ 2*N*small N 20 3 := by gcongr; exact (small_pos (by linarith) 20 3).le
    _ = 2*small N 20 2 := by rw [mul_assoc, hc]
    _ ≤ 2*((2:ℝ)^20)⁻¹ := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ ≤ 1/4096 := by norm_num

theorem centerGrid_accumulation {N m : ℝ} (hN : 1 ≤ N) (hm : m ≤ N) :
    10*m*prefixUpdates N*centerGrid N ≤ 1/10000 := by
  have he := big_small_cancel (by linarith : 0<N) 1120 213 30 3
  change prefixUpdates N * centerGrid N = small N 30 3 at he
  have hc := big_small_cancel (by linarith : 0<N) 0 1 30 2
  simp only [big, pow_zero, one_mul, pow_one, zero_add] at hc
  have hb := small_le_dyadic hN 30 2
  calc
    10*m*prefixUpdates N*centerGrid N = 10*m*small N 30 3 := by rw [mul_assoc, mul_assoc, he]; ring
    _ ≤ 10*N*small N 30 3 := by gcongr; exact (small_pos (by linarith) 30 3).le
    _ = 10*small N 30 2 := by rw [mul_assoc, hc]
    _ ≤ 10*((2:ℝ)^30)⁻¹ := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ ≤ 1/10000 := by norm_num

theorem ownerGrid_le_floor {N : ℝ} (hN : 1 ≤ N) :
    ownerGrid N ≤ (1/8192 : ℝ)/100 := by
  calc
    ownerGrid N ≤ small N 20 0 := small_mono hN (by omega) (by omega)
    _ ≤ (1/8192 : ℝ)/100 := by norm_num [small, big]

theorem centerGrid_progress {N m : ℝ} (hN : 1 ≤ N) (hm : m ≤ N) :
    3*m*centerGrid N ≤ (1/8 : ℝ)*mesh N^2/100 := by
  have he := big_small_cancel (by linarith : 0<N) 0 1 1150 215
  simp only [big, pow_zero, one_mul, pow_one, zero_add] at he
  have hp := small_mono hN (show 1080+12 ≤ 1150 by omega) (show 208 ≤ 215 by omega)
  have hc : small N (1080+12) 208 = small N 1080 208 / 4096 := by
    simpa only [Nat.add_zero, show small N 12 0 = 1/4096 by norm_num [small, big],
      div_eq_mul_inv, one_div, one_mul] using (small_mul N 1080 208 12 0).symm
  have hs := (small_pos (by linarith : 0<N) 1080 208).le
  calc
    3*m*centerGrid N ≤ 3*N*centerGrid N := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by norm_num))
        (small_pos (by linarith) 1150 216).le
    _ = 3*small N 1150 215 := by unfold centerGrid; rw [mul_assoc, he]
    _ ≤ 3*small N (1080+12) 208 := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = 3*small N 1080 208/4096 := by rw [hc]; ring
    _ ≤ (1/8:ℝ)*mesh N^2/100 := by rw [mesh_squared]; linarith

theorem all_inverse_scales (N : ℝ) :
    (densityFloor N)⁻¹ = big N 10 6 ∧
    (paidStep N)⁻¹ = big N 320 62 ∧
    (mesh N)⁻¹ = big N 540 104 ∧
    (ownerGrid N)⁻¹ = big N 1140 216 ∧
    (centerGrid N)⁻¹ = big N 1150 216 ∧
    (derivativeAccuracy N)⁻¹ = big N 20 2 ∧
    (differenceStep N)⁻¹ = big N 322 62 ∧
    (valueAccuracy N)⁻¹ = big N 346 64 := by
  simp [densityFloor, paidStep, mesh, ownerGrid, centerGrid, derivativeAccuracy,
    differenceStep, valueAccuracy, small]

theorem densityFloor_le_primitive {m D : ℝ} (hm : 1 ≤ m) (hD : 1 ≤ D) :
    densityFloor (m+D+2) ≤ RectangularRidgeParameters.densityFloor D m := by
  let N := m+D+2
  have hN : 4 ≤ N := by dsimp [N]; linarith
  have hN0 : 0<N := by linarith
  have hQ : 0 < D+m+1 := by linarith
  have hQN : D+m+1 ≤ N := by dsimp [N]; linarith
  have hp := pow_le_pow_left₀ hQ.le hQN 4
  have hs : 10000 ≤ 1024*N^2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hs (pow_nonneg hN0.le 4)
  have hden : 10000*(D+m+1)^4 ≤ 1024*N^6 := by
    nlinarith [show N^2*N^4=N^6 by ring]
  change (2^10*N^6)⁻¹ ≤ 1/(10000*RectangularRidgeParameters.size D m^4)
  norm_num only [show (2:ℝ)^10=1024 by norm_num]
  rw [inv_eq_one_div]
  exact one_div_le_one_div_of_le (by dsimp [RectangularRidgeParameters.size]; positivity) hden

end MatrixSpencer.RectangularRidgeNumericalParameters
