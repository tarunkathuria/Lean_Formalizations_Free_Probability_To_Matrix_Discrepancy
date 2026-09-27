import MatrixSpencer.KSFullManuscriptWalkBudget
import MatrixSpencer.KSEighthManuscriptBudgets



noncomputable section
namespace MatrixSpencer.KSManuscriptPolynomialParameters

private theorem inverse_square_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx hxy 2

theorem inv_min_sq_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (min a b ^ 2)⁻¹ ≤ (a ^ 2)⁻¹ + (b ^ 2)⁻¹ := by
  by_cases h : a ≤ b
  · rw [min_eq_left h]
    exact le_add_of_nonneg_right (by positivity)
  · rw [min_eq_right (le_of_not_ge h)]
    exact le_add_of_nonneg_left (by positivity)

theorem full_curvature_inv_le {N : ℕ} (hN : 0 < N) {δ : ℝ}
    (hδ : 0 < δ) (hi : δ⁻¹ ≤ N) :
    (KSFullManuscriptParameters.curvatureTolerance N δ)⁻¹ ≤ 100 * (N : ℝ)^2 := by
  have he : (KSFullManuscriptParameters.curvatureTolerance N δ)⁻¹ =
      100*(N : ℝ)*δ⁻¹ := by simp [KSFullManuscriptParameters.curvatureTolerance]; ring
  rw [he]
  calc
    _ ≤ 100*(N : ℝ)*N := mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by ring

theorem full_query_inv_sq_le {N : ℕ} (hN : 0 < N) {δ M B : ℝ}
    (hδ : 0 < δ) (hi : δ⁻¹ ≤ N) (hM : 0 < M) (hMB : M ≤ B) :
    (KSFullManuscriptParameters.queryStep N δ M ^ 2)⁻¹ ≤
      32*(N : ℝ)^2 + 800*(N : ℝ)^3*B := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hB : 0 ≤ B := hM.le.trans hMB
  have hk := KSFullManuscriptParameters.curvatureTolerance_pos hN hδ
  have hs : 0 < Real.sqrt 2 := by positivity
  have hδ2 := inverse_square_le (inv_nonneg.mpr hδ.le) hi
  have hb := inv_min_sq_le (a := δ/(4*Real.sqrt 2))
    (b := Real.sqrt (KSFullManuscriptParameters.curvatureTolerance N δ/(8*N*M)))
    (by positivity) (by positivity)
  have he1 : ((δ/(4*Real.sqrt 2))^2)⁻¹ = 32*(δ⁻¹)^2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    simp
    ring
  have he2 : (Real.sqrt (KSFullManuscriptParameters.curvatureTolerance N δ/(8*N*M))^2)⁻¹ =
      800*(N : ℝ)^2*M*δ⁻¹ := by
    rw [Real.sq_sqrt (by positivity)]
    simp only [KSFullManuscriptParameters.curvatureTolerance, div_eq_mul_inv, mul_inv_rev, inv_inv]
    norm_num
    ring
  change (KSFullManuscriptParameters.queryStep N δ M ^ 2)⁻¹ ≤ _ at hb
  rw [he1, he2] at hb
  apply hb.trans (add_le_add (mul_le_mul_of_nonneg_left hδ2 (by norm_num)) ?_)
  calc
    _ ≤ 800*(N : ℝ)^2*B*δ⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMB (by positivity)) (by positivity)
    _ ≤ 800*(N : ℝ)^2*B*N := mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by ring

theorem full_value_inv_le {N : ℕ} (hN : 0 < N) {δ M B : ℝ}
    (hδ : 0 < δ) (hi : δ⁻¹ ≤ N) (hM : 0 < M) (hMB : M ≤ B) :
    (KSFullManuscriptParameters.valueTolerance N δ M)⁻¹ ≤
      1600*(N : ℝ)^3*(32*(N : ℝ)^2 + 800*(N : ℝ)^3*B) := by
  have hq := full_query_inv_sq_le hN hδ hi hM hMB
  have hk := full_curvature_inv_le hN hδ hi
  have he : (KSFullManuscriptParameters.valueTolerance N δ M)⁻¹ =
      16*(N : ℝ)*(KSFullManuscriptParameters.curvatureTolerance N δ)⁻¹ *
        (KSFullManuscriptParameters.queryStep N δ M ^ 2)⁻¹ := by
    simp [KSFullManuscriptParameters.valueTolerance]
    ring
  rw [he]
  calc
    _ ≤ (16*(N : ℝ)*(100*(N : ℝ)^2)) *
        (32*(N : ℝ)^2 + 800*(N : ℝ)^3*B) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hk (by positivity)) hq
        (by positivity) (by positivity)
    _ = _ := by ring

theorem full_movement_inv_sq_le {N : ℕ} (hN : 0 < N) {δ M B : ℝ}
    (hδ : 0 < δ) (hi : δ⁻¹ ≤ N) (hM : 0 < M) (hMB : M ≤ B) :
    (KSFullManuscriptParameters.movementStep N δ M ^ 2)⁻¹ ≤
      16*(N : ℝ)^2 + 100*(N : ℝ)^2*B := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hB : 0 ≤ B := hM.le.trans hMB
  have hk := KSFullManuscriptParameters.curvatureTolerance_pos hN hδ
  have hδ2 := inverse_square_le (inv_nonneg.mpr hδ.le) hi
  have hb := inv_min_sq_le (a := δ/4)
    (b := Real.sqrt (24*KSFullManuscriptParameters.curvatureTolerance N δ/M))
    (by positivity) (by positivity)
  have he1 : ((δ/4)^2)⁻¹ = 16*(δ⁻¹)^2 := by simp; ring
  have he2 : (Real.sqrt (24*KSFullManuscriptParameters.curvatureTolerance N δ/M)^2)⁻¹ =
      (25/6 : ℝ)*(N : ℝ)*M*δ⁻¹ := by
    rw [Real.sq_sqrt (by positivity)]
    simp only [KSFullManuscriptParameters.curvatureTolerance, div_eq_mul_inv, mul_inv_rev, inv_inv]
    norm_num
    ring
  change (KSFullManuscriptParameters.movementStep N δ M ^ 2)⁻¹ ≤ _ at hb
  rw [he1,he2] at hb
  apply hb.trans (add_le_add (mul_le_mul_of_nonneg_left hδ2 (by norm_num)) ?_)
  calc
    _ ≤ (25/6 : ℝ)*(N : ℝ)*B*δ⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMB (by positivity)) (by positivity)
    _ ≤ (25/6 : ℝ)*(N : ℝ)*B*N := mul_le_mul_of_nonneg_left hi (by positivity)
    _ = (25/6 : ℝ)*(N : ℝ)^2*B := by ring
    _ ≤ _ := by
      have hB : 0 ≤ B := hM.le.trans hMB
      nlinarith [mul_nonneg (sq_nonneg (N : ℝ)) hB]

theorem full_cutoff_le {N : ℕ} (hN : 0 < N) {δ M B : ℝ}
    (hδ : 0 < δ) (hi : δ⁻¹ ≤ N) (hM : 0 < M) (hMB : M ≤ B) :
    (KSFullManuscriptParameters.cutoff N δ M : ℝ) ≤
      256*(N : ℝ)^3 + 100*(N : ℝ)^3*B + 1 := by
  have hB : 0 ≤ B := hM.le.trans hMB
  have hδ2 := inverse_square_le (inv_nonneg.mpr hδ.le) hi
  have h1 : 256*(N : ℝ)/δ^2 ≤ 256*(N : ℝ)^3 := by
    simp only [div_eq_mul_inv, ← inv_pow]
    calc
      _ ≤ 256*(N : ℝ)*((N : ℝ)^2) := mul_le_mul_of_nonneg_left hδ2 (by positivity)
      _ = _ := by ring
  have h2 : 100*(N : ℝ)^2*M/δ ≤ 100*(N : ℝ)^3*B := by
    simp only [div_eq_mul_inv]
    calc
      _ ≤ 100*(N : ℝ)^2*B*δ⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMB (by positivity)) (by positivity)
      _ ≤ 100*(N : ℝ)^2*B*N := mul_le_mul_of_nonneg_left hi (by positivity)
      _ = _ := by ring

  exact (KSFullManuscriptWalkBudget.cutoff_le hN hδ hM).trans
    (add_le_add_right (add_le_add h1 h2) 1)


theorem eighth_rho_inv_le {N : ℕ} {δ : ℝ} (hi : δ⁻¹ ≤ N) :
    (KSEighthManuscriptParameters.rho N δ)⁻¹ ≤ 100*(N : ℝ)^2 := by
  have he : (KSEighthManuscriptParameters.rho N δ)⁻¹ = 100*(N : ℝ)*δ⁻¹ := by
    simp [KSEighthManuscriptParameters.rho]; ring
  rw [he]
  calc
    _ ≤ 100*(N : ℝ)*N := mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by ring

theorem eighth_kappa_inv_le {N : ℕ} {δ : ℝ} (hi : δ⁻¹ ≤ N) :
    (KSEighthManuscriptParameters.kappa N δ)⁻¹ ≤ 10000*(N : ℝ)^3 := by
  have he : (KSEighthManuscriptParameters.kappa N δ)⁻¹ = 10000*(N : ℝ)^2*δ⁻¹ := by
    simp [KSEighthManuscriptParameters.kappa]; ring
  rw [he]
  calc
    _ ≤ 10000*(N : ℝ)^2*N := mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by ring

theorem eighth_precision_inv_le {N : ℕ} {δ : ℝ} (hi : δ⁻¹ ≤ N) :
    (KSEighthManuscriptParameters.precision N δ)⁻¹ ≤ 1000000*(N : ℝ)^4 := by
  have he : (KSEighthManuscriptParameters.precision N δ)⁻¹ =
      100*(N : ℝ)*(KSEighthManuscriptParameters.kappa N δ)⁻¹ := by
    simp [KSEighthManuscriptParameters.precision]; ring
  rw [he]
  calc
    _ ≤ 100*(N : ℝ)*(10000*(N : ℝ)^3) :=
      mul_le_mul_of_nonneg_left (eighth_kappa_inv_le hi) (by positivity)
    _ = _ := by ring

theorem eighth_beta_inv_le {N d : ℕ} (v : Fin N → Fin d → ℂ) {δ θ B : ℝ}
    (hδ : 0 < δ) (hi : δ⁻¹ ≤ N) (hM : 0 ≤ KSEighthManuscriptParameters.fourthCap v θ)
    (hMB : KSEighthManuscriptParameters.fourthCap v θ ≤ B) :
    (KSEighthManuscriptParameters.beta v δ θ)⁻¹ ≤ 1000000*(N : ℝ)^4*(B+1) := by
  have he : (KSEighthManuscriptParameters.beta v δ θ)⁻¹ =
      (100*(N : ℝ)*(KSEighthManuscriptParameters.fourthCap v θ+1))*
        (KSEighthManuscriptParameters.kappa N δ)⁻¹ := by
    simp [KSEighthManuscriptParameters.beta]; ring
  have hB : 0 ≤ B := hM.trans hMB
  have hk : 0 ≤ KSEighthManuscriptParameters.kappa N δ := by
    unfold KSEighthManuscriptParameters.kappa; positivity
  rw [he]
  calc
    _ ≤ (100*(N : ℝ)*(B+1))*(10000*(N : ℝ)^3) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (add_le_add_right hMB 1) (by positivity))
        (eighth_kappa_inv_le hi) (by positivity) (by positivity)
    _ = _ := by ring

theorem eighth_movement_inv_sq_le {N d : ℕ} (v : Fin N → Fin d → ℂ)
    {δ θ B : ℝ} (hN : 0 < N) (hδ : 0 < δ) (hi : δ⁻¹ ≤ N)
    (hM : 0 < KSEighthManuscriptParameters.fourthCap v θ)
    (hMB : KSEighthManuscriptParameters.fourthCap v θ ≤ B) :
    (KSEighthManuscriptParameters.movementStep v δ θ ^ 2)⁻¹ ≤
      40000*((N : ℝ)^5+B*(N : ℝ)^4+1) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hB : 0 ≤ B := hM.le.trans hMB
  have hr := KSEighthManuscriptParameters.rho_pos hN hδ
  have hδ2 := inverse_square_le (inv_nonneg.mpr hδ.le) hi
  let a := KSEighthManuscriptParameters.rho N δ/Real.sqrt (N : ℝ)
  let b := Real.sqrt (δ/(10000*KSEighthManuscriptParameters.fourthCap v θ*(N : ℝ)^3))
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hs := inv_min_sq_le ha (lt_min hb (by norm_num : (0 : ℝ) < 1/100))
  have hs2 := inv_min_sq_le hb (by norm_num : (0 : ℝ) < 1/100)
  have h1 : (a^2)⁻¹ ≤ 10000*(N : ℝ)^5 := by
    have he : (a^2)⁻¹ = 10000*(N : ℝ)^3*(δ⁻¹)^2 := by
      dsimp [a,KSEighthManuscriptParameters.rho]
      rw [div_pow,Real.sq_sqrt hn.le,div_pow,mul_pow]
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, ← inv_pow]
      norm_num
      ring
    rw [he]
    calc
      _ ≤ 10000*(N : ℝ)^3*(N : ℝ)^2 := mul_le_mul_of_nonneg_left hδ2 (by positivity)
      _ = _ := by ring
  have h2 : (b^2)⁻¹ ≤ 10000*B*(N : ℝ)^4 := by
    have he : (b^2)⁻¹ = 10000*KSEighthManuscriptParameters.fourthCap v θ*(N : ℝ)^3*δ⁻¹ := by
      dsimp [b]
      rw [Real.sq_sqrt (by positivity)]
      simp [div_eq_mul_inv]
    rw [he]
    calc
      _ ≤ 10000*B*(N : ℝ)^3*δ⁻¹ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMB (by norm_num)) (by positivity))
          (by positivity)
      _ ≤ 10000*B*(N : ℝ)^3*N := mul_le_mul_of_nonneg_left hi (by positivity)
      _ = _ := by ring
  have he : (KSEighthManuscriptParameters.movementStep v δ θ^2)⁻¹ =
      4*(min a (min b (1/100))^2)⁻¹ := by
    dsimp [KSEighthManuscriptParameters.movementStep,a,b]
    rw [mul_pow]
    norm_num
    ring
  rw [he]
  have h3 : (((1/100 : ℝ)^2)⁻¹) = 10000 := by norm_num
  rw [h3] at hs2
  nlinarith

theorem eighth_cutoff_le {N d : ℕ} (v : Fin N → Fin d → ℂ)
    {δ θ B : ℝ} (hN : 0 < N) (hδ : 0 < δ) (hi : δ⁻¹ ≤ N)
    (hM : 0 < KSEighthManuscriptParameters.fourthCap v θ)
    (hMB : KSEighthManuscriptParameters.fourthCap v θ ≤ B) :
    (KSEighthManuscriptBudgets.cutoff v δ θ : ℝ) ≤
      4000000*(N : ℝ)*((N : ℝ)^5+B*(N : ℝ)^4+1)+1 := by
  have hb := eighth_movement_inv_sq_le v hN hδ hi hM hMB
  have hc := (Nat.ceil_lt_add_one
    (by positivity : 0 ≤ 100*(N : ℝ)/KSEighthManuscriptParameters.movementStep v δ θ^2)).le
  change (KSEighthManuscriptBudgets.cutoff v δ θ : ℝ) ≤ _ at hc
  apply hc.trans
  have hh := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 100*(N : ℝ))
  simp only [div_eq_mul_inv] at *
  nlinarith


theorem eighth_count_le {N : ℕ} (x : Fin N → ℝ) : KSEighthLiveEnumeration.count x ≤ N := by
  simpa [KSEighthLiveEnumeration.count, KSEighthLiveEnumeration.labels]
    using List.length_filter_le (fun i : Fin N => decide (|x i| < (1/8 : ℝ))) (List.finRange N)

theorem eighth_query_inv_sq_le {N d : ℕ} (v : Fin N → Fin d → ℂ)
    {δ θ B : ℝ} (hN : 0 < N) (hδ : 0 < δ) (hi : δ⁻¹ ≤ N)
    (hM : 0 < KSEighthManuscriptParameters.fourthCap v θ)
    (hMB : KSEighthManuscriptParameters.fourthCap v θ ≤ B)
    (x : Fin N → ℝ) (hx : 0 < KSEighthLiveEnumeration.count x) :
    (KSEighthHessianQueries.queryMesh v θ (KSEighthManuscriptParameters.precision N δ) x ^ 2)⁻¹ ≤
      1024+1000000*B*(N : ℝ)^5 := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hc : (0 : ℝ) < KSEighthLiveEnumeration.count x := Nat.cast_pos.mpr hx
  have hcN : (KSEighthLiveEnumeration.count x : ℝ) ≤ N := by exact_mod_cast eighth_count_le x
  have hB : 0 ≤ B := hM.le.trans hMB
  have hp := KSEighthManuscriptParameters.precision_pos hN hδ
  have hcap : 0 < KSEighthInputTaylorBound.fourthBudget v θ + 1 := by
    simpa only [KSEighthManuscriptParameters.fourthCap,add_comm] using hM
  have hs := inv_min_sq_le (by norm_num : (0 : ℝ) < 1/32)
    (b := Real.sqrt (KSEighthManuscriptParameters.precision N δ /
      ((KSEighthLiveEnumeration.count x : ℝ)*(KSEighthInputTaylorBound.fourthBudget v θ+1))))
    (by positivity)
  change (KSEighthHessianQueries.queryMesh v θ (KSEighthManuscriptParameters.precision N δ) x ^ 2)⁻¹ ≤ _ at hs
  have he : (Real.sqrt (KSEighthManuscriptParameters.precision N δ /
      ((KSEighthLiveEnumeration.count x : ℝ)*(KSEighthInputTaylorBound.fourthBudget v θ+1)))^2)⁻¹ =
      (KSEighthLiveEnumeration.count x : ℝ)*KSEighthManuscriptParameters.fourthCap v θ*
        (KSEighthManuscriptParameters.precision N δ)⁻¹ := by
    rw [Real.sq_sqrt (by positivity)]
    simp only [KSEighthManuscriptParameters.fourthCap, div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  rw [he] at hs
  norm_num at hs
  apply hs.trans (add_le_add_left ?_ 1024)
  calc
    _ ≤ ((N : ℝ)*B)*(1000000*(N : ℝ)^4) :=
      mul_le_mul (mul_le_mul hcN hMB hM.le (Nat.cast_nonneg N))
        (eighth_precision_inv_le hi) (by positivity) (by positivity)
    _ = _ := by ring

theorem eighth_query_value_inv_le {N d : ℕ} (v : Fin N → Fin d → ℂ)
    {δ θ B : ℝ} (hN : 0 < N) (hδ : 0 < δ) (hi : δ⁻¹ ≤ N)
    (hM : 0 < KSEighthManuscriptParameters.fourthCap v θ)
    (hMB : KSEighthManuscriptParameters.fourthCap v θ ≤ B)
    (x : Fin N → ℝ) (hx : 0 < KSEighthLiveEnumeration.count x) :
    (KSEighthHessianQueries.queryTolerance v θ (KSEighthManuscriptParameters.precision N δ) x)⁻¹ ≤
      4000000*(N : ℝ)^5*(1024+1000000*B*(N : ℝ)^5) := by
  have hcN : (KSEighthLiveEnumeration.count x : ℝ) ≤ N := by exact_mod_cast eighth_count_le x
  have hp := KSEighthManuscriptParameters.precision_pos hN hδ
  have hB : 0 ≤ B := hM.le.trans hMB
  have hq := eighth_query_inv_sq_le v hN hδ hi hM hMB x hx
  have he : (KSEighthHessianQueries.queryTolerance v θ (KSEighthManuscriptParameters.precision N δ) x)⁻¹ =
      (4*(KSEighthLiveEnumeration.count x : ℝ)*(KSEighthManuscriptParameters.precision N δ)⁻¹)*
        (KSEighthHessianQueries.queryMesh v θ (KSEighthManuscriptParameters.precision N δ) x^2)⁻¹ := by
    simp [KSEighthHessianQueries.queryTolerance,KSNumericalHessian.valueTolerance,
      KSEighthHessianQueries.queryMesh]
    ring
  rw [he]
  calc
    _ ≤ (4*(N : ℝ)*(1000000*(N : ℝ)^4))*(1024+1000000*B*(N : ℝ)^5) :=
      mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hcN (by norm_num))
          (eighth_precision_inv_le hi) (by positivity) (by positivity))
        hq (by positivity) (by positivity)
    _ = _ := by ring

end MatrixSpencer.KSManuscriptPolynomialParameters
