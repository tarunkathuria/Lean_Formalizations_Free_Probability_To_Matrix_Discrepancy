import MatrixSpencer.RectangularTunedParameters

/-! Explicit polynomial size of the dyadic semidefinite representation.
These are representation-size bounds, not bounds on the rectangular walk's
numerical tolerances, iteration counts, or total runtime. -/
noncomputable section
namespace MatrixSpencer.DyadicSDPProgramSize

/-- Trace-one Hermitian density, `m` Hermitian auxiliary matrices, and one
unrestricted complex fidelity witness. -/
def variableCount (m d : ℕ) : ℕ := (m+3)*d^2-1

/-- `m` positivity constraints, `m` dyadic blocks, and one fidelity block. -/
def constraintCount (m : ℕ) : ℕ := 2*m+1

/-- Every complex block has order at most `2d`; realification doubles it. -/
def blockOrder (d : ℕ) : ℕ := 4*d

/-- Dense real affine LMI coefficient entries, including constant matrices. -/
def denseCoefficients (m d : ℕ) : ℕ :=
  constraintCount m * (variableCount m d+1) * blockOrder d ^ 2

theorem variableCount_add_one (m : ℕ) {d : ℕ} (hd : 0 < d) :
    variableCount m d+1 = (m+3)*d^2 := by
  unfold variableCount
  have hh : 1 ≤ (m+3)*d^2 := by
    have hp : 0 < d^2 := pow_pos hd _
    nlinarith
  exact Nat.sub_add_cancel hh

theorem denseCoefficients_eq (m : ℕ) {d : ℕ} (hd : 0 < d) :
    denseCoefficients m d = 16*(2*m+1)*(m+3)*d^4 := by
  rw [denseCoefficients, variableCount_add_one m hd]
  unfold constraintCount blockOrder
  ring

/-- The actual dyadic depth chosen for an `N`-matrix, `D`-dimensional input
is at most linear in the original matrix dimension.  The bound includes the
signed lift to physical dimension `2D`. -/
theorem rectangular_depth_le {N D : ℕ} (hN : 1 ≤ N) (hD : 1 ≤ D) :
    RectangularTunedParameters.depth N D ≤ 2+2*D := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  have hd : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hdiv : 2*(D : ℝ)/(N : ℝ) ≤ 2*D := by
    apply (div_le_iff₀ hn0).mpr
    nlinarith
  have ha : RectangularParameters.aspect (2*(D : ℝ)) (N : ℝ) ≤ 2*D :=
    max_le (by linarith) hdiv
  have hl := Real.log_le_self
    (RectangularParameters.aspect_pos (2*(D : ℝ)) (N : ℝ)).le
  have ho := RectangularParameters.order_le_two_add_log (2*(D : ℝ)) (N : ℝ)
  have hob : RectangularParameters.order (2*(D : ℝ)) (N : ℝ) ≤ 2+2*D := by
    have hh : (RectangularParameters.order (2*(D : ℝ)) (N : ℝ) : ℝ) ≤
        (2+2*D : ℕ) := by push_cast; linarith
    exact_mod_cast hh
  have hpos : RectangularParameters.order (2*(D : ℝ)) (N : ℝ) ≠ 0 := by
    have hh := RectangularParameters.order_two_le (2*(D : ℝ)) (N : ℝ)
    omega
  have hh := Nat.log_lt_self 2 hpos
  unfold RectangularTunedParameters.depth RectangularParameters.dyadicDepth
  omega

theorem rectangular_variableCount_le {N D : ℕ} (hN : 1 ≤ N) (hD : 1 ≤ D) :
    variableCount (RectangularTunedParameters.depth N D) (2*D) ≤
      4*(2*D+5)*D^2 := by
  have hh := rectangular_depth_le hN hD
  have hv : variableCount (RectangularTunedParameters.depth N D) (2*D) ≤
      (RectangularTunedParameters.depth N D+3)*(2*D)^2 := Nat.sub_le _ _
  calc
    _ ≤ (2*D+5)*(2*D)^2 := hv.trans (Nat.mul_le_mul_right _ (by omega))
    _ = _ := by ring

theorem rectangular_constraintCount_le {N D : ℕ} (hN : 1 ≤ N) (hD : 1 ≤ D) :
    constraintCount (RectangularTunedParameters.depth N D) ≤ 4*D+5 := by
  have hh := rectangular_depth_le hN hD
  unfold constraintCount
  omega

@[simp] theorem rectangular_blockOrder (D : ℕ) : blockOrder (2*D) = 8*D := by
  unfold blockOrder
  ring

/-- An explicit polynomial of fixed degree six bounds the entire dense LMI
coefficient array for the actual tuned rectangular exponent. -/
theorem rectangular_denseCoefficients_le {N D : ℕ} (hN : 1 ≤ N) (hD : 1 ≤ D) :
    denseCoefficients (RectangularTunedParameters.depth N D) (2*D) ≤
      256*(4*D+5)*(2*D+5)*D^4 := by
  have hh := rectangular_depth_le hN hD
  rw [denseCoefficients_eq _ (by omega : 0 < 2*D)]
  calc
    _ ≤ 16*(4*D+5)*(2*D+5)*(2*D)^4 := by
      gcongr <;> omega
    _ = _ := by ring

/-- Simultaneous explicit input-polynomial bounds on variables, LMI count,
real LMI order, and dense coefficient entries. -/
theorem rectangular_sizes {N D : ℕ} (hN : 1 ≤ N) (hD : 1 ≤ D) :
    let m := RectangularTunedParameters.depth N D
    variableCount m (2*D) ≤ 4*(2*D+5)*D^2 ∧
    constraintCount m ≤ 4*D+5 ∧
    blockOrder (2*D) = 8*D ∧
    denseCoefficients m (2*D) ≤ 256*(4*D+5)*(2*D+5)*D^4 :=
  ⟨rectangular_variableCount_le hN hD, rectangular_constraintCount_le hN hD,
    rectangular_blockOrder D, rectangular_denseCoefficients_le hN hD⟩

end MatrixSpencer.DyadicSDPProgramSize
