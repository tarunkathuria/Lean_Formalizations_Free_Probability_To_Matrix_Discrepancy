import SeamlessKS.Parameters

/-! Natural polynomial caps; their real casts equal the analytic majorants.
These are bounds for finite counters, not supplied numerical assumptions. -/
namespace SeamlessKS.RuntimeBudgets

def radiusInverseCap (N : ℕ) : ℕ := 10000*(1+22500*N^2)
def jointDerivativeCap (N d : ℕ) : ℕ := 10000*(2*d+1)^2*(10*radiusInverseCap N)^4
def derivativeCap (N d : ℕ) : ℕ :=
  1+(jointDerivativeCap N d+3*(jointDerivativeCap N d)^2*(4*N)) *
    (1+jointDerivativeCap N d*(4*N))^4
def queryInverseSquareCap (N d : ℕ) : ℕ :=
  256*(100*N^2)^2+128*N*derivativeCap N d*(100*N^2)
def movementInverseSquareCap (N d : ℕ) : ℕ :=
  256*(100*N^2)^2+4*derivativeCap N d*(100*N^2)
def hessianAccuracyInverseCap (N d : ℕ) : ℕ :=
  128*N*(100*N^2)*queryInverseSquareCap N d
def localAccuracyInverseCap (N d : ℕ) : ℕ :=
  8*(100*N^2)*movementInverseSquareCap N d
def horizonCap (N d : ℕ) : ℕ := 16*N*movementInverseSquareCap N d+1

@[simp] theorem cast_radiusInverseCap (N : ℕ) :
    (radiusInverseCap N : ℝ)=Parameters.radiusInverseCap N := by
  simp [radiusInverseCap,Parameters.radiusInverseCap]
@[simp] theorem cast_jointDerivativeCap (N d : ℕ) :
    (jointDerivativeCap N d : ℝ)=Parameters.jointDerivativeCap N d := by
  simp [jointDerivativeCap,Parameters.jointDerivativeCap,Parameters.objectiveBound]
@[simp] theorem cast_derivativeCap (N d : ℕ) :
    (derivativeCap N d : ℝ)=Parameters.derivativeCap N d := by
  simp [derivativeCap,Parameters.derivativeCap]
@[simp] theorem cast_queryInverseSquareCap (N d : ℕ) :
    (queryInverseSquareCap N d : ℝ)=Parameters.queryInverseSquareCap N d := by
  simp [queryInverseSquareCap,Parameters.queryInverseSquareCap]
@[simp] theorem cast_movementInverseSquareCap (N d : ℕ) :
    (movementInverseSquareCap N d : ℝ)=Parameters.movementInverseSquareCap N d := by
  simp [movementInverseSquareCap,Parameters.movementInverseSquareCap]
@[simp] theorem cast_hessianAccuracyInverseCap (N d : ℕ) :
    (hessianAccuracyInverseCap N d : ℝ)=Parameters.hessianAccuracyInverseCap N d := by
  simp [hessianAccuracyInverseCap,Parameters.hessianAccuracyInverseCap]
@[simp] theorem cast_localAccuracyInverseCap (N d : ℕ) :
    (localAccuracyInverseCap N d : ℝ)=Parameters.localAccuracyInverseCap N d := by
  simp [localAccuracyInverseCap,Parameters.localAccuracyInverseCap]
@[simp] theorem cast_horizonCap (N d : ℕ) :
    (horizonCap N d : ℝ)=Parameters.horizonCap N d := by
  simp [horizonCap,Parameters.horizonCap]

def entryCap (N d : ℕ) : ℕ := 148*queryInverseSquareCap N d
-- No spectral iteration budgets are needed in the exact-EVD model.
end SeamlessKS.RuntimeBudgets
