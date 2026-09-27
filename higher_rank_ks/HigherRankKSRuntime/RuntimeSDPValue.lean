import AugmentedHigherRankKS.FourBlockSDPIdentity
import MatrixSpencer.RealRAMJacobiIteration
import MatrixSpencer.KSFullManuscriptSDPBlockPencil

/-! Value queries for a finite, explicit block SDP. The permitted solver
only approximates an attained linear optimum of these displayed LMIs.
Its contract contains no potential, derivative, walk, or discrepancy claim.
The equivalence with the actual optimized potential is proved below. -/
open Matrix MatrixSpencer HigherRankKS AugmentedHigherRankKS
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace HigherRankKSRuntime.SDPValue
open RealRAM.JacobiIteration (Counted)
variable {N d k : ℕ}
local instance sdpCStar {j : Type*} [Fintype j] [DecidableEq j] :
    CStarAlgebra (Matrix j j ℂ) := {}

abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ
abbrev Full (d : ℕ) := Matrix (FourSpin (Fin d)) (FourSpin (Fin d)) ℂ

/-- Only raw scalar/matrix data are supplied to the solver. -/
structure Program (N d : ℕ) where
  factor : Fin N → Mat d
  center : Full d
  reserve : Fin N → ℝ
  theta : ℝ

/-- Finitely many Hermitian matrix variables and one unrestricted complex
fidelity variable. No infinite sequence is supplied to the solver. -/
structure Variables (N d k : ℕ) where
  S : selfAdjoint (Full d)
  U : selfAdjoint (Full d)
  X : Full d
  Y : Fin N → Fin (k+1) → selfAdjoint (Mat d)

def carrier (P : Program N d) (v : Variables N d k) (i : Fin N) : Mat d :=
  (P.factor i)ᴴ * AugmentedHigherRankKS.marginal (v.S : Full d) * P.factor i

def source (P : Program N d) (v : Variables N d k) : Full d :=
  ∑ i, P.reserve i • spinDuplicateCLM (spinDuplicateCLM
    (P.factor i * (v.Y i (Fin.last k) : Mat d) * (P.factor i)ᴴ))

/-- Every constraint is an affine equality or a Hermitian PSD block. -/
def Feasible (P : Program N d) (v : Variables N d k) : Prop :=
  (∀ i, (v.Y i 0 : Mat d) = realTrace (carrier P v i) • 1) ∧
  (∀ i j, (v.Y i j : Mat d).PosSemidef) ∧
  (∀ i (j : Fin k), (Matrix.fromBlocks (carrier P v i)
    (v.Y i j.succ : Mat d) (v.Y i j.succ : Mat d) (v.Y i j.castSucc : Mat d)).PosSemidef) ∧
  realTrace (v.S : Full d) = 1 ∧ (v.U : Full d).PosSemidef ∧
  (Matrix.fromBlocks (v.S : Full d) v.X v.Xᴴ (source P v)).PosSemidef ∧
  (Matrix.fromBlocks (v.S : Full d) (v.U : Full d) (v.U : Full d) 1).PosSemidef

def objective (P : Program N d) (v : Variables N d k) : ℝ :=
  realTrace (P.center * (v.S : Full d)) + 2*realTrace v.X +
    2*P.theta*realTrace (v.U : Full d)

def ofAtoms (A : Fin N → Mat d) (H : Full d) (c : Fin N → ℝ) (θ : ℝ) : Program N d :=
  ⟨fun i => CFC.sqrt (A i),H,c,θ⟩

def extendedLift (v : Variables N d k) : FourBlockSDP.Lift (Fin N) (Fin d) :=
  fun i j => v.Y i ⟨min j k,by omega⟩

theorem extendedLift_apply (v : Variables N d k) (i : Fin N) (j : ℕ) (hj : j ≤ k) :
    extendedLift v i j = (v.Y i ⟨j,by omega⟩ : Mat d) := by
  simp only [extendedLift, min_eq_left hj]

theorem ofAtoms_carrier (A : Fin N → Mat d) (H : Full d) (c : Fin N → ℝ) (θ : ℝ)
    (v : Variables N d k) (i : Fin N) :
    carrier (ofAtoms A H c θ) v i = FourBlockSDP.ownerCarrier (A i) (v.S : Full d) := by
  simp only [carrier, ofAtoms, FourBlockSDP.ownerCarrier, HigherRankKS.carrier, AugmentedHigherRankKS.marginal,
    (CFC.sqrt_nonneg (A i)).posSemidef.isHermitian.eq]

theorem ofAtoms_source (A : Fin N → Mat d) (H : Full d) (c : Fin N → ℝ) (θ : ℝ)
    (v : Variables N d k) :
    source (ofAtoms A H c θ) v = FourBlockSDP.liftedSource A c k (extendedLift v) := by
  unfold source FourBlockSDP.liftedSource FourBlockSDP.output
  apply Finset.sum_congr rfl
  intro i _
  simp only [ofAtoms, extendedLift, min_self, Fin.last,
    (CFC.sqrt_nonneg (A i)).posSemidef.isHermitian.eq]

theorem feasible_iff (A : Fin N → Mat d) (H : Full d) (c : Fin N → ℝ) (θ : ℝ)
    (v : Variables N d k) :
    Feasible (ofAtoms A H c θ) v ↔ FourBlockSDP.Feasible A k c
      (v.S : Full d) (v.U : Full d) v.X (extendedLift v) := by
  simp only [Feasible, FourBlockSDP.Feasible, FourBlockSDP.PowerFeasible,
    KSFullManuscriptSDPIdentity.Feasible, zero_smul, add_zero,
    ofAtoms_carrier, ofAtoms_source]
  constructor
  · rintro ⟨h0,hY,hstep,hS,hU,hF,hR⟩
    refine ⟨fun i => ⟨?_,?_,?_⟩,hS,hU,hF,hR⟩
    · simpa only [extendedLift_apply v i 0 (Nat.zero_le k)] using h0 i
    · intro j hj
      rw [extendedLift_apply v i j hj]
      exact hY i _
    · intro j hj
      rw [extendedLift_apply v i (j+1) (by omega),extendedLift_apply v i j (by omega)]
      exact hstep i ⟨j,hj⟩
  · rintro ⟨hpow,hS,hU,hF,hR⟩
    refine ⟨?_,?_,?_,hS,hU,hF,hR⟩
    · intro i
      simpa only [extendedLift_apply v i 0 (Nat.zero_le k)] using (hpow i).1
    · intro i j
      have hh := (hpow i).2.1 j.val (by omega)
      simpa only [extendedLift_apply v i j.val (by omega)] using hh
    · intro i j
      have hh := (hpow i).2.2 j.val j.isLt
      simpa only [extendedLift_apply v i (j.val+1) (by omega),
        extendedLift_apply v i j.val (by omega)] using hh

theorem objective_eq (A : Fin N → Mat d) (H : Full d) (c : Fin N → ℝ) (θ : ℝ)
    (v : Variables N d k) :
    objective (ofAtoms A H c θ) v = FourBlockSDP.value H θ
      (v.S : Full d) (v.U : Full d) v.X := rfl

/-- Restriction to exactly the finitely many variables sent to the solver. -/
def restrict (S U X : Full d) (Y : FourBlockSDP.Lift (Fin N) (Fin d))
    (hS : S.IsHermitian) (hU : U.IsHermitian)
    (hY : ∀ i j, j ≤ k → (Y i j).IsHermitian) : Variables N d k :=
  ⟨⟨S,hS.isSelfAdjoint⟩,⟨U,hU.isSelfAdjoint⟩,X,
    fun i j => ⟨Y i j, (hY i j (by omega)).isSelfAdjoint⟩⟩

theorem restrict_feasible {A : Fin N → Mat d} (H : Full d) {c : Fin N → ℝ} (θ : ℝ)
    {S U X : Full d} {Y : FourBlockSDP.Lift (Fin N) (Fin d)}
    (hf : FourBlockSDP.Feasible A k c S U X Y) :
    ∃ v : Variables N d k, Feasible (ofAtoms A H c θ) v ∧
      objective (ofAtoms A H c θ) v = FourBlockSDP.value H θ S U X := by
  have hS := (KSFullManuscriptSDPIdentity.feasible_density hf.2).1.isHermitian
  have hU := hf.2.2.1.isHermitian
  have hY : ∀ i j, j ≤ k → (Y i j).IsHermitian :=
    fun i j hj => ((hf.1 i).2.1 j hj).isHermitian
  let v := restrict S U X Y hS hU hY
  refine ⟨v,?_,rfl⟩
  apply (feasible_iff A H c θ v).2
  have he (i : Fin N) (j : ℕ) (hj : j ≤ k) : extendedLift v i j = Y i j := by
    rw [extendedLift_apply v i j hj]
    rfl
  refine ⟨fun i => ⟨?_,?_,?_⟩,?_⟩
  · rw [he i 0 (Nat.zero_le k)]
    exact (hf.1 i).1
  · intro j hj
    rw [he i j hj]
    exact (hf.1 i).2.1 j hj
  · intro j hj
    rw [he i (j+1) (by omega),he i j (by omega)]
    exact (hf.1 i).2.2 j hj
  · have hsrc : FourBlockSDP.liftedSource A c k (extendedLift v) =
        FourBlockSDP.liftedSource A c k Y := by
      unfold FourBlockSDP.liftedSource
      simp only [he _ k le_rfl]
    change KSFullManuscriptSDPIdentity.Feasible
      (fun _ => FourBlockSDP.liftedSource A c k (extendedLift v)) 0 S U X
    rw [hsrc]
    exact hf.2

theorem attained_potential (A : Fin N → Mat d) (H : Full d) (hd : 0 < d)
    (k : ℕ) (hk : 1 ≤ k) {c : Fin N → ℝ} (hc : ∀ i, 0 ≤ c i)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ v : Variables N d k, Feasible (ofAtoms A H c θ) v ∧
      objective (ofAtoms A H c θ) v = potential H A ((1:ℝ)/2^k) c θ ∧
      ∀ w : Variables N d k, Feasible (ofAtoms A H c θ) w →
        objective (ofAtoms A H c θ) w ≤ objective (ofAtoms A H c θ) v := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  obtain ⟨S,U,X,Y,hf,hvalue,hmax⟩ := FourBlockSDP.SDP_exact H A k hk hc hθ
  obtain ⟨v,hv,he⟩ := restrict_feasible H θ hf
  refine ⟨v,hv,he.trans hvalue,fun w hw => ?_⟩
  rw [he,objective_eq]
  exact hmax _ _ _ _ ((feasible_iff A H c θ w).1 hw)

/-- Conservative dense size after real coordinates and realification.
The exact finite block representation is smaller. -/
def variableCount (N d k : ℕ) : ℕ := 2*(3*(4*d)^2+N*(k+1)*d^2)
def pencilOrder (N d k : ℕ) : ℕ := 40*d+2*N*(3*k+1)*d+4*N*d^2+2
def dataSize (N d k : ℕ) : ℕ := (variableCount N d k+1)*(pencilOrder N d k)^2+
  variableCount N d k+2

/-- The permitted solver accepts this explicit finite affine-block specification.
Its work contract includes materializing its real-coordinate SDP encoding.
Input factors, centers, and reserves are computed outside this primitive. -/
structure Solver where
  report : {N d k : ℕ} → Program N d → ℝ → Counted ℝ
  accuracy : ∀ {N d k : ℕ} (P : Program N d) (ν : ℝ), 0 < ν →
    ∀ v : Variables N d k, Feasible P v →
      (∀ w : Variables N d k, Feasible P w → objective P w ≤ objective P v) →
      |(report (k := k) P ν).value-objective P v| ≤ ν
  coefficient : ℕ
  degree : ℕ
  work_bound : ∀ {N d k : ℕ} (P : Program N d) (ν : ℝ), 0 < ν →
    (report (k := k) P ν).cost ≤ coefficient*(dataSize N d k+⌈ν⁻¹⌉₊+1)^degree

/-- Charges the solver invocation, including its affine-block encoding.
Factor construction and center/reserve assembly are charged separately. -/
def query (O : Solver) (A : Fin N → Mat d) (k : ℕ) (H : Full d)
    (c : Fin N → ℝ) (θ ν : ℝ) : Counted ℝ :=
  O.report (k := k) (ofAtoms A H c θ) ν

theorem query_accuracy (O : Solver) (A : Fin N → Mat d) (k : ℕ)
    (H : Full d) (hd : 0 < d) (hk : 1 ≤ k) {c : Fin N → ℝ}
    (hc : ∀ i, 0 ≤ c i) {θ ν : ℝ} (hθ : 0 < θ) (hν : 0 < ν) :
    |(query O A k H c θ ν).value-potential H A ((1:ℝ)/2^k) c θ| ≤ ν := by
  obtain ⟨v,hv,he,hmax⟩ := attained_potential A H hd k hk hc hθ
  have hh := O.accuracy (ofAtoms A H c θ) ν hν v hv hmax
  simpa only [query,he] using hh

theorem query_cost (O : Solver) (A : Fin N → Mat d) (k : ℕ)
    (H : Full d) (c : Fin N → ℝ) (θ : ℝ) {ν : ℝ} (hν : 0 < ν) :
    (query O A k H c θ ν).cost ≤
      O.coefficient*(dataSize N d k+⌈ν⁻¹⌉₊+1)^O.degree :=
  O.work_bound _ _ hν

end HigherRankKSRuntime.SDPValue

