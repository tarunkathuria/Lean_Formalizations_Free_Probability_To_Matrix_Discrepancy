import HigherRankKSRuntime.RuntimeSDPValue

/-! Explicit real coordinates for the finite SDP, and realification of
each of its PSD blocks. This is the finite encoding used by the solver
interface; no function space or nonlinear matrix power is a solver variable. -/
open Matrix MatrixSpencer AugmentedHigherRankKS
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace HigherRankKSRuntime.SDPValue
variable {N d k : ℕ}

abbrev ScalarIndex (N d k : ℕ) :=
  (Fin 3 × FourSpin (Fin d) × FourSpin (Fin d) × Bool) ⊕
    (Fin N × Fin (k+1) × Fin d × Fin d × Bool)

theorem scalarIndex_card : Fintype.card (ScalarIndex N d k) = variableCount N d k := by
  simp [ScalarIndex,FourSpin,variableCount,Fintype.card_sum,Fintype.card_prod]
  ring

def hermitianPart {j : Type*} [Fintype j] [DecidableEq j] (M : Matrix j j ℂ) :
    selfAdjoint (Matrix j j ℂ) :=
  ⟨(1/2:ℝ) • (M+Mᴴ),by
    have hh : (M+Mᴴ).IsHermitian := by
      simp only [Matrix.IsHermitian,Matrix.conjTranspose_add,
        Matrix.conjTranspose_conjTranspose]
      exact add_comm _ _
    change ((1/2:ℝ) • (M+Mᴴ))ᴴ = (1/2:ℝ) • (M+Mᴴ)
    rw [Matrix.conjTranspose_smul,star_trivial,hh.eq]⟩

theorem hermitianPart_eq {j : Type*} [Fintype j] [DecidableEq j]
    (M : selfAdjoint (Matrix j j ℂ)) : hermitianPart (M : Matrix j j ℂ) = M := by
  apply Subtype.ext
  change (1/2:ℝ) • ((M:Matrix j j ℂ)+(M:Matrix j j ℂ)ᴴ) = _
  rw [show (M:Matrix j j ℂ)ᴴ = M from M.property]
  module

def complexEntry (a b : ℝ) : ℂ := ⟨a,b⟩

def decodedFull (z : ScalarIndex N d k → ℝ) (a : Fin 3) : Full d :=
  fun i j => complexEntry (z (.inl (a,i,j,false))) (z (.inl (a,i,j,true)))

def decodedOwner (z : ScalarIndex N d k → ℝ) (i : Fin N) (j : Fin (k+1)) : Mat d :=
  fun p q => complexEntry (z (.inr (i,j,p,q,false))) (z (.inr (i,j,p,q,true)))

def decode (z : ScalarIndex N d k → ℝ) : Variables N d k :=
  ⟨hermitianPart (decodedFull z 0),hermitianPart (decodedFull z 1),
    decodedFull z 2,fun i j => hermitianPart (decodedOwner z i j)⟩

def mainVariable (v : Variables N d k) (a : Fin 3) : Full d :=
  ![(v.S : Full d),(v.U : Full d),v.X] a

def encode (v : Variables N d k) : ScalarIndex N d k → ℝ
  | .inl (a,i,j,b) => if b then (mainVariable v a i j).im else (mainVariable v a i j).re
  | .inr (i,j,p,q,b) => if b then ((v.Y i j : Mat d) p q).im else ((v.Y i j : Mat d) p q).re

theorem decodedFull_encode (v : Variables N d k) (a : Fin 3) :
    decodedFull (encode v) a = mainVariable v a := by
  ext i j
  exact Complex.ext rfl rfl

theorem decodedOwner_encode (v : Variables N d k) (i : Fin N) (j : Fin (k+1)) :
    decodedOwner (encode v) i j = (v.Y i j : Mat d) := by
  ext p q
  exact Complex.ext rfl rfl

theorem decode_encode (v : Variables N d k) : decode (encode v) = v := by
  cases v with
  | mk S U X Y =>
    simp only [decode,decodedFull_encode,decodedOwner_encode,mainVariable,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,hermitianPart_eq]
    rfl

/-- Entrywise realification replaces each complex Hermitian PSD block. -/
def realPSD {j : Type*} [Fintype j] [DecidableEq j] (M : Matrix j j ℂ) : Prop :=
  (KSComplexTraceSqrt.realification M).PosSemidef

theorem realPSD_iff {j : Type*} [Fintype j] [DecidableEq j] (M : Matrix j j ℂ) :
    realPSD M ↔ M.PosSemidef :=
  ⟨KSComplexProjectionGeometry.realification_reflects_posSemidef M,
    KSComplexTraceSqrt.realification_posSemidef M⟩

/-- The literal real-coordinate constraints passed to a numerical solver.
Complex matrix equality means equality of both displayed real coordinates. -/
def RealFeasible (P : Program N d) (z : ScalarIndex N d k → ℝ) : Prop :=
  let v := decode z
  (∀ i p q, ((v.Y i 0 : Mat d) p q).re =
      ((realTrace (carrier P v i) • (1 : Mat d)) p q).re ∧
    ((v.Y i 0 : Mat d) p q).im =
      ((realTrace (carrier P v i) • (1 : Mat d)) p q).im) ∧
  (∀ i j, realPSD (v.Y i j : Mat d)) ∧
  (∀ i (j : Fin k), realPSD (Matrix.fromBlocks (carrier P v i)
    (v.Y i j.succ : Mat d) (v.Y i j.succ : Mat d) (v.Y i j.castSucc : Mat d))) ∧
  realTrace (v.S : Full d) = 1 ∧ realPSD (v.U : Full d) ∧
  realPSD (Matrix.fromBlocks (v.S : Full d) v.X v.Xᴴ (source P v)) ∧
  realPSD (Matrix.fromBlocks (v.S : Full d) (v.U : Full d) (v.U : Full d) 1)

theorem realFeasible_iff (P : Program N d) (z : ScalarIndex N d k → ℝ) :
    RealFeasible P z ↔ Feasible P (decode z) := by
  simp only [RealFeasible,Feasible,realPSD_iff]
  have he : (∀ i p q, (((decode z).Y i 0 : Mat d) p q).re =
      ((realTrace (carrier P (decode z) i) • (1 : Mat d)) p q).re ∧
    (((decode z).Y i 0 : Mat d) p q).im =
      ((realTrace (carrier P (decode z) i) • (1 : Mat d)) p q).im) ↔
      ∀ i, ((decode z).Y i 0 : Mat d) = realTrace (carrier P (decode z) i) • 1 := by
    constructor
    · intro h i
      ext p q
      exact Complex.ext (h i p q).1 (h i p q).2
    · intro h i p q
      rw [h i]
      exact ⟨rfl,rfl⟩
  rw [he]

theorem encoded_attainment (A : Fin N → Mat d) (H : Full d) (hd : 0 < d)
    (k : ℕ) (hk : 1 ≤ k) {c : Fin N → ℝ} (hc : ∀ i,0 ≤ c i)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ z : ScalarIndex N d k → ℝ, RealFeasible (ofAtoms A H c θ) z ∧
      objective (ofAtoms A H c θ) (decode z) = potential H A ((1:ℝ)/2^k) c θ ∧
      ∀ y : ScalarIndex N d k → ℝ, RealFeasible (ofAtoms A H c θ) y →
        objective (ofAtoms A H c θ) (decode y) ≤
          objective (ofAtoms A H c θ) (decode z) := by
  obtain ⟨v,hv,he,hmax⟩ := attained_potential A H hd k hk hc hθ
  refine ⟨encode v,?_,?_,?_⟩
  · rw [realFeasible_iff,decode_encode]
    exact hv
  · rw [decode_encode]
    exact he
  · intro y hy
    rw [decode_encode]
    exact hmax _ ((realFeasible_iff _ _).1 hy)

end HigherRankKSRuntime.SDPValue

