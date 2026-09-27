import SimpleMS.CountedSpectralSampler
import MatrixSpencer.RealRAMMSCleanup

/-! Materialization of the high spectral projection from one exact-EVD call,
an eigenvalue comparison scan, and two scalar matrix multiplication circuits. -/
open Matrix
noncomputable section
namespace SimpleMS.CountedHighProjection
open MatrixSpencer
open RealRAM.JacobiIteration (Counted Mat)
variable {N : ℕ}
attribute [local instance] Classical.propDecidable

def hermitianValue (C : Mat N) (hC : C.IsHermitian) : Counted (Mat N) :=
  let U : Mat N := hC.eigenvectorUnitary
  let D : Mat N := Matrix.diagonal (fun j => if (1/2:ℝ)≤hC.eigenvalues j then 1 else 0)
  let a := RealRAM.MSCleanup.multiply U D
  let b := RealRAM.MSCleanup.multiply a.value Uᵀ
  ⟨b.value,1+8*N+4*N^2+a.cost+b.cost+5⟩

lemma hermitianValue_value (C : Mat N) (hC : C.IsHermitian) :
    (hermitianValue C hC).value=highProjection C := by
  simp only [hermitianValue,RealRAM.MSCleanup.multiply_value,highProjection_eq C hC,
    RealSpectralCutoff.high,RealSpectralCutoff.spectralMatrix,Matrix.conjTranspose_eq_transpose_of_trivial]

lemma hermitianValue_cost (C : Mat N) (hC : C.IsHermitian) :
    (hermitianValue C hC).cost≤700*(N+1)^3 := by
  let U : Mat N := hC.eigenvectorUnitary
  let D : Mat N := Matrix.diagonal (fun j => if (1/2:ℝ)≤hC.eigenvalues j then 1 else 0)
  have ha := RealRAM.MSCleanup.multiply_cost U D
  have hb := RealRAM.MSCleanup.multiply_cost (RealRAM.MSCleanup.multiply U D).value Uᵀ
  have hh : (N+N+N+1)^3≤27*(N+1)^3 := by
    calc _≤(3*(N+1))^3 := Nat.pow_le_pow_left (by omega) _
         _=_ := by ring
  have h1 : 1≤(N+1)^3 := Nat.one_le_pow _ _ (by omega)
  have h2 : N^2≤(N+1)^3 := (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hn : N≤(N+1)^3 := by nlinarith
  change 1+8*N+4*N^2+(RealRAM.MSCleanup.multiply U D).cost+
    (RealRAM.MSCleanup.multiply (RealRAM.MSCleanup.multiply U D).value Uᵀ).cost+5≤_
  omega

/-- The branch test is the finite entrywise symmetry comparison; a false
branch returns the zero matrix, matching the totalized mathematical definition. -/
def value (C : Mat N) : Counted (Mat N) :=
  if hC : C.IsHermitian then
    let p := hermitianValue C hC
    ⟨p.value,p.cost+4*N^2+5⟩
  else ⟨0,6*N^2+5⟩

lemma value_value (C : Mat N) : (value C).value=highProjection C := by
  unfold value
  split_ifs with hC
  · exact hermitianValue_value C hC
  · simp [highProjection,hC]

lemma value_cost (C : Mat N) : (value C).cost≤720*(N+1)^3 := by
  have h2 : N^2≤(N+1)^3 := (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have h1 : 1≤(N+1)^3 := Nat.one_le_pow _ _ (by omega)
  unfold value
  split_ifs with hC
  · have hp := hermitianValue_cost C hC
    dsimp only
    omega
  · dsimp only
    omega

lemma evd_execution (C : Mat N) (hC : C.IsHermitian) :
    CountedSpectralSampler.EVDExecutes C hC hC.eigenvalues hC.eigenvectorUnitary 1 := .evd

end SimpleMS.CountedHighProjection
