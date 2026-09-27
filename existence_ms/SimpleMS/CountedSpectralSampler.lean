import SimpleMS.UniformSampler
import MatrixSpencer.RealRAMCategoricalLabels
import MatrixSpencer.MSCountedSampler
import Mathlib.Data.List.ProdSigma

/-! Finite uniform sampling from the nonzero eigenspace of a materialized
orthogonal projection. The arithmetic model includes exact eigendecomposition;
the only spectral call below acts on that projection. The scan and scaling are
explicit scalar operations, and the categorical law has equal masses. -/
open Matrix MeasureTheory Set
open scoped BigOperators
noncomputable section
namespace SimpleMS.CountedSpectralSampler
open MatrixSpencer
open RealRAM.JacobiIteration (Counted)
variable {N : ℕ}
attribute [local instance] Classical.propDecidable

/-- A call to the exact-EVD primitive, with an explicit chosen diagonalization.
The unit work charge refers to the augmented arithmetic model. -/
inductive EVDExecutes (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian) :
    (Fin N → ℝ) → Matrix (Fin N) (Fin N) ℝ → ℕ → Prop where
  | evd : EVDExecutes A hA hA.eigenvalues hA.eigenvectorUnitary 1

theorem evd_spectral (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian)
    {e : Fin N → ℝ} {U : Matrix (Fin N) (Fin N) ℝ} {k : ℕ}
    (h : EVDExecutes A hA e U k) : Uᵀ*U=1 ∧ A=U*Matrix.diagonal e*Uᵀ := by
  cases h
  constructor
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      unitary.coe_star_mul_self hA.eigenvectorUnitary
  · simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial,
      RCLike.ofReal_real_eq_id,Function.comp_id] using hA.spectral_theorem

def retained (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) : List (Fin N) :=
  (List.finRange N).filter (fun j => decide ((SpectralFrame.hermitian W).eigenvalues j ≠ 0))

lemma retained_mem (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (j : Fin N) :
    j∈retained W ↔ (SpectralFrame.hermitian W).eigenvalues j ≠ 0 := by simp [retained]

def indices (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) : List (SpectralFrame.Index W) :=
  (retained W).attach.map (fun j => ⟨j.val,(retained_mem W j.val).mp j.property⟩)

lemma indices_mem (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (j : SpectralFrame.Index W) :
    j∈indices W := by
  apply List.mem_map.mpr
  refine ⟨⟨j.val,(retained_mem W j.val).mpr j.property⟩,by simp,?_⟩
  rfl

lemma indices_nodup (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) : (indices W).Nodup := by
  apply List.Nodup.map
  · intro a b h
    exact Subtype.ext (congrArg (fun z : SpectralFrame.Index W => z.val) h)
  · exact ((List.nodup_finRange N).filter _).attach

lemma indices_length (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) :
    (indices W).length=Module.finrank ℝ W := by
  have he : (indices W).toFinset=Finset.univ := by ext j; simp [indices_mem]
  rw [←List.toFinset_card_of_nodup (indices_nodup W),he,Finset.card_univ,SpectralFrame.card_index]

lemma indices_length_le (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) : (indices W).length≤N := by
  simp only [indices,List.length_map,List.length_attach]
  exact (List.length_filter_le _ _).trans_eq List.length_finRange

def table (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) : RealRAM.MSPoint.Table (UniformSampler.Draws W) where
  labels := indices W ×ˢ [false,true]
  nodup := (indices_nodup W).product (by simp)
  complete z := by cases z with | mk j b => cases b <;> simp [indices_mem]

lemma table_length (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) :
    (table W).labels.length=2*(indices W).length := by simp [table,List.length_product]; omega

def weights (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) : Counted (UniformSampler.Draws W → ℝ) :=
  ⟨fun _ => 1/(2*((indices W).length:ℝ)), 12*N+8⟩

lemma weights_value (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) :
    (weights W).value=UniformSampler.weight W := by
  funext s
  simp only [weights,indices_length,UniformSampler.weight]

def increment (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (z : UniformSampler.Draws W) :
    Counted (EuclideanSpace ℝ (Fin N)) :=
  let r := Real.sqrt (((indices W).length:ℝ)/2)
  let u := (SpectralFrame.hermitian W).eigenvectorBasis z.1.val
  ⟨if z.2 then r•u else -(r•u), 12*N+10⟩

lemma increment_value (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (z : UniformSampler.Draws W) :
    (increment W z).value=UniformSampler.increment W z := by
  simp only [increment,indices_length,UniformSampler.increment,UniformSampler.basisVector,SpectralFrame.vector]

def pick (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (u : ℝ) :=
  RealRAM.CategoricalLabels.pick (table W) (weights W).value u

lemma pick_probability (W : Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    (hW : 0<Module.finrank ℝ W) (z : UniformSampler.Draws W) :
    (volume.restrict (Ico (0:ℝ) 1)) {u | (pick W u).value=some z} =
      ENNReal.ofReal (UniformSampler.weight W z) := by
  have hp := RealRAM.CategoricalLabels.probability (table W) (weights W).value
    (fun z => by rw [weights_value]; exact (UniformSampler.weight_positive W hW z).le)
    (by rw [weights_value]; exact UniformSampler.weights_sum W hW) z
  simpa only [pick,weights_value] using hp

def drawCost (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (u : ℝ) (z : UniformSampler.Draws W) : ℕ :=
  1+(weights W).cost+20*(N+1)+(pick W u).cost+(increment W z).cost+1

lemma drawCost_le (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (u : ℝ) (z : UniformSampler.Draws W) :
    drawCost W u z≤1000*(N+1)^5 := by
  have hp := RealRAM.CategoricalLabels.pick_cost (table W) (weights W).value u
  rw [table_length] at hp
  have hl := indices_length_le W
  have hn : N+1≤(N+1)^5 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 1≤N+1 by omega) (show 1≤5 by omega)
  change (pick W u).cost≤13*(2*(indices W).length)+4 at hp
  unfold drawCost weights increment
  dsimp only
  omega

end SimpleMS.CountedSpectralSampler
