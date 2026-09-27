import MatrixSpencer.RealRAMCategoricalLabels
import MatrixSpencer.RealRAMMSSampling
import MatrixSpencer.MSCountedSampler
import Mathlib.Data.List.ProdSigma


open Matrix MeasureTheory Set
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.MSCountedCategorical
open RealRAM.JacobiIteration (Counted)
open RealRAM.MSSampling
open MSCountedSampler MSManuscriptNumericalSamplerData
variable {k : ℕ}

def table (Q : Matrix (Fin k) (Fin k) ℝ) : RealRAM.MSPoint.Table (Draws Q) where
  labels := (List.finRange (count Q)) ×ˢ [false,true]
  nodup := (List.nodup_finRange _).product (by simp)
  complete z := by cases z with | mk j b => cases b <;> simp

theorem table_length (Q : Matrix (Fin k) (Fin k) ℝ) : (table Q).labels.length=2*count Q := by
  simp [table,List.length_product]; omega

def pick (Q : Matrix (Fin k) (Fin k) ℝ) (u : ℝ) : Counted (Option (Draws Q)) :=
  RealRAM.CategoricalLabels.pick (table Q) (RealRAM.MSSampling.weights Q).value u

theorem pick_probability (Q : Matrix (Fin k) (Fin k) ℝ) (hQ : Q.PosSemidef) (hq : 0<realTrace Q)
    (z : Draws Q) :
    (volume.restrict (Ico (0:ℝ) 1)) {u | (pick Q u).value=some z}=ENNReal.ofReal (weight Q z) := by
  have h:=RealRAM.CategoricalLabels.probability (table Q) (RealRAM.MSSampling.weights Q).value
    (fun a => by rw [weights_value]; exact (weight_pos Q hq a).le)
    (by simp only [weights_value]; exact weight_sum Q hQ hq) z
  simpa only [weights_value] using h

def drawCost (Q : Matrix (Fin k) (Fin k) ℝ) (u : ℝ) (z : Draws Q) : ℕ :=
  (RealRAM.MSSampling.weights Q).cost+20*(k+1)+(pick Q u).cost+
    (RealRAM.MSSampling.increment Q z).cost+1

theorem drawCost_le (Q : Matrix (Fin k) (Fin k) ℝ) (u : ℝ) (z : Draws Q) :
    drawCost Q u z≤1000*(k+1)^5 := by
  have hw:=RealRAM.MSSampling.weights_cost Q
  have hi:=RealRAM.MSSampling.increment_cost Q z
  have hp:=RealRAM.CategoricalLabels.pick_cost (table Q) (RealRAM.MSSampling.weights Q).value u
  rw [table_length] at hp
  have hc:=count_le Q
  have hk : k+1≤(k+1)^5 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 1≤k+1 by omega) (show 1≤5 by omega)
  change (pick Q u).cost≤13*(2*count Q)+4 at hp
  unfold drawCost
  omega

def implementation (Q : Matrix (Fin k) (Fin k) ℝ) (hQ : Q.PosSemidef) (hq : 0<realTrace Q) :
    Implementation (sample Q hQ hq) where
  Executes z out cost draws := ∃u, u∈Ico (0:ℝ) 1 ∧ (pick Q u).value=some z ∧
    out=(RealRAM.MSSampling.increment Q z).value ∧ cost=drawCost Q u z ∧ draws=1
  result z out cost draws h := by
    obtain ⟨u,hu,hp,ho,hc,hr⟩:=h
    exact ho.trans (RealRAM.MSSampling.increment_value Q z)
  complete z := by
    obtain ⟨u,hu,hp⟩:=RealRAM.CategoricalLabels.complete (table Q) (RealRAM.MSSampling.weights Q).value
      (fun a => by rw [weights_value]; exact weight_pos Q hq a)
      (by simp only [weights_value]; exact weight_sum Q hQ hq) z
    refine ⟨drawCost Q u z,1,u,hu,hp,?_,rfl,rfl⟩
    exact (RealRAM.MSSampling.increment_value Q z).symm

theorem implementation_bounded (Q : Matrix (Fin k) (Fin k) ℝ) (hQ : Q.PosSemidef) (hq : 0<realTrace Q) :
    Bounded (implementation Q hQ hq) (1000*(k+1)^5) 1 := by
  intro z out cost draws h
  obtain ⟨u,hu,hp,ho,rfl,rfl⟩:=h
  exact ⟨drawCost_le Q u z,le_rfl⟩

end MatrixSpencer.MSCountedCategorical
