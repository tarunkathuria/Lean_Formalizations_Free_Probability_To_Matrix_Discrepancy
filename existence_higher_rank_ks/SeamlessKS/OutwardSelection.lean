import SeamlessKS.Proposals
import SeamlessKS.Value

/-! The actual finite local value tests and their soundness.
The selected label is the least successful original label. -/
open Set
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace SeamlessKS.OutwardSelection
open MatrixSpencer SeamlessKS.State SeamlessKS.StatePotential SeamlessKS.Proposals
variable {N : ℕ} {ρ : ℝ} {d : ℕ} [Nonempty (Fin d)]

attribute [local instance] Classical.propDecidable

def candidates (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (θ ζ ν a : ℝ) (s : PreparedState N ρ) : Finset (Fin N) :=
  Finset.univ.filter (fun i => |s.coeff i|<1 ∧
    Value.report O v 0 θ ζ ν (outwardVector s.coeff i a)-
      Value.report O v 0 θ ζ ν s.coeff≤2*ν)

def select (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (θ ζ ν a : ℝ) (s : PreparedState N ρ) : Option (Fin N) :=
  if hn : (candidates O v θ ζ ν a s).Nonempty then
    some ((candidates O v θ ζ ν a s).min' hn) else none

theorem selected_mem (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (θ ζ ν a : ℝ) (s : PreparedState N ρ) (i : Fin N)
    (hi : select O v θ ζ ν a s=some i) : i∈candidates O v θ ζ ν a s := by
  unfold select at hi
  split_ifs at hi with hn
  · cases Option.some.inj hi
    exact Finset.min'_mem _ hn

theorem selected_live (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (θ ζ ν a : ℝ) (s : PreparedState N ρ) (i : Fin N)
    (hi : select O v θ ζ ν a s=some i) : |s.coeff i|<1 :=
  ((Finset.mem_filter.mp (selected_mem O v θ ζ ν a s i hi)).2).1

theorem none_rejects (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (θ ζ ν a : ℝ) (s : PreparedState N ρ)
    (hn : select O v θ ζ ν a s=none) (i : Fin N) (hi : |s.coeff i|<1) :
    2*ν<Value.report O v 0 θ ζ ν (outwardVector s.coeff i a)-
      Value.report O v 0 θ ζ ν s.coeff := by
  have he : ¬(candidates O v θ ζ ν a s).Nonempty := by
    intro hc
    simp only [select,dif_pos hc] at hn
    contradiction
  have hnot : i∉candidates O v θ ζ ν a s := fun hm => he ⟨i,hm⟩
  simp only [candidates,Finset.mem_filter,Finset.mem_univ,true_and,hi,true_and] at hnot
  exact lt_of_not_ge hnot

theorem selected_drift (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    {θ ζ ν a : ℝ} (hθ : 0<θ) (hν : 0<ν) (hρ : 0<ρ) (ha : 0≤a) (har : a≤ρ/8)
    (s : PreparedState N ρ) (i : Fin N) (hi : select O v θ ζ ν a s=some i) :
    potential v θ ζ (outwardMove hρ s i (selected_live O v θ ζ ν a s i hi) a ha har)≤
      potential v θ ζ s.toCubeState+4*ν := by
  let hiLive := selected_live O v θ ζ ν a s i hi
  let y := outwardMove hρ s i hiLive a ha har
  have hold := Value.state_report_accuracy O v (ζ := ζ) hθ hν s.toCubeState
  have hnew := Value.report_accuracy O v 0 (ζ := ζ) hθ hν y.coeff y.cube
  have haccept := ((Finset.mem_filter.mp (selected_mem O v θ ζ ν a s i hi)).2).2
  exact Value.accepted_local_increase hold hnew haccept

theorem none_true_increase (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    {θ ζ ν a : ℝ} (hθ : 0<θ) (hν : 0<ν) (hρ : 0<ρ) (ha : 0≤a) (har : a≤ρ/8)
    (s : PreparedState N ρ) (hn : select O v θ ζ ν a s=none)
    (i : Fin N) (hi : |s.coeff i|<1) :
    potential v θ ζ s.toCubeState<
      KSDebitPotential.potential (signedSum v (outwardVector s.coeff i a)) 0
        v (SourceTransport.smoothWeights ζ (outwardVector s.coeff i a)) θ := by
  let y := outwardMove hρ s i hi a ha har
  exact Value.rejected_local_increases (Value.state_report_accuracy O v hθ hν s.toCubeState)
    (Value.report_accuracy O v 0 hθ hν y.coeff y.cube)
    (none_rejects O v θ ζ ν a s hn i hi)

end SeamlessKS.OutwardSelection
