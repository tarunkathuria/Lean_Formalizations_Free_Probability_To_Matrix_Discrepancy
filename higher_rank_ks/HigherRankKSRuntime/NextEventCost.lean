import HigherRankKSRuntime.NextEvent

/-! Counts all value reports, scans, tangent-frame arithmetic, EVD, and
zero-extension performed by the local controller. -/
noncomputable section
namespace HigherRankKSRuntime.NextEvent
open AugmentedHigherRankKS ActiveEnumeration ControllerLoop Tangent
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
variable {N : ℕ}

def queryWork (N Q : ℕ) : ℕ := Q + 50*(N+1)^3+100*(N+1)^2

def walkWork (N Q : ℕ) : ℕ :=
  N^2*(4*queryWork N Q+100*(N+1)+18)+1000*(N+1)^5+2*queryWork N Q+3*N+25+
    20*(N+1)^2+50*(N+1)^3+100*(N+1)^2

def eventWork (N Q : ℕ) : ℕ :=
  8*N+(13*N+2)+Q+N*(Q+3)+walkWork N Q

theorem afterRejection_work (query : EpochState (Fin N) → Counted ℝ)
    (a t h : ℝ) (z : EpochState (Fin N)) {Q : ℕ}
    (hQ : ∀ y, (query y).cost ≤ Q) :
    (afterRejection query a t h z).cost ≤ walkWork N Q := by
  have hchart (y : MatrixSpencer.KSNumericalHessian.Space (count z)) :
      (chartReport query a z y).cost ≤ queryWork N Q := by
    have he := Execution.extension_cost z y
    have hq := hQ (movement a z (Execution.extension z y).value 1)
    simp only [chartReport,queryWork]
    omega
  have hp := Execution.positions_cost z
  by_cases hr : 0 < (Frame.canonical (count z) (restrictedPosition z)).rank
  · have hw := WalkExecution.compute_cost (chartReport query a z)
      (restrictedPosition z) t h hr (fun y _ => hchart y) (fun y _ => hchart y)
    have he := Execution.extension_cost z (WalkExecution.compute (chartReport query a z)
      (restrictedPosition z) t h hr).value
    have hm := count_le z
    have hw' : (WalkExecution.compute (chartReport query a z)
        (restrictedPosition z) t h hr).cost ≤
        N^2*(4*queryWork N Q+100*(N+1)+18)+1000*(N+1)^5+2*queryWork N Q+3*N+25 := by
      apply hw.trans
      gcongr
    simp only [afterRejection,dif_pos hr,walkWork]
    omega
  · simp only [afterRejection,dif_neg hr,walkWork]
    omega

theorem compute_work (query : EpochState (Fin N) → Counted ℝ)
    (a step h t p0 ρ ζ : ℝ) (z : EpochState (Fin N)) {Q : ℕ}
    (hQ : ∀ y, (query y).cost ≤ Q) :
    (compute query a step h t p0 ρ ζ z).cost ≤ eventWork N Q := by
  have hc := CleanupScan.scan_work_le z ρ ζ (List.finRange N)
  simp only [List.length_finRange] at hc
  have ht := Execution.table_cost z
  have hb := hQ z
  have hp := PreparationScan.scan_work_le (fun i => query (prepareOwner a z i step))
    (query z).value (-(step*p0/(4*a))) (labels z) (fun i _ => hQ _)
  have hm := count_le z
  have hp' : (PreparationScan.scan (fun i => query (prepareOwner a z i step))
      (query z).value (-(step*p0/(4*a))) (labels z)).cost ≤ N*(Q+3) :=
    hp.trans (Nat.mul_le_mul_right (Q+3) hm)
  have hw := afterRejection_work query a t h z hQ
  have hbase : 100*(N+1)^2 ≤ walkWork N Q := by unfold walkWork; omega
  generalize he : (CleanupScan.scan z ρ ζ (List.finRange N)).value = clean
  cases clean with
  | some e =>
    simp only [compute,he]
    unfold eventWork
    omega
  | none =>
    by_cases hzero : count z = 0
    · simp only [compute,he,hzero,↓reduceIte]
      unfold eventWork
      omega
    · generalize hprep : (PreparationScan.scan (fun i => query (prepareOwner a z i step))
        (query z).value (-(step*p0/(4*a))) (labels z)).value = prep
      cases prep with
      | some i =>
        simp only [compute,he,hzero,↓reduceIte,hprep]
        unfold eventWork
        omega
      | none =>
        simp only [compute,he,hzero,↓reduceIte,hprep]
        unfold eventWork
        omega
end HigherRankKSRuntime.NextEvent
