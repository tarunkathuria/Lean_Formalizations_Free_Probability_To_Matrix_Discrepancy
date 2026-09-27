import MatrixSpencer.KSEighthCountedPreparation
import MatrixSpencer.KSJacobiPolynomialBounds
import MatrixSpencer.KSEighthConvexReportMagnitude

/-!
# Counted finite Hessian and covariance for the eighth convex walk

Live lookup is the existing ordered list lookup/index search. The conservative
charge allows a full scan of the original labels for each extended coordinate.
Every entry makes exactly four counted retained-owner queries. The subsequent
matrix symmetrization, scaling, off-diagonal energy and capped-simplex/Jacobi
projection are counted explicitly. The natural Jacobi count is implemented by
the bounded scalar ceiling loop; the supplied polynomial cap is proved to
cover the actual count before equality to the old covariance is asserted.

Input-only scalar budgets are supplied as precomputed data. The extra constant
charge in `hessian` covers mesh/tolerance scalar arithmetic from those budgets
and the current live count; it does not charge recomputing Taylor bounds.
-/
open Matrix Set
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSEighthCountedHessian
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
open RealRAM RealRAM.JacobiIteration KSEighthLiveEnumeration
open KSEighthCountedPreparation KSEighthHessianQueries
variable {N d : ℕ}
attribute [local instance] Classical.propDecidable

def labelsScan (x : Fin N → ℝ) : List (Fin N) → Counted (List (Fin N))
  | [] => ⟨[],1⟩
  | i::is =>
    let a := KSCappedSimplex.absolute (x i)
    let r := labelsScan x is
    ⟨if a.value<1/8 then i::r.value else r.value,a.cost+r.cost+6⟩

theorem labelsScan_value (x : Fin N → ℝ) (is : List (Fin N)) :
    (labelsScan x is).value=is.filter (fun i => decide (|x i|<(1/8:ℝ))) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [labelsScan,KSCappedSimplex.absolute_value,ih,List.filter_cons,decide_eq_true_eq]

theorem labelsScan_cost (x : Fin N → ℝ) (is : List (Fin N)) :
    (labelsScan x is).cost≤20*is.length+1 := by
  induction is with
  | nil => simp [labelsScan]
  | cons i is ih =>
    have ha := KSCappedSimplex.absolute_cost (x i)
    simp only [labelsScan,List.length_cons]
    omega

def liveLabels (x : Fin N → ℝ) : Counted (List (Fin N)) :=
  let l := labelsScan x (List.finRange N)
  ⟨l.value,l.cost+3*N+1⟩

theorem liveLabels_value (x : Fin N → ℝ) : (liveLabels x).value=labels x :=
  labelsScan_value x _

theorem liveLabels_cost (x : Fin N → ℝ) : (liveLabels x).cost≤23*N+2 := by
  have h := labelsScan_cost x (List.finRange N)
  simp only [List.length_finRange] at h
  dsimp [liveLabels]
  omega

/-- A stored ordered live list implements both forward and inverse lookup.
Each inverse lookup is charged for scanning at most all `N` original labels. -/
def face (x : Fin N → ℝ) (z : KSEighthFacePotential.Space x) : Counted (Fin N → ℝ) :=
  let l := liveLabels x
  ⟨fun i => x i+Real.sqrt (1-x i^2)*extend x z i,
    l.cost+N*(12*N+50)+1⟩

theorem face_value (x : Fin N → ℝ) (z : KSEighthFacePotential.Space x) :
    (face x z).value=KSEighthLiveCoordinates.face x z := by
  funext i
  simp only [face,KSEighthLiveCoordinates.face,KSEighthLiveCoordinates.weightedMap_apply]

theorem face_cost (x : Fin N → ℝ) (z : KSEighthFacePotential.Space x) :
    (face x z).cost≤100*(N+1)^2 := by
  have h := liveLabels_cost x
  dsimp only [face]
  nlinarith

def faceReport (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (θ η : ℝ) (hd : 0<d) (q : Queries O v θ hd) (x : Fin N → ℝ)
    (z : KSEighthFacePotential.Space x) : Counted ℝ :=
  let y := face x z
  let r := q.retained (KSPotentialModels.live (1/8) x) (queryTolerance v θ η x) y.value
  ⟨r.value,y.cost+r.cost+3*N+2⟩

theorem faceReport_value (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (θ η : ℝ) (hd : 0<d) (q : Queries O v θ hd) (x : Fin N → ℝ)
    (z : KSEighthFacePotential.Space x) :
    (faceReport O v θ η hd q x z).value=KSEighthConvexValue.faceReport O v θ η hd x z := by
  simp only [faceReport,q.retained_value,face_value,KSEighthConvexValue.faceReport]

theorem faceReport_cost (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (θ η : ℝ) (hd : 0<d) (q : Queries O v θ hd) {x : Fin N → ℝ}
    (hx : x∈ksCube (1/8)) {Q : ℕ}
    (hQ : ∀y∈ksCube (1/4),
      (q.retained (KSPotentialModels.live (1/8) x) (queryTolerance v θ η x) y).cost≤Q)
    (z : KSEighthFacePotential.Space x) (hz : ‖z‖≤1/16) :
    (faceReport O v θ η hd q x z).cost≤Q+110*(N+1)^2 := by
  have hr := hQ _ (query_ball_cube hx z hz)
  rw [←face_value x z] at hr
  have hf := face_cost x z
  dsimp only [faceReport]
  nlinarith

def stencil {m : ℕ} (report : KSNumericalHessian.Space m → Counted ℝ)
    (t : ℝ) (i j : Fin m) : Counted ℝ :=
  let pp := report (t • (KSNumericalHessian.coordinate i+KSNumericalHessian.coordinate j))
  let pm := report (t • (KSNumericalHessian.coordinate i-KSNumericalHessian.coordinate j))
  let mp := report (-(t • (KSNumericalHessian.coordinate i-KSNumericalHessian.coordinate j)))
  let mm := report (-(t • (KSNumericalHessian.coordinate i+KSNumericalHessian.coordinate j)))
  ⟨(pp.value-pm.value-mp.value+mm.value)/(4*t^2),
    pp.cost+pm.cost+mp.cost+mm.cost+40*m+40⟩

theorem stencil_value {m : ℕ} (report : KSNumericalHessian.Space m → Counted ℝ)
    (t : ℝ) (i j : Fin m) :
    (stencil report t i j).value=KSNumericalHessian.matrixReport (fun z=>(report z).value) 0 t i j := by
  rw [KSNumericalHessian.matrixReport_queries]
  have he1 : (0:KSNumericalHessian.Space m)+t•KSNumericalHessian.coordinate i+t•KSNumericalHessian.coordinate j=
      t•(KSNumericalHessian.coordinate i+KSNumericalHessian.coordinate j) := by simp [smul_add]
  have he2 : (0:KSNumericalHessian.Space m)+t•KSNumericalHessian.coordinate i-t•KSNumericalHessian.coordinate j=
      t•(KSNumericalHessian.coordinate i-KSNumericalHessian.coordinate j) := by simp [smul_sub]
  have he3 : (0:KSNumericalHessian.Space m)-t•KSNumericalHessian.coordinate i+t•KSNumericalHessian.coordinate j=
      -(t•(KSNumericalHessian.coordinate i-KSNumericalHessian.coordinate j)) := by simp [smul_sub,neg_sub]; abel
  have he4 : (0:KSNumericalHessian.Space m)-t•KSNumericalHessian.coordinate i-t•KSNumericalHessian.coordinate j=
      -(t•(KSNumericalHessian.coordinate i+KSNumericalHessian.coordinate j)) := by simp [smul_add,neg_add_rev]; abel
  simp only [stencil,he1,he2,he3,he4]

theorem stencil_cost {m : ℕ} (report : KSNumericalHessian.Space m → Counted ℝ)
    {t : ℝ} (ht : 0≤t) (htR : t≤1/32) {Q : ℕ}
    (hQ : ∀z,‖z‖≤1/16→(report z).cost≤Q) (i j : Fin m) :
    (stencil report t i j).cost≤4*Q+40*m+40 := by
  have hp : ‖t•(KSNumericalHessian.coordinate i+KSNumericalHessian.coordinate j)‖≤(1/16:ℝ) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht]
    have hh := mul_le_mul_of_nonneg_left (coordinate_add_norm i j) ht
    linarith
  have hm : ‖t•(KSNumericalHessian.coordinate i-KSNumericalHessian.coordinate j)‖≤(1/16:ℝ) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht]
    have hh := mul_le_mul_of_nonneg_left (coordinate_sub_norm i j) ht
    linarith
  have h1 := hQ _ hp
  have h2 := hQ _ hm
  have h3 := hQ (-(t•(KSNumericalHessian.coordinate i-KSNumericalHessian.coordinate j))) (by simpa only [norm_neg] using hm)
  have h4 := hQ (-(t•(KSNumericalHessian.coordinate i+KSNumericalHessian.coordinate j))) (by simpa only [norm_neg] using hp)
  dsimp only [stencil]
  omega

def hessian (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (θ η : ℝ) (hd : 0<d) (q : Queries O v θ hd) (x : Fin N → ℝ) :
    Counted (Matrix (Fin (count x)) (Fin (count x)) ℝ) :=
  let e := stencil (faceReport O v θ η hd q x) (queryMesh v θ η x)
  ⟨(1/2:ℝ) • KSMatrixEntryAccuracy.symmetrize (fun i j=>(e i j).value),
    (∑i,∑j,((e i j).cost+16))+50*(count x)+200⟩

theorem hessian_value (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (θ η : ℝ) (hd : 0<d) (q : Queries O v θ hd) (x : Fin N → ℝ) :
    (hessian O v θ η hd q x).value=KSEighthConvexController.hessianReport O v θ η hd x := by
  simp only [hessian,stencil_value,faceReport_value,KSEighthConvexController.hessianReport]

theorem hessian_cost (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    {θ η : ℝ} (hθ : 0<θ) (hη : 0<η) (hd : 0<d) (q : Queries O v θ hd)
    {x : Fin N → ℝ} (hx : x∈ksCube (1/8)) (hk : 0<count x) {Q : ℕ}
    (hQ : ∀y∈ksCube (1/4),
      (q.retained (KSPotentialModels.live (1/8) x) (queryTolerance v θ η x) y).cost≤Q) :
    (hessian O v θ η hd q x).cost≤1000*(N+1)^4*(Q+1) := by
  have he := stencil_cost (faceReport O v θ η hd q x)
    (queryMesh_pos v hθ hη hd x hk).le (queryMesh_le v θ η x)
    (faceReport_cost O v θ η hd q hx hQ)
  have hs : (∑i,∑j,((stencil (faceReport O v θ η hd q x) (queryMesh v θ η x) i j).cost+16))≤
      (count x)^2*(4*(Q+110*(N+1)^2)+40*(count x)+56) := by
    calc
      _ ≤ ∑_i : Fin (count x),∑_j : Fin (count x),(4*(Q+110*(N+1)^2)+40*(count x)+56) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        have hh := he i j
        omega
      _ = _ := by simp; ring
  have hkN := KSEighthManuscriptMovement.count_le x
  dsimp only [hessian]
  calc
    _ ≤ (count x)^2*(4*(Q+110*(N+1)^2)+40*(count x)+56)+50*(count x)+200 := by omega
    _ ≤ N^2*(4*(Q+110*(N+1)^2)+40*N+56)+50*N+200 := by gcongr
    _ ≤ _ := by nlinarith [Nat.zero_le (N^2),Nat.zero_le (N^3),Nat.zero_le (N^4),
      Nat.zero_le (Q*N),Nat.zero_le (Q*N^2),Nat.zero_le (Q*N^3),Nat.zero_le (Q*N^4)]

end MatrixSpencer.KSEighthCountedHessian
