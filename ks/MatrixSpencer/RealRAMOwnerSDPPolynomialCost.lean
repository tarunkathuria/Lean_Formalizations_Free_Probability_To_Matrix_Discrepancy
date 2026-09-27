import MatrixSpencer.RealRAMOwnerSDPSetup

/-! A deliberately coarse single-monomial bound for direct SDP construction. -/
namespace MatrixSpencer.RealRAM.OwnerSDPSetup
open OwnerSDPBlocks

theorem setupCost_mono {r s d e : ℕ} (hr : r≤s) (hd : d≤e) : setupCost r d≤setupCost s e := by
  unfold setupCost blockBound objectiveBound sourceBound productBound
  gcongr

theorem setupCost_polynomial (r d : ℕ) : setupCost r d≤1000000*(r+d+1)^9 := by
  let t:=r+d+1
  have ht : 1≤t := by dsimp [t];omega
  have h0 : 1≤t^9 := one_le_pow₀ ht
  have h1 : t≤t^9 := by simpa using Nat.pow_le_pow_right ht (show 1≤9 by omega)
  have h2 : t^2≤t^9 := Nat.pow_le_pow_right ht (by omega)
  have h3 : t^3≤t^9 := Nat.pow_le_pow_right ht (by omega)
  have h4 : t^4≤t^9 := Nat.pow_le_pow_right ht (by omega)
  have h5 : t^5≤t^9 := Nat.pow_le_pow_right ht (by omega)
  have h6 : t^6≤t^9 := Nat.pow_le_pow_right ht (by omega)
  have h7 : t^7≤t^9 := Nat.pow_le_pow_right ht (by omega)
  have h8 : t^8≤t^9 := Nat.pow_le_pow_right ht (by omega)
  apply (setupCost_mono (show r≤t by dsimp [t];omega) (show d≤t by dsimp [t];omega)).trans
  change setupCost t t≤1000000*t^9
  unfold setupCost blockBound objectiveBound sourceBound productBound
  ring_nf
  omega

end MatrixSpencer.RealRAM.OwnerSDPSetup
