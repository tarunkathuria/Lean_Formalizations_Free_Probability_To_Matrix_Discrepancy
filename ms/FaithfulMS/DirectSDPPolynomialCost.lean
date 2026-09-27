import FaithfulMS.DirectSDPArithmetic

/-! Uniform monomial bounds for the fully materialized exact primal query. -/
noncomputable section
namespace FaithfulMS.DirectSDPArithmetic
open DirectSDP

theorem squareSize_mono {d e : ℕ} (h : d ≤ e) : squareSize d ≤ squareSize e := by
  unfold squareSize;gcongr

theorem rectangularSize_mono {m n d e : ℕ} (hm : m ≤ n) (hd : d ≤ e) :
    rectangularSize m d ≤ rectangularSize n e := by
  unfold rectangularSize;gcongr

theorem squareSize_polynomial {t : ℕ} (ht : 1 ≤ t) : squareSize t+1 ≤ 1000*t^4 := by
  have h0 : 1 ≤ t^4 := one_le_pow₀ ht
  have h2 : t^2 ≤ t^4 := Nat.pow_le_pow_right ht (by omega)
  unfold squareSize
  ring_nf
  omega

theorem rectangularSize_polynomial {t : ℕ} (ht : 1 ≤ t) : rectangularSize t t+1 ≤ 1000*t^6 := by
  have h0 : 1 ≤ t^6 := one_le_pow₀ ht
  have h2 : t^2 ≤ t^6 := Nat.pow_le_pow_right ht (by omega)
  have h3 : t^3 ≤ t^6 := Nat.pow_le_pow_right ht (by omega)
  have h4 : t^4 ≤ t^6 := Nat.pow_le_pow_right ht (by omega)
  have h5 : t^5 ≤ t^6 := Nat.pow_le_pow_right ht (by omega)
  unfold rectangularSize
  ring_nf
  omega

theorem squareCost_polynomial (P : PolynomialService) (r d : ℕ) :
    squareCost P r d ≤ (1000100+P.coefficient*1000^P.degree)*(r+d+1)^(9+4*P.degree) := by
  let t := r+d+1
  have ht : 1 ≤ t := by dsimp [t];omega
  have hd : d ≤ t := by dsimp [t];omega
  have hs : squareSize d+1 ≤ 1000*t^4 :=
    (Nat.add_le_add_right (squareSize_mono hd) 1).trans (squareSize_polynomial ht)
  have hsolve : P.coefficient*(squareSize d+1)^P.degree ≤
      P.coefficient*1000^P.degree*t^(4*P.degree) := by
    simpa only [Nat.mul_pow,←Nat.pow_mul,Nat.mul_assoc] using
      Nat.mul_le_mul_left P.coefficient (Nat.pow_le_pow_left hs P.degree)
  have hdecode : d*d*(4*d+16)+16*d^2+4 ≤ 100*t^9 := by
    have h0 : 1 ≤ t^9 := one_le_pow₀ ht
    have h2 : t^2 ≤ t^9 := Nat.pow_le_pow_right ht (by omega)
    have h3 : t^3 ≤ t^9 := Nat.pow_le_pow_right ht (by omega)
    calc
      _ ≤ t*t*(4*t+16)+16*t^2+4 := by gcongr
      _ ≤ _ := by ring_nf;omega
  have h9 : t^9 ≤ t^(9+4*P.degree) := Nat.pow_le_pow_right ht (by omega)
  have h4 : t^(4*P.degree) ≤ t^(9+4*P.degree) := Nat.pow_le_pow_right ht (by omega)
  have ha := Nat.mul_le_mul_left 1000100 h9
  have hb := Nat.mul_le_mul_left (P.coefficient*1000^P.degree) h4
  change 1000000*t^9+_+_+_+_ ≤ (1000100+P.coefficient*1000^P.degree)*t^(9+4*P.degree)
  rw [Nat.add_mul]
  omega

theorem rectangularCost_polynomial (P : PolynomialService) (r m d : ℕ) :
    rectangularCost P r m d ≤
      (1000100+P.coefficient*1000^P.degree)*(r+m+d+1)^(11+6*P.degree) := by
  let t := r+m+d+1
  have ht : 1 ≤ t := by dsimp [t];omega
  have hd : d ≤ t := by dsimp [t];omega
  have hm : m ≤ t := by dsimp [t];omega
  have hs : rectangularSize m d+1 ≤ 1000*t^6 :=
    (Nat.add_le_add_right (rectangularSize_mono hm hd) 1).trans (rectangularSize_polynomial ht)
  have hsolve : P.coefficient*(rectangularSize m d+1)^P.degree ≤
      P.coefficient*1000^P.degree*t^(6*P.degree) := by
    simpa only [Nat.mul_pow,←Nat.pow_mul,Nat.mul_assoc] using
      Nat.mul_le_mul_left P.coefficient (Nat.pow_le_pow_left hs P.degree)
  have hdecode : d*d*(4*d+16)+4*(m+3)*d^2+4 ≤ 100*t^11 := by
    have h0 : 1 ≤ t^11 := one_le_pow₀ ht
    have h2 : t^2 ≤ t^11 := Nat.pow_le_pow_right ht (by omega)
    have h3 : t^3 ≤ t^11 := Nat.pow_le_pow_right ht (by omega)
    calc
      _ ≤ t*t*(4*t+16)+4*(t+3)*t^2+4 := by gcongr
      _ ≤ _ := by ring_nf;omega
  have h11 : t^11 ≤ t^(11+6*P.degree) := Nat.pow_le_pow_right ht (by omega)
  have h6 : t^(6*P.degree) ≤ t^(11+6*P.degree) := Nat.pow_le_pow_right ht (by omega)
  have ha := Nat.mul_le_mul_left 1000100 h11
  have hb := Nat.mul_le_mul_left (P.coefficient*1000^P.degree) h6
  change 1000000*t^11+_+_+_+_ ≤ (1000100+P.coefficient*1000^P.degree)*t^(11+6*P.degree)
  rw [Nat.add_mul]
  omega

end FaithfulMS.DirectSDPArithmetic
