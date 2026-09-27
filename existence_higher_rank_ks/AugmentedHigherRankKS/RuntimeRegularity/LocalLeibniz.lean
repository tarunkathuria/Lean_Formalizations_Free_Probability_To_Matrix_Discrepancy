import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Data.Nat.Choose.Cast

/-! Local quantitative Leibniz bounds. The hypotheses concern genuine
smoothness at the point, and the conclusion concerns genuine derivatives. -/

open Set Filter
open scoped Topology BigOperators

namespace HigherRankKSRuntime.LocalLeibniz

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_iteratedDeriv_smul_le {f : ℝ → ℝ} {g : ℝ → F}
    {k : ℕ} {x : ℝ} (hf : ContDiffAt ℝ k f x) (hg : ContDiffAt ℝ k g x) :
    ‖iteratedDeriv k (fun t => f t • g t) x‖ ≤
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedDeriv i f x‖ * ‖iteratedDeriv (k - i) g x‖ := by
  obtain ⟨s, hs, hxs, hfs⟩ := hf.contDiffOn' le_rfl (by simp)
  obtain ⟨t, ht, hxt, hgt⟩ := hg.contDiffOn' le_rfl (by simp)
  let u := s ∩ t
  have hu : IsOpen u := hs.inter ht
  have hxu : x ∈ u := ⟨hxs, hxt⟩
  have hfu : ContDiffOn ℝ k f u := hfs.mono (by intro y hy; exact ⟨by simp, hy.1⟩)
  have hgu : ContDiffOn ℝ k g u := hgt.mono (by intro y hy; exact ⟨by simp, hy.2⟩)
  have hh := norm_iteratedFDerivWithin_smul_le hfu hgu hu.uniqueDiffOn hxu
    (le_rfl : (k : WithTop ℕ∞) ≤ k)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hu.uniqueDiffOn (hf.smul hg) hxu,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hu.uniqueDiffOn
      (hf.of_le (by exact_mod_cast hik)) hxu,
    iteratedFDerivWithin_eq_iteratedFDeriv hu.uniqueDiffOn
      (hg.of_le (by exact_mod_cast Nat.sub_le k i)) hxu,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv]

theorem factorial_convolution (k : ℕ) (b p : ℝ) :
    (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
      ((i.factorial : ℝ) * b ^ i * p) *
      (((k - i).factorial : ℝ) * b ^ (k - i))) =
      (k + 1) * (k.factorial : ℝ) * b ^ k * p := by
  calc
    _ = ∑ _i ∈ Finset.range (k + 1), (k.factorial : ℝ) * b ^ k * p := by
      apply Finset.sum_congr rfl
      intro i hi
      have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hc : (k.choose i : ℝ) * (i.factorial : ℝ) *
          ((k - i).factorial : ℝ) = (k.factorial : ℝ) := by
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial hik
      have hp : b ^ i * b ^ (k - i) = b ^ k := by
        rw [← pow_add, Nat.add_sub_of_le hik]
      calc
        _ = ((k.choose i : ℝ) * (i.factorial : ℝ) * ((k - i).factorial : ℝ)) *
            (b ^ i * b ^ (k - i)) * p := by ring
        _ = _ := by rw [hc, hp]
    _ = _ := by simp; ring

theorem norm_iteratedDeriv_smul_factorial {f : ℝ → ℝ} {g : ℝ → F}
    {k : ℕ} {x b p : ℝ} (hf : ContDiffAt ℝ k f x) (hg : ContDiffAt ℝ k g x)
    (hb : 0 ≤ b) (hp : 0 ≤ p)
    (hfbound : ∀ i ≤ k, ‖iteratedDeriv i f x‖ ≤ (i.factorial : ℝ) * b ^ i * p)
    (hgbound : ∀ i ≤ k, ‖iteratedDeriv i g x‖ ≤ (i.factorial : ℝ) * b ^ i) :
    ‖iteratedDeriv k (fun t => f t • g t) x‖ ≤
      (k + 1) * (k.factorial : ℝ) * b ^ k * p := by
  refine (norm_iteratedDeriv_smul_le hf hg).trans ?_
  rw [← factorial_convolution k b p]
  apply Finset.sum_le_sum
  intro i hi
  have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (hfbound i hik) (Nat.cast_nonneg _)
  · exact hgbound (k - i) (Nat.sub_le _ _)
  · exact norm_nonneg _
  · positivity

theorem geometric_convolution_le {d e : ℝ} (hd : 0 ≤ d) (he : 0 ≤ e) (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), d ^ i * e ^ (k - i)) ≤ (d + e) ^ k := by
  rw [add_pow]
  apply Finset.sum_le_sum
  intro i hi
  have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hc : (1 : ℝ) ≤ (k.choose i : ℝ) := by
    exact_mod_cast Nat.choose_pos hik
  calc
    d ^ i * e ^ (k - i) = d ^ i * e ^ (k - i) * 1 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hc (by positivity)

theorem norm_iteratedDeriv_smul_geometric {f : ℝ → ℝ} {g : ℝ → F}
    {k : ℕ} {x d e p : ℝ} (hf : ContDiffAt ℝ k f x) (hg : ContDiffAt ℝ k g x)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hp : 0 ≤ p)
    (hfbound : ∀ i ≤ k, ‖iteratedDeriv i f x‖ ≤ (i.factorial : ℝ) * d ^ i * p)
    (hgbound : ∀ i ≤ k, ‖iteratedDeriv i g x‖ ≤ (i.factorial : ℝ) * e ^ i) :
    ‖iteratedDeriv k (fun t => f t • g t) x‖ ≤
      (k.factorial : ℝ) * (d + e) ^ k * p := by
  calc
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ((i.factorial : ℝ) * d ^ i * p) *
        (((k - i).factorial : ℝ) * e ^ (k - i)) := by
      refine (norm_iteratedDeriv_smul_le hf hg).trans ?_
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hfbound i hik) (Nat.cast_nonneg _))
        (hgbound (k - i) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
    _ = (k.factorial : ℝ) * p *
        ∑ i ∈ Finset.range (k + 1), d ^ i * e ^ (k - i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hc : (k.choose i : ℝ) * (i.factorial : ℝ) *
          ((k - i).factorial : ℝ) = (k.factorial : ℝ) := by
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial hik
      calc
        _ = ((k.choose i : ℝ) * (i.factorial : ℝ) * ((k - i).factorial : ℝ)) *
            p * (d ^ i * e ^ (k - i)) := by ring
        _ = _ := by rw [hc]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (geometric_convolution_le hd he k)
        (show 0 ≤ (k.factorial : ℝ) * p by positivity)
      convert hh using 1 <;> ring

end HigherRankKSRuntime.LocalLeibniz
