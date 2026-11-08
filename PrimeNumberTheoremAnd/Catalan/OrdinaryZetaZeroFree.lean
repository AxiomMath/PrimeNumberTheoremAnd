import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Complex.Asymptotics
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

namespace CatalanPNT

open Complex Asymptotics Filter
open scoped Topology

namespace CatalanOrdinaryZeta

private lemma re_log_comb_nonneg' {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 3 * (-log (1 - a)).re + 4 * (-log (1 - a * z)).re +
      (-log (1 - a * z ^ 2)).re := by
  have hac₀ : ‖(a : ℂ)‖ < 1 := by
    simp only [Complex.norm_of_nonneg ha₀, ha₁]
  have hac₁ : ‖a * z‖ < 1 := by rwa [norm_mul, hz, mul_one]
  have hac₂ : ‖a * z ^ 2‖ < 1 := by rwa [norm_mul, norm_pow, hz, one_pow, mul_one]
  rw [← ((hasSum_re <| hasSum_taylorSeries_neg_log hac₀).mul_left 3).add
    ((hasSum_re <| hasSum_taylorSeries_neg_log hac₁).mul_left 4) |>.add
    (hasSum_re <| hasSum_taylorSeries_neg_log hac₂) |>.tsum_eq]
  refine tsum_nonneg fun n ↦ ?_
  simp only [← ofReal_pow, div_natCast_re, ofReal_re, mul_pow, mul_re, ofReal_im,
    zero_mul, sub_zero]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · simp only [← mul_div_assoc, ← add_div]
    refine div_nonneg ?_ n.cast_nonneg
    rw [← pow_mul, pow_mul', sq, mul_re, ← sq, ← sq, ← sq_norm_sub_sq_re, norm_pow, hz]
    convert! (show 0 ≤ 2 * a ^ n * ((z ^ n).re + 1) ^ 2 by positivity) using 1
    ring

private lemma re_log_comb_nonneg {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 1 < x)
    (y : ℝ) :
    0 ≤ 3 * (-log (1 - (n : ℂ) ^ (-x : ℂ))).re +
      4 * (-log (1 - (n : ℂ) ^ (-(x + I * y)))).re +
      (-log (1 - (n : ℂ) ^ (-(x + 2 * I * y)))).re := by
  let a : ℝ := (n : ℝ) ^ (-x)
  let z : ℂ := (n : ℂ) ^ (-(I * y))
  have hn₀ : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have ha₀ : 0 ≤ a := by dsimp [a]; positivity
  have ha₁ : a < 1 := by
    dsimp [a]
    rw [Real.rpow_neg (Nat.cast_nonneg n), inv_lt_one_iff₀]
    exact .inr <| Real.one_lt_rpow (mod_cast one_lt_two.trans_le hn) <| zero_lt_one.trans hx
  have hz : ‖z‖ = 1 := by
    dsimp [z]
    rw [← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos (mod_cast by omega)]
    simp only [neg_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im,
      mul_zero, sub_self, neg_zero, Real.rpow_zero]
  have h₀ : (n : ℂ) ^ (-x : ℂ) = (a : ℂ) := by
    dsimp [a]
    simp only [ofReal_cpow n.cast_nonneg (-x), ofReal_natCast, ofReal_neg]
  have h₁ : (n : ℂ) ^ (-(x + I * y)) = (a : ℂ) * z := by
    dsimp [z]
    rw [neg_add, cpow_add _ _ hn₀, h₀]
  have h₂ : (n : ℂ) ^ (-(x + 2 * I * y)) = (a : ℂ) * z ^ 2 := by
    dsimp [z]
    rw [neg_add, cpow_add _ _ hn₀, h₀,
      show -(2 * I * y) = (2 : ℕ) * -(I * y) by ring, cpow_nat_mul]
  simpa only [h₀, h₁, h₂] using re_log_comb_nonneg' ha₀ ha₁ hz

private lemma summable_prime_log {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes ↦ -log (1 - (p : ℂ) ^ (-s))) := by
  simpa only [riemannZetaSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk] using!
    (summable_riemannZetaSummand hs).of_norm.clog_one_sub.neg.subtype Nat.Prime

private lemma one_lt_re_one_add {x : ℝ} (hx : 0 < x) (y : ℝ) :
    1 < (1 + x : ℂ).re ∧ 1 < (1 + x + I * y).re ∧
      1 < (1 + x + 2 * I * y).re := by
  simp only [add_re, one_re, ofReal_re, lt_add_iff_pos_right, hx, mul_re, I_re,
    zero_mul, I_im, ofReal_im, mul_zero, sub_self, add_zero, re_ofNat, im_ofNat,
    mul_one, mul_im, and_self]

theorem norm_riemannZeta_product_ge_one {x : ℝ} (hx : 0 < x) (y : ℝ) :
    1 ≤ ‖riemannZeta (1 + x) ^ 3 * riemannZeta (1 + x + I * y) ^ 4 *
      riemannZeta (1 + x + 2 * I * y)‖ := by
  have ⟨h₀, h₁, h₂⟩ := one_lt_re_one_add hx y
  have H₀ := summable_prime_log h₀
  have H₁ := summable_prime_log h₁
  have H₂ := summable_prime_log h₂
  have hsum₀ := (hasSum_re H₀.hasSum).summable.mul_left 3
  have hsum₁ := (hasSum_re H₁.hasSum).summable.mul_left 4
  have hsum₂ := (hasSum_re H₂.hasSum).summable
  rw [← riemannZeta_eulerProduct_exp_log h₀, ← riemannZeta_eulerProduct_exp_log h₁,
    ← riemannZeta_eulerProduct_exp_log h₂]
  simp only [← exp_nat_mul, Nat.cast_ofNat, ← exp_add, norm_exp, add_re, mul_re,
    re_ofNat, im_ofNat, zero_mul, sub_zero, Real.one_le_exp_iff]
  rw [re_tsum H₀, re_tsum H₁, re_tsum H₂, ← tsum_mul_left, ← tsum_mul_left,
    ← hsum₀.tsum_add hsum₁, ← (hsum₀.add hsum₁).tsum_add hsum₂]
  simpa only [neg_add_rev, neg_re, ge_iff_le, add_re, one_re, ofReal_re,
    ofReal_add, ofReal_one] using
    tsum_nonneg (fun p : Nat.Primes ↦ re_log_comb_nonneg p.prop.two_le
      (show 1 < 1 + x by linarith) y)

private lemma riemannZeta_isBigO_near_one_horizontal :
    (fun x : ℝ ↦ riemannZeta (1 + x)) =O[𝓝[>] 0] fun x ↦ (1 : ℂ) / x := by
  have : (fun w : ℂ ↦ riemannZeta (1 + w)) =O[𝓝[≠] 0] (1 / ·) := by
    have H : Tendsto (fun w : ℂ ↦ w * riemannZeta (1 + w)) (𝓝[≠] 0) (𝓝 1) := by
      convert! riemannZeta_residue_one.comp (f := fun w ↦ 1 + w) ?_ using 1
      · simp only [Function.comp_def, add_sub_cancel_left]
      · simpa only [tendsto_iff_comap, Homeomorph.coe_addLeft, add_zero,
          map_le_iff_le_comap] using
          ((Homeomorph.addLeft (1 : ℂ)).map_punctured_nhds_eq 0).le
    exact (isBigO_mul_iff_isBigO_div eventually_mem_nhdsWithin).mp <| H.isBigO_one ℂ
  exact (isBigO_comp_ofReal_nhds_ne this).mono <| nhdsGT_le_nhdsNE 0

private lemma one_add_I_mul_ne_one {y : ℝ} (hy : y ≠ 0) : 1 + I * y ≠ 1 := by
  simpa only [ne_eq, add_eq_left, mul_eq_zero, I_ne_zero, ofReal_eq_zero, false_or] using hy

private lemma riemannZeta_isBigO_horizontal {y : ℝ} (hy : y ≠ 0) :
    (fun x : ℝ ↦ riemannZeta (1 + x + I * y)) =O[𝓝[>] 0]
      fun _ ↦ (1 : ℂ) := by
  refine IsBigO.mono ?_ nhdsWithin_le_nhds
  simp_rw [add_comm (1 : ℂ), add_assoc]
  have := (differentiableAt_riemannZeta (one_add_I_mul_ne_one hy)).continuousAt
  rw [← zero_add (1 + _)] at this
  exact this.comp (f := fun x : ℝ ↦ x + (1 + I * y)) (x := 0) (by fun_prop)
    |>.tendsto.isBigO_one ℂ

private lemma riemannZeta_isBigO_horizontal_of_eq_zero {y : ℝ} (hy : y ≠ 0)
    (h : riemannZeta (1 + I * y) = 0) :
    (fun x : ℝ ↦ riemannZeta (1 + x + I * y)) =O[𝓝[>] 0]
      fun x : ℝ ↦ (x : ℂ) := by
  simp_rw [add_comm (1 : ℂ), add_assoc]
  have := (differentiableAt_riemannZeta (one_add_I_mul_ne_one hy)).hasDerivAt
  rw [← zero_add (1 + _)] at this
  simpa only [zero_add, h, sub_zero] using
    (Complex.isBigO_comp_ofReal_nhds
      (this.comp_add_const 0 _).differentiableAt.isBigO_sub) |>.mono nhdsWithin_le_nhds

private lemma riemannZeta_ne_zero_one_add_I_mul {t : ℝ} (ht : t ≠ 0) :
    riemannZeta (1 + I * t) ≠ 0 := by
  intro Hz
  have ht₂ : 2 * t ≠ 0 := mul_ne_zero two_ne_zero ht
  have help (x : ℝ) : ((1 / x) ^ 3 * x ^ 4 * 1 : ℂ) = x := by
    rcases eq_or_ne x 0 with rfl | h
    · rw [ofReal_zero, zero_pow (by omega), mul_zero, mul_one]
    · rw [one_div, inv_pow, pow_succ _ 3, ← mul_assoc,
        inv_mul_cancel₀ <| pow_ne_zero 3 (ofReal_ne_zero.mpr h), one_mul, mul_one]
  have H₀ : (fun _ : ℝ ↦ (1 : ℝ)) =O[𝓝[>] 0]
      fun x ↦ riemannZeta (1 + x) ^ 3 * riemannZeta (1 + x + I * t) ^ 4 *
        riemannZeta (1 + x + 2 * I * t) :=
    IsBigO.of_bound' <| eventually_nhdsWithin_of_forall
      fun _ hx ↦ (norm_one (α := ℝ)).symm ▸ (norm_riemannZeta_product_ge_one hx t)
  have H := riemannZeta_isBigO_near_one_horizontal.pow 3 |>.mul <|
    (riemannZeta_isBigO_horizontal_of_eq_zero ht Hz).pow 4 |>.mul <|
    riemannZeta_isBigO_horizontal ht₂
  simp only [ofReal_mul, ofReal_ofNat, mul_left_comm I, ← mul_assoc, help] at H
  replace H := (H₀.trans H).norm_right
  simp only [norm_real] at H
  exact isLittleO_irrefl (.of_forall (fun _ ↦ one_ne_zero)) <|
    H.of_norm_right.trans_isLittleO <| isLittleO_id_one.mono nhdsWithin_le_nhds

theorem riemannZeta_ne_zero_of_re_eq_one_of_ne_one {s : ℂ} (hs : s.re = 1)
    (hs₁ : s ≠ 1) : riemannZeta s ≠ 0 := by
  have hs' : s = 1 + I * s.im := by
    conv_lhs => rw [← re_add_im s, hs, ofReal_one, mul_comm]
  have him : s.im ≠ 0 := by
    intro h
    apply hs₁
    rw [hs', h, ofReal_zero, mul_zero, add_zero]
  exact hs'.symm ▸ riemannZeta_ne_zero_one_add_I_mul him

theorem riemannZeta_ne_zero_of_one_le_re_of_ne_one {s : ℂ} (hs : 1 ≤ s.re)
    (hs₁ : s ≠ 1) : riemannZeta s ≠ 0 := by
  rcases hs.eq_or_lt with h | h
  · exact riemannZeta_ne_zero_of_re_eq_one_of_ne_one h.symm hs₁
  · exact _root_.riemannZeta_ne_zero_of_one_lt_re h

end CatalanOrdinaryZeta

end CatalanPNT
