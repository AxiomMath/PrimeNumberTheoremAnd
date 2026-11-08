import Mathlib

namespace SiegelZeros

open _root_.Complex

section
open scoped BigOperators

namespace Real

lemma pow_div_one_sub_le_two_mul {r : ℝ} (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) (m : ℕ) :
    r ^ (m + 1) / (1 - r) ≤ 2 * r ^ (m + 1) := by
  have hpow : 0 ≤ r ^ (m + 1) := pow_nonneg hr _
  have hhalf' : (1 / 2 : ℝ) ≤ 1 - r := by linarith
  calc
    r ^ (m + 1) / (1 - r) ≤ r ^ (m + 1) / (1 / 2 : ℝ) := by
      exact div_le_div_of_nonneg_left hpow (by positivity) hhalf'
    _ = 2 * r ^ (m + 1) := by ring

end Real

namespace Complex

open scoped BigOperators in
                                                                                        
lemma neg_log_one_sub_eq_tsum {z : ℂ} (hz : ‖z‖ < 1) :
    -log (1 - z) = ∑' n : ℕ, z ^ (n + 1) / (n + 1) := by
  have h := hasSum_taylorSeries_neg_log hz
  rw [← h.tsum_eq, h.summable.tsum_eq_zero_add]
  simp only [pow_zero, Nat.cast_zero, div_zero, zero_add, Nat.cast_add, Nat.cast_one]

noncomputable
def partialLogSum (m : ℕ) (z : ℂ) : ℂ :=
  -logTaylor (m + 1) (-z)

@[simp]
lemma partialLogSum_zero (z : ℂ) : partialLogSum 0 z = 0 := by
  simp [partialLogSum, logTaylor_succ, logTaylor_zero]

@[simp]
lemma partialLogSum_at_zero (m : ℕ) : partialLogSum m 0 = 0 := by
  simp [partialLogSum, logTaylor_at_zero]

lemma logTaylor_succ_neg (n : ℕ) (z : ℂ) :
    logTaylor (n + 1) (-z) = logTaylor n (-z) - z ^ n / n := by
  rw [logTaylor_succ, Pi.add_apply]
  have hsign : (-1 : ℂ) ^ (n + 1) * (-z) ^ n = -z ^ n := by
    have hzpow : (-z) ^ n = (((-1 : ℂ) * z) ^ n) := by simp
    rw [hzpow, mul_pow, ← mul_assoc, ← pow_add]
    have hpow : (-1 : ℂ) ^ (n + 1 + n) = (-1 : ℂ) := by
      rw [show n + 1 + n = 2 * n + 1 by omega, pow_add, pow_mul]
      norm_num
    rw [hpow]
    ring
  rw [show (-1 : ℂ) ^ (n + 1) * (-z) ^ n / n = -(z ^ n / n) by
    rw [hsign]
    ring]
  abel

lemma logTaylor_neg_eq_neg_sum (m : ℕ) (z : ℂ) :
    logTaylor (m + 1) (-z) = -∑ k ∈ Finset.range m, z ^ (k + 1) / (k + 1) := by
  induction m with
  | zero =>
      simp [logTaylor_succ, logTaylor_zero]
  | succ m hm =>
      rw [logTaylor_succ_neg, hm, Finset.sum_range_succ]
      have hcast : ((m + 1 : ℕ) : ℂ) = (1 + (m : ℂ)) := by
        simp [Nat.cast_add, Nat.cast_one, add_comm]
      rw [hcast]
      ring_nf

lemma partialLogSum_eq_sum (m : ℕ) (z : ℂ) :
    partialLogSum m z = ∑ k ∈ Finset.range m, z ^ (k + 1) / (k + 1) := by
  simpa [partialLogSum] using congrArg Neg.neg (logTaylor_neg_eq_neg_sum m z)

lemma hasDerivAt_partialLogSum (m : ℕ) (z : ℂ) :
    HasDerivAt (partialLogSum m) (∑ j ∈ Finset.range m, z ^ j) z := by
  cases m with
  | zero =>
      have hzero : partialLogSum 0 = fun _ : ℂ ↦ (0 : ℂ) := by
        funext w
        exact partialLogSum_zero w
      simpa [hzero] using (hasDerivAt_const z (c := (0 : ℂ)))
  | succ m =>
      have hsum :
          (∑ j ∈ Finset.range (m + 1), z ^ j) =
            ∑ j ∈ Finset.range (m + 1), (-1) ^ j * (-z) ^ j := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        symm
        calc
          (-1 : ℂ) ^ j * (-z) ^ j = (-1 : ℂ) ^ j * (((-1 : ℂ) * z) ^ j) := by simp
          _ = ((-1 : ℂ) ^ j * (-1 : ℂ) ^ j) * z ^ j := by rw [mul_pow]; ring
          _ = z ^ j := by
                rw [← pow_add, show j + j = 2 * j by omega, pow_mul]
                norm_num
      rw [hsum]
      simpa [partialLogSum] using!
        (((hasDerivAt_logTaylor (m + 1) (-z)).comp z (hasDerivAt_neg z)).neg)

lemma differentiable_partialLogSum (m : ℕ) :
    Differentiable ℂ (fun z : ℂ => partialLogSum m z) := by
  intro z
  exact (hasDerivAt_partialLogSum m z).differentiableAt

noncomputable
def logTail (m : ℕ) (z : ℂ) : ℂ :=
  ∑' k, z ^ (m + 1 + k) / (m + 1 + k)

lemma summable_logTail {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    Summable (fun k => z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)) := by
  have h_geom : Summable (fun k : ℕ => ‖z‖ ^ k) :=
    summable_geometric_of_lt_one (norm_nonneg z) hz
  refine Summable.of_norm_bounded (g := fun k => ‖z‖ ^ k) h_geom ?_
  intro k
  rw [norm_div, norm_pow]
  have h1 : (1 : ℝ) ≤ (m + 1 + k : ℝ) := by
    have : (0 : ℝ) ≤ (m + k : ℝ) := by positivity
    nlinarith
  have hnorm : ‖(↑m + 1 + ↑k : ℂ)‖ = (m + 1 + k : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
      (Complex.norm_natCast (m + 1 + k))
  rw [hnorm]
  calc
    ‖z‖ ^ (m + 1 + k) / (m + 1 + k : ℝ) ≤ ‖z‖ ^ (m + 1 + k) := by
      exact div_le_self (pow_nonneg (norm_nonneg z) _) h1
    _ = ‖z‖ ^ (m + 1) * ‖z‖ ^ k := by rw [pow_add]
    _ ≤ 1 * ‖z‖ ^ k := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg z) k)
          exact pow_le_one₀ (norm_nonneg z) (le_of_lt hz)
    _ = ‖z‖ ^ k := one_mul _

lemma norm_logTail_le {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    ‖logTail m z‖ ≤ ‖z‖ ^ (m + 1) / (1 - ‖z‖) := by
  dsimp only [logTail]
  have h_rhs_summable : Summable (fun k => ‖z‖ ^ (m + 1 + k)) := by
    simpa [pow_add] using
      (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left (‖z‖ ^ (m + 1))
  have h_norm_summable : Summable (fun k => ‖z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ h_rhs_summable
    intro k
    rw [norm_div, norm_pow]
    have hnorm : ‖(↑m + 1 + ↑k : ℂ)‖ = (m + 1 + k : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
        (Complex.norm_natCast (m + 1 + k))
    rw [hnorm]
    have hm : 1 ≤ (m + 1 + k : ℝ) := by
      have : (0 : ℝ) ≤ (m + k : ℝ) := by positivity
      nlinarith
    exact div_le_self (pow_nonneg (norm_nonneg z) _) hm
  calc
    ‖∑' k, z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)‖
        ≤ ∑' k, ‖z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)‖ :=
          norm_tsum_le_tsum_norm h_norm_summable
    _ ≤ ∑' k, ‖z‖ ^ (m + 1 + k) := by
          refine h_norm_summable.tsum_le_tsum ?_ h_rhs_summable
          intro k
          rw [norm_div, norm_pow]
          have hm : 1 ≤ (m + 1 + k : ℝ) := by
            have : (0 : ℝ) ≤ (m + k : ℝ) := by positivity
            nlinarith
          have hnorm : ‖(↑m + 1 + ↑k : ℂ)‖ = (m + 1 + k : ℝ) := by
            simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
              (Complex.norm_natCast (m + 1 + k))
          rw [hnorm]
          exact div_le_self (pow_nonneg (norm_nonneg z) _) hm
    _ = ‖z‖ ^ (m + 1) / (1 - ‖z‖) := by
          have h_eq :
              (fun k => ‖z‖ ^ (m + 1 + k)) = fun k => ‖z‖ ^ (m + 1) * ‖z‖ ^ k := by
            ext k
            rw [pow_add]
          rw [h_eq, tsum_mul_left]
          have h_geom := hasSum_geometric_of_lt_one (norm_nonneg z) hz
          rw [h_geom.tsum_eq, div_eq_mul_inv]

lemma norm_logTail_le_two_mul_norm_pow {z : ℂ} (hz : ‖z‖ < 1) (hzhalf : ‖z‖ ≤ 1 / 2) (m : ℕ) :
    ‖logTail m z‖ ≤ 2 * ‖z‖ ^ (m + 1) :=
  (norm_logTail_le hz m).trans (Real.pow_div_one_sub_le_two_mul (norm_nonneg z) hzhalf m)

lemma norm_partialLogSum_le_nat_mul_max_one_norm_pow (m : ℕ) (z : ℂ) :
    ‖partialLogSum m z‖ ≤ (m : ℝ) * max 1 (‖z‖ ^ m) := by
  have hsum :
      ‖partialLogSum m z‖ ≤ ∑ k ∈ Finset.range m, ‖z ^ (k + 1) / (k + 1)‖ := by
    rw [partialLogSum_eq_sum]
    exact norm_sum_le _ _
  have hterm : ∀ k ∈ Finset.range m, ‖z ^ (k + 1) / (k + 1)‖ ≤ max 1 (‖z‖ ^ m) := by
    intro k hk
    rw [norm_div, norm_pow]
    have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have hk1_nat : (1 : ℕ) ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
      exact_mod_cast hk1_nat
    have hdenom : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
        (Complex.norm_natCast (k + 1))
    have hk_le : k + 1 ≤ m := Nat.succ_le_iff.2 (Finset.mem_range.1 hk)
    have hpow_le : ‖z‖ ^ (k + 1) ≤ max 1 (‖z‖ ^ m) := by
      have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
      by_cases hz1 : ‖z‖ ≤ (1 : ℝ)
      · have : ‖z‖ ^ (k + 1) ≤ 1 := by exact pow_le_one₀ hz0 hz1
        exact this.trans (le_max_left _ _)
      · have hz1' : (1 : ℝ) ≤ ‖z‖ := le_of_lt (lt_of_not_ge hz1)
        have : ‖z‖ ^ (k + 1) ≤ ‖z‖ ^ m := pow_le_pow_right₀ hz1' hk_le
        exact this.trans (le_max_right _ _)
    calc
      ‖z‖ ^ (k + 1) / ‖((k : ℂ) + 1)‖ = ‖z‖ ^ (k + 1) / ((k : ℝ) + 1) := by simp [hdenom]
      _ ≤ ‖z‖ ^ (k + 1) := by
            exact div_le_self (pow_nonneg (norm_nonneg z) _) hk1
      _ ≤ max 1 (‖z‖ ^ m) := hpow_le
  have hsum_le :
      (∑ k ∈ Finset.range m, ‖z ^ (k + 1) / (k + 1)‖) ≤
        ∑ _k ∈ Finset.range m, max 1 (‖z‖ ^ m) :=
    Finset.sum_le_sum (fun k hk => hterm k hk)
  have hcard : ∑ _k ∈ Finset.range m, max 1 (‖z‖ ^ m) = (m : ℝ) * max 1 (‖z‖ ^ m) := by
    simp [Finset.sum_const]
  exact hsum.trans (hsum_le.trans_eq hcard)

lemma neg_log_one_sub_eq_partialLogSum_add_logTail {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    -log (1 - z) = partialLogSum m z + logTail m z := by
  let f : ℕ → ℂ := fun k ↦ z ^ (k + 1) / ((k : ℂ) + 1)
  have h_summable : Summable f := by
    simpa [f, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
      (summable_logTail hz 0)
  have h_decomp := h_summable.sum_add_tsum_nat_add m
  rw [neg_log_one_sub_eq_tsum hz, partialLogSum_eq_sum, ← h_decomp]
  congr 1
  dsimp only [logTail]
  refine tsum_congr fun k ↦ ?_
  simp only [f, Nat.cast_add]
  ring_nf

end Complex
end
section
noncomputable section

namespace Complex

variable {z : ℂ}

@[bound]
theorem neg_norm_le_re (z : ℂ) : -‖z‖ ≤ z.re :=
  neg_le_of_abs_le (abs_re_le_norm z)

lemma norm_inv_pow_le_one_of_one_le_norm (u : ℂ) (n : ℕ) (hu : (1 : ℝ) ≤ ‖u‖) :
    ‖(u ^ n)⁻¹‖ ≤ 1 := by
  have hge : (1 : ℝ) ≤ ‖u ^ n‖ := by
    rw [Complex.norm_pow]
    exact one_le_pow₀ hu
  calc ‖(u ^ n)⁻¹‖ = ‖(1 : ℂ) / u ^ n‖ := by rw [inv_eq_one_div]
    _ = 1 / ‖u ^ n‖ := by
        have hone : ‖(1 : ℂ)‖ = (1 : ℝ) := by simp
        rw [Complex.norm_div, hone]
    _ ≤ 1 := by simpa [one_div] using inv_le_one_of_one_le₀ hge

end Complex
end
end
section
noncomputable section

open scoped BigOperators
open Set

namespace Complex

def weierstrassFactor (m : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * exp (partialLogSum m z)

lemma weierstrassFactor_def (m : ℕ) (z : ℂ) :
    weierstrassFactor m z = (1 - z) * exp (partialLogSum m z) := by
  simp [weierstrassFactor]

@[simp]
lemma weierstrassFactor_at_zero (m : ℕ) : weierstrassFactor m 0 = 1 := by
  simp [weierstrassFactor, partialLogSum_at_zero]

lemma weierstrassFactor_eq_zero_iff (m : ℕ) (z : ℂ) :
    weierstrassFactor m z = 0 ↔ z = 1 := by
  constructor
  · intro hz
    rw [weierstrassFactor] at hz
    rcases mul_eq_zero.mp hz with h1 | h2
    · exact (sub_eq_zero.mp h1).symm
    · exact absurd h2 (exp_ne_zero _)
  · rintro rfl
    simp [weierstrassFactor]

lemma weierstrassFactor_ne_zero_iff (m : ℕ) (z : ℂ) :
    weierstrassFactor m z ≠ 0 ↔ z ≠ 1 := by
  simpa [ne_eq] using (not_congr (weierstrassFactor_eq_zero_iff (m := m) (z := z)))

lemma weierstrassFactor_ne_zero_of_ne_one (m : ℕ) {z : ℂ} (hz : z ≠ 1) :
    weierstrassFactor m z ≠ 0 :=
  (weierstrassFactor_ne_zero_iff (m := m) (z := z)).2 hz

lemma differentiable_weierstrassFactor (m : ℕ) :
    Differentiable ℂ (fun z : ℂ => weierstrassFactor m z) := by
  simpa [weierstrassFactor] using!
    ((differentiable_const (c := (1 : ℂ))).sub differentiable_id).mul
      (differentiable_exp.comp (differentiable_partialLogSum m))

theorem analyticOrderAt_weierstrassFactor_div_self (m : ℕ) {a : ℂ} (ha : a ≠ 0) :
    analyticOrderAt (fun z : ℂ => weierstrassFactor m (z / a)) a = (1 : ℕ∞) := by
  set F : ℂ → ℂ := fun z => weierstrassFactor m (z / a)
  have hF : AnalyticAt ℂ F a := by
    have hdiv : Differentiable ℂ (fun z : ℂ => z / a) := by
      simp [div_eq_mul_inv]
    have hdiff : Differentiable ℂ F := (differentiable_weierstrassFactor m).comp hdiv
    exact Differentiable.analyticAt (f := F) hdiff a
  let g : ℂ → ℂ := fun z => (-a⁻¹) * Complex.exp (partialLogSum m (z / a))
  have hg : AnalyticAt ℂ g a := by
    have hdiv : Differentiable ℂ (fun z : ℂ => z / a) := by
      simp [div_eq_mul_inv]
    have hpls : Differentiable ℂ (fun z : ℂ => partialLogSum m (z / a)) :=
      (differentiable_partialLogSum m).comp hdiv
    have hexp : Differentiable ℂ (fun z : ℂ => Complex.exp (partialLogSum m (z / a))) :=
      (Complex.differentiable_exp).comp hpls
    have hdiffg : Differentiable ℂ g := by
      simpa [g] using hexp.const_mul (-a⁻¹ : ℂ)
    exact Differentiable.analyticAt (f := g) hdiffg a
  have hg0 : g a ≠ 0 := by
    have hconst : (-a⁻¹ : ℂ) ≠ 0 := by simp [ha]
    have hexp0 : Complex.exp (partialLogSum m (a / a)) ≠ 0 :=
      Complex.exp_ne_zero (partialLogSum m (a / a))
    simpa [g] using mul_ne_zero hconst hexp0
  refine (hF.analyticOrderAt_eq_natCast (n := 1)).2 ?_
  refine ⟨g, hg, hg0, ?_⟩
  refine Filter.Eventually.of_forall ?_
  intro z
  have hlin : (1 - z / a) = (z - a) * (-a⁻¹) := by
    have h1 : (1 : ℂ) = a * a⁻¹ := by simp [ha]
    simp [div_eq_mul_inv, h1]
    ring
  simp only [F, g, pow_one, smul_eq_mul]
  rw [weierstrassFactor_def]
  simp [hlin, mul_assoc]

lemma weierstrassFactor_eq_exp_neg_tail (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) (hz1 : z ≠ 1) :
    weierstrassFactor m z = exp (-logTail m z) := by
  unfold weierstrassFactor
  have hz_ne_1 : 1 - z ≠ 0 := sub_ne_zero.mpr hz1.symm
  rw [← exp_log hz_ne_1, ← Complex.exp_add]
  have hsum : log (1 - z) + partialLogSum m z = -logTail m z := by
    have hdecomp := neg_log_one_sub_eq_partialLogSum_add_logTail hz m
    calc
      log (1 - z) + partialLogSum m z
          = log (1 - z) + (partialLogSum m z + logTail m z) - logTail m z := by ring
      _ = log (1 - z) + (-log (1 - z)) - logTail m z := by rw [hdecomp]
      _ = -logTail m z := by ring
  simp [hsum]

theorem weierstrassFactor_sub_one_pow_bound {m : ℕ} {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖weierstrassFactor m z - 1‖ ≤ 4 * ‖z‖ ^ (m + 1) := by
  by_cases hm : m = 0
  · subst hm
    have hmain : ‖(1 - z) - 1‖ ≤ 4 * ‖z‖ ^ 1 := by
      have h : (1 - z) - 1 = -z := by ring
      calc
        ‖(1 - z) - 1‖ = ‖-z‖ := by simp [h]
        _ = ‖z‖ := norm_neg z
        _ = ‖z‖ ^ 1 := by simp
        _ ≤ 4 * ‖z‖ ^ 1 := by nlinarith [pow_nonneg (norm_nonneg z) 1]
    simpa [weierstrassFactor] using hmain
  · have hz_lt : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
    by_cases hz1 : z = 1
    · exfalso; rw [hz1] at hz; norm_num at hz
    have h_eq : weierstrassFactor m z = exp (-logTail m z) :=
      weierstrassFactor_eq_exp_neg_tail m hz_lt hz1
    rw [h_eq]
    have h_tail_bound := norm_logTail_le_two_mul_norm_pow hz_lt hz m
    have hw_le_one : ‖-logTail m z‖ ≤ 1 := by
      simp only [norm_neg]
      have : ‖logTail m z‖ ≤ 1 := by
        have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
        have h2 : 2 ≤ m + 1 := by
          exact Nat.succ_le_succ (Nat.succ_le_iff.2 hm_pos)
        have hpow : (‖z‖ ^ (m + 1)) ≤ (‖z‖ ^ 2) := by
          have hz1' : ‖z‖ ≤ 1 := by nlinarith [hz]
          have hz0' : 0 ≤ ‖z‖ := norm_nonneg z
          exact pow_le_pow_of_le_one hz0' hz1' h2
        have hmul : 2 * ‖z‖ ^ (m + 1) ≤ 2 * ‖z‖ ^ 2 := by gcongr
        have hsq : 2 * ‖z‖ ^ 2 ≤ 1 := by
          have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
          have hz_sq : ‖z‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ hz0 hz 2
          nlinarith
        exact (h_tail_bound.trans hmul).trans hsq
      linarith
    have h_exp_sub_one : ‖exp (-logTail m z) - 1‖ ≤ 2 * ‖-logTail m z‖ :=
      Complex.norm_exp_sub_one_le hw_le_one
    simp only [norm_neg] at h_exp_sub_one
    calc
      ‖exp (-logTail m z) - 1‖ ≤ 2 * ‖logTail m z‖ := h_exp_sub_one
      _ ≤ 2 * (2 * ‖z‖ ^ (m + 1)) := by gcongr
      _ = 4 * ‖z‖ ^ (m + 1) := by ring

lemma log_norm_weierstrassFactor_ge_log_norm_one_sub_sub (m : ℕ) (z : ℂ) :
    Real.log ‖1 - z‖ - ‖partialLogSum m z‖ ≤ Real.log ‖weierstrassFactor m z‖ := by
  by_cases hz1 : z = (1 : ℂ)
  · subst hz1
    simp [weierstrassFactor]
  set S : ℂ := partialLogSum m z
  have hS : weierstrassFactor m z = (1 - z) * Complex.exp S := by
    simp [weierstrassFactor, S]
  have hnorm_pos : 0 < ‖(1 : ℂ) - z‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz1))
  have hlog :
      Real.log ‖weierstrassFactor m z‖ = Real.log ‖1 - z‖ + S.re := by
    have hne : ‖(1 : ℂ) - z‖ ≠ 0 := ne_of_gt hnorm_pos
    calc
      Real.log ‖weierstrassFactor m z‖
          = Real.log (‖(1 : ℂ) - z‖ * ‖Complex.exp S‖) := by
              simp [hS]
      _ = Real.log ‖(1 : ℂ) - z‖ + Real.log ‖Complex.exp S‖ := by
            simpa using (Real.log_mul hne (ne_of_gt (by simp)))
      _ = Real.log ‖(1 : ℂ) - z‖ + S.re := by
            simp [Complex.norm_exp, Real.log_exp]
      _ = Real.log ‖1 - z‖ + S.re := by simp [sub_eq_add_neg, add_comm]
  have hre : S.re ≥ -‖S‖ := Complex.neg_norm_le_re S
  have : Real.log ‖weierstrassFactor m z‖ ≥ Real.log ‖1 - z‖ - ‖S‖ := by
    linarith [hlog, hre]
  simpa [S] using this

lemma log_norm_weierstrassFactor_ge_neg_two_pow {m : ℕ} {z : ℂ} (hz : ‖z‖ ≤ (1 / 2 : ℝ)) :
    (-2 : ℝ) * ‖z‖ ^ (m + 1) ≤ Real.log ‖weierstrassFactor m z‖ := by
  have hz_lt : ‖z‖ < (1 : ℝ) := lt_of_le_of_lt hz (by norm_num)
  have hz1 : z ≠ (1 : ℂ) := by
    intro h
    have : (1 : ℝ) ≤ (1 / 2 : ℝ) := by
      simpa [h] using hz
    norm_num at this
  have hEq : weierstrassFactor m z = Complex.exp (-logTail m z) :=
    weierstrassFactor_eq_exp_neg_tail m hz_lt hz1
  have hlog :
      Real.log ‖weierstrassFactor m z‖ = (-logTail m z).re := by
    simp [hEq, Complex.norm_exp, Real.log_exp]
  have hre : (-logTail m z).re ≥ -‖logTail m z‖ := by
    simpa [norm_neg] using Complex.neg_norm_le_re (-logTail m z)
  have htail := norm_logTail_le_two_mul_norm_pow hz_lt hz m
  have : (-logTail m z).re ≥ (-2 : ℝ) * ‖z‖ ^ (m + 1) := by
    calc
      (-logTail m z).re ≥ -‖logTail m z‖ := hre
      _ ≥ (-2 : ℝ) * ‖z‖ ^ (m + 1) := by
            nlinarith [htail]
  simpa [hlog, mul_assoc, mul_left_comm, mul_comm] using this

end Complex
end
end
section
noncomputable section

open Filter Topology

namespace Complex

theorem logDeriv_weierstrassFactor_one_div {a z : ℂ} (ha : a ≠ 0) (hz : z ≠ a) :
    logDeriv (fun w : ℂ => weierstrassFactor 1 (w / a)) z =
      1 / (z - a) + 1 / a := by
  have hE :
      (fun w : ℂ => weierstrassFactor 1 (w / a)) =
        fun w : ℂ => (1 - w / a) * exp (w / a) := by
    ext w
    simp [weierstrassFactor_def, partialLogSum_eq_sum]
  have hf : (1 - z / a) ≠ 0 := by
    intro hzero
    have hdiv : z / a = 1 := by
      exact (sub_eq_zero.mp hzero).symm
    exact hz ((div_eq_one_iff_eq ha).1 hdiv)
  rw [hE, logDeriv_fun_mul z hf (exp_ne_zero (z / a)) (by fun_prop) (by fun_prop)]
  have hleft : logDeriv (fun w : ℂ => 1 - w / a) z = 1 / (z - a) := by
    rw [logDeriv_apply]
    have hderiv : deriv (fun w : ℂ => 1 - w / a) z = -(1 / a) := by
      simp [one_div]
    rw [hderiv]
    have haz : -z + a ≠ 0 := by
      simpa [sub_eq_add_neg, add_comm] using sub_ne_zero.mpr (Ne.symm hz)
    field_simp [ha, sub_ne_zero.mpr hz, haz]
    have haz' : a - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
    have hza : z - a = -(a - z) := by ring
    rw [hza]
    field_simp [haz']
  have hright : logDeriv (fun w : ℂ => exp (w / a)) z = 1 / a := by
    rw [logDeriv_apply]
    have hderiv : deriv (fun w : ℂ => exp (w / a)) z =
        exp (z / a) * (1 / a) := by
      simp [one_div]
    rw [hderiv]
    field_simp [exp_ne_zero (z / a)]
  rw [hleft, hright]

end Complex
end
end

end SiegelZeros
