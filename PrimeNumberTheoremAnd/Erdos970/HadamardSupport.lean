import Mathlib

namespace Erdos970

section HadamardAssemblyScope

section HadamardSourceScope00

open scoped BigOperators

namespace Real

open _root_.Real

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

open _root_.Complex

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
end HadamardSourceScope00

section HadamardSourceScope01

noncomputable section

namespace Complex

open _root_.Complex

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
end HadamardSourceScope01

section HadamardSourceScope02

noncomputable section

open scoped BigOperators
open Set

namespace Complex

open _root_.Complex

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
end HadamardSourceScope02

section HadamardSourceScope03

noncomputable section

open Filter Topology

namespace Complex

open _root_.Complex

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
end HadamardSourceScope03

section HadamardSourceScope04

open Filter Topology Set

namespace MeromorphicOn

open _root_.MeromorphicOn

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U K : Set 𝕜} {z : 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

lemma divisor_support_inter_compact_finite (f : 𝕜 → E) {U K : Set 𝕜}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    (K ∩ (MeromorphicOn.divisor f U).support).Finite := by
  classical
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  have hloc :
      ∀ x ∈ K, ∃ V : Set 𝕜, V ∈ 𝓝 x ∧ Set.Finite (V ∩ D.support) := by
    intro x hxK
    rcases D.supportLocallyFiniteWithinDomain x (hKU hxK) with ⟨V, hV, hfin⟩
    exact ⟨V, hV, hfin⟩
  choose V hVnhds hVfin using hloc
  rcases hK.elim_nhds_subcover' (U := fun x hx => V x hx) (hU := fun x hx => hVnhds x hx) with
    ⟨t, ht⟩
  have hsub :
      K ∩ D.support ⊆ ⋃ x ∈ t, (V (x : 𝕜) x.2 ∩ D.support) := by
    intro y hy
    rcases hy with ⟨hyK, hyS⟩
    have hycov : y ∈ ⋃ x ∈ t, V (x : 𝕜) x.2 := ht hyK
    rcases Set.mem_iUnion.1 hycov with ⟨x, hycov'⟩
    rcases Set.mem_iUnion.1 hycov' with ⟨hxT, hyV⟩
    refine Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ?_⟩
    exact ⟨hxT, ⟨hyV, hyS⟩⟩
  have hfinU : Set.Finite (⋃ x ∈ t, (V (x : 𝕜) x.2 ∩ D.support)) := by
    classical
    refine (t.finite_toSet).biUnion ?_
    intro x hx
    simpa using (hVfin (x : 𝕜) x.2)
  exact hfinU.subset hsub

end MeromorphicOn
end HadamardSourceScope04

section HadamardSourceScope05

open Set

namespace Complex.Hadamard

open _root_.Complex

def divisorZeroIndex (f : ℂ → ℂ) (U : Set ℂ) : Type :=
  Σ z : ℂ, Fin (Int.toNat (MeromorphicOn.divisor f U z))

abbrev divisorZeroIndex₀ (f : ℂ → ℂ) (U : Set ℂ) : Type :=
  {p : divisorZeroIndex f U // p.1 ≠ 0}

abbrev divisorZeroIndex₀Val {f : ℂ → ℂ} {U : Set ℂ} (p : divisorZeroIndex₀ f U) : ℂ :=
  p.1.1

@[simp]
lemma divisorZeroIndex₀Val_ne_zero {f : ℂ → ℂ} {U : Set ℂ} (p : divisorZeroIndex₀ f U) :
    divisorZeroIndex₀Val p ≠ 0 := p.2

@[simp]
lemma divisorZeroIndex₀Val_mem_divisor_support {f : ℂ → ℂ} {U : Set ℂ}
    (p : divisorZeroIndex₀ f U) :
    MeromorphicOn.divisor f U (divisorZeroIndex₀Val p) ≠ 0 := by
  have hn :
      Int.toNat (MeromorphicOn.divisor f U (divisorZeroIndex₀Val p)) ≠ 0 := by
    intro h0
    have q0 : Fin 0 := by
      simpa [divisorZeroIndex₀Val, h0] using p.1.2
    exact Fin.elim0 q0
  intro hdiv
  have : Int.toNat (MeromorphicOn.divisor f U (divisorZeroIndex₀Val p)) = 0 := by
    simp [hdiv]
  exact hn this

noncomputable def divisorCanonicalProduct (m : ℕ) (f : ℂ → ℂ) (U : Set ℂ) (z : ℂ) : ℂ :=
  ∏' p : divisorZeroIndex₀ f U, weierstrassFactor m (z / divisorZeroIndex₀Val p)

@[simp]
lemma divisorCanonicalProduct_zero (m : ℕ) (f : ℂ → ℂ) (U : Set ℂ) :
    divisorCanonicalProduct m f U 0 = 1 := by
  simp [divisorCanonicalProduct]

end Complex.Hadamard
end HadamardSourceScope05

section HadamardSourceScope06

namespace Complex

open _root_.Complex

section UniformMul

theorem _root_.Erdos970.TendstoUniformlyOn.mul_left_bounded {ι : Type*} {p : Filter ι} {K : Set ℂ}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {h : ℂ → ℂ}
    (hF : TendstoUniformlyOn F f p K) (hh : ∃ C, ∀ z ∈ K, ‖h z‖ ≤ C) :
    TendstoUniformlyOn (fun n z => h z * F n z) (fun z => h z * f z) p K := by
  intro u hu
  rcases Metric.mem_uniformity_dist.1 hu with ⟨ε, hεpos, hεu⟩
  rcases hh with ⟨C, hC⟩
  set C' : ℝ := max C 1
  have hC'pos : 0 < C' := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hC' : ∀ z ∈ K, ‖h z‖ ≤ C' := fun z hz => le_trans (hC z hz) (le_max_left _ _)
  have hv : {p : ℂ × ℂ | dist p.1 p.2 < ε / C'} ∈ uniformity ℂ :=
    Metric.mem_uniformity_dist.2 ⟨ε / C', div_pos hεpos hC'pos, fun _ _ hab => hab⟩
  have hF' : ∀ᶠ n in p, ∀ z : ℂ, z ∈ K → dist (f z) (F n z) < ε / C' := hF _ hv
  filter_upwards [hF'] with n hn z hzK
  have hn' : ‖f z - F n z‖ < ε / C' := by simpa [dist_eq_norm] using hn z hzK
  have hle : ‖h z‖ * ‖f z - F n z‖ ≤ C' * ‖f z - F n z‖ :=
    mul_le_mul_of_nonneg_right (hC' z hzK) (norm_nonneg _)
  have hlt : C' * ‖f z - F n z‖ < C' * (ε / C') := mul_lt_mul_of_pos_left hn' hC'pos
  have hnorm :
      ‖h z * f z - h z * F n z‖ = ‖h z‖ * ‖f z - F n z‖ := by
    calc
      ‖h z * f z - h z * F n z‖ = ‖h z * (f z - F n z)‖ := by simp [mul_sub]
      _ = ‖h z‖ * ‖f z - F n z‖ := by simp
  have hdist : dist (h z * f z) (h z * F n z) < ε := by
    rw [dist_eq_norm, hnorm]
    have hlt' : ‖h z‖ * ‖f z - F n z‖ < ε := by
      calc
        ‖h z‖ * ‖f z - F n z‖ ≤ C' * ‖f z - F n z‖ := hle
        _ < C' * (ε / C') := hlt
        _ = ε := by field_simp [hC'pos.ne']
    exact hlt'
  exact hεu hdist

end UniformMul

end Complex
end HadamardSourceScope06

section HadamardSourceScope07

open Filter _root_.Function _root_.Complex _root_.Erdos970.Complex Finset Topology
open scoped Topology BigOperators
open Set

namespace Complex.Hadamard

open _root_.Complex

lemma finite_divisorZeroIndex₀_subtype_norm_le {f : ℂ → ℂ} {U : Set ℂ} (B : ℝ)
    (hBU : Metric.closedBall (0 : ℂ) B ⊆ U) :
    Finite {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀Val p‖ ≤ B} := by
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  have hK : IsCompact (Metric.closedBall (0 : ℂ) B) := isCompact_closedBall _ _
  have hpts0 : ((Metric.closedBall (0 : ℂ) B) ∩ D.support).Finite :=
    MeromorphicOn.divisor_support_inter_compact_finite (f := f) (U := U)
      (K := Metric.closedBall (0 : ℂ) B) hK hBU
  set pts : Set ℂ := ((Metric.closedBall (0 : ℂ) B) ∩ D.support) \ {0}
  have hpts : pts.Finite := hpts0.sdiff
  let : Fintype pts := hpts.fintype
  let T : Type := Σ z : pts, Fin (Int.toNat (D z.1))
  have : Finite T := by infer_instance
  let F :
      {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀Val p‖ ≤ B} → T := fun p =>
    ⟨⟨divisorZeroIndex₀Val p.1, by
        have hball : divisorZeroIndex₀Val p.1 ∈ Metric.closedBall (0 : ℂ) B := by
          simpa [Metric.mem_closedBall, dist_zero_right] using p.2
        have hsupport : divisorZeroIndex₀Val p.1 ∈ D.support := by
          have hne_toNat :
              Int.toNat (MeromorphicOn.divisor f U (divisorZeroIndex₀Val p.1)) ≠ 0 := by
            intro h0
            have hpfin :
                Fin (Int.toNat (MeromorphicOn.divisor f U (divisorZeroIndex₀Val p.1))) := by
              simpa [D] using p.1.1.2
            have : Fin 0 := by simpa [h0] using hpfin
            exact Fin.elim0 this
          have hne_D : D (divisorZeroIndex₀Val p.1) ≠ 0 := by
            intro hD0
            apply hne_toNat
            simp [D, hD0]
          simp [D, Function.locallyFinsuppWithin.support, Function.support]
        have hne0 : divisorZeroIndex₀Val p.1 ≠ 0 := divisorZeroIndex₀Val_ne_zero p.1
        exact ⟨⟨hball, hsupport⟩, by simp [Set.mem_singleton_iff]⟩⟩,
      p.1.1.2⟩
  refine Finite.of_injective F ?_
  intro p q hpq
  apply Subtype.ext
  apply Subtype.ext
  have h' := (Sigma.mk.inj_iff.1 hpq)
  have hz : divisorZeroIndex₀Val p.1 = divisorZeroIndex₀Val q.1 := congrArg Subtype.val h'.1
  apply (Sigma.mk.inj_iff).2
  refine ⟨hz, ?_⟩
  exact h'.2

lemma divisorZeroIndex₀_norm_le_finite {f : ℂ → ℂ} {U : Set ℂ} (B : ℝ)
    (hBU : Metric.closedBall (0 : ℂ) B ⊆ U) :
    ({p : divisorZeroIndex₀ f U | ‖divisorZeroIndex₀Val p‖ ≤ B} : Set _).Finite := by
  let s : Set (divisorZeroIndex₀ f U) := {p | ‖divisorZeroIndex₀Val p‖ ≤ B}
  have : Finite (↥s) :=
    finite_divisorZeroIndex₀_subtype_norm_le (f := f) (U := U) B hBU
  exact Set.toFinite s

lemma norm_div_le_half_of_norm_le_of_two_mul_lt {z a : ℂ} {R : ℝ}
    (hR : 0 < R) (hz : ‖z‖ ≤ R) (ha : (2 * R : ℝ) < ‖a‖) :
    ‖z / a‖ ≤ (1 / 2 : ℝ) := by
  have h2R_pos : 0 < (2 * R : ℝ) := by nlinarith [hR]
  have hinv : ‖a‖⁻¹ < (2 * R)⁻¹ := by
    simpa [one_div] using one_div_lt_one_div_of_lt h2R_pos ha
  have hmul_le : ‖z‖ * ‖a‖⁻¹ ≤ R * ‖a‖⁻¹ :=
    mul_le_mul_of_nonneg_right hz (inv_nonneg.2 (norm_nonneg a))
  have hmul_lt : R * ‖a‖⁻¹ < R * (2 * R)⁻¹ :=
    mul_lt_mul_of_pos_left hinv hR
  have hRhalf : R * (2 * R)⁻¹ = (1 / 2 : ℝ) := by
    have hRne : (R : ℝ) ≠ 0 := hR.ne'
    rw [show R * (2 * R)⁻¹ = R / (2 * R) by simp [div_eq_mul_inv]]
    field_simp [hRne]
  have hnorm : ‖z / a‖ = ‖z‖ * ‖a‖⁻¹ := by
    simp [div_eq_mul_inv]
  exact le_of_lt <| by
    calc
      ‖z / a‖ = ‖z‖ * ‖a‖⁻¹ := hnorm
      _ ≤ R * ‖a‖⁻¹ := hmul_le
      _ < R * (2 * R)⁻¹ := hmul_lt
      _ = (1 / 2 : ℝ) := hRhalf

theorem summable_logDerivTerms_divisorZeroIndex₀_of_summable_inv_sq
    {f : ℂ → ℂ} {z : ℂ}
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (2 : ℕ)))
    (hz : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), z ≠ divisorZeroIndex₀Val p) :
    Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      1 / (z - divisorZeroIndex₀Val p) + 1 / divisorZeroIndex₀Val p) := by
  let R : ℝ := max ‖z‖ 1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hzle : ‖z‖ ≤ R := le_max_left _ _
  let u : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
    fun p => (2 * R) * (‖divisorZeroIndex₀Val p‖⁻¹ ^ (2 : ℕ))
  have hu : Summable u := h_sum.mul_left (2 * R)
  refine hu.of_norm_bounded_eventually ?_
  have h_big :
      ∀ᶠ p : divisorZeroIndex₀ f (Set.univ : Set ℂ) in Filter.cofinite,
        (2 * R : ℝ) < ‖divisorZeroIndex₀Val p‖ := by
    have hfin :
        ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀Val p‖ ≤
          2 * R} : Set _).Finite := by
      have : Metric.closedBall (0 : ℂ) (2 * R) ⊆ (Set.univ : Set ℂ) := by simp
      exact divisorZeroIndex₀_norm_le_finite
        (f := f) (U := (Set.univ : Set ℂ)) (B := 2 * R) this
    have := hfin.eventually_cofinite_notMem
    filter_upwards [this] with p hp
    have : ¬ ‖divisorZeroIndex₀Val p‖ ≤ 2 * R := by simpa using hp
    exact lt_of_not_ge this
  filter_upwards [h_big] with p hp
  let a : ℂ := divisorZeroIndex₀Val p
  have ha0 : a ≠ 0 := divisorZeroIndex₀Val_ne_zero p
  have hza0 : z - a ≠ 0 := sub_ne_zero.mpr (hz p)
  have hterm : 1 / (z - a) + 1 / a = z / (a * (z - a)) := by
    field_simp [ha0, hza0]
    ring
  have htri : ‖a‖ ≤ ‖z‖ + ‖z - a‖ := by
    have hraw : ‖a‖ ≤ ‖z‖ + ‖a - z‖ := by
      have h := norm_add_le z (a - z)
      simpa [a, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
    simpa [norm_sub_rev] using hraw
  have hza_lower : ‖a‖ / 2 ≤ ‖z - a‖ := by
    nlinarith [htri, hzle, hp]
  have hnorm : ‖1 / (z - a) + 1 / a‖ ≤ (2 * R) * (‖a‖⁻¹ ^ (2 : ℕ)) := by
    rw [hterm, norm_div, norm_mul]
    have ha_norm_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
    have hza_norm_pos : 0 < ‖z - a‖ := norm_pos_iff.mpr hza0
    rw [div_eq_mul_inv]
    calc
      ‖z‖ * (‖a‖ * ‖z - a‖)⁻¹
          = ‖z‖ * ‖a‖⁻¹ * ‖z - a‖⁻¹ := by
              field_simp [ha_norm_pos.ne', hza_norm_pos.ne']
      _ ≤ R * ‖a‖⁻¹ * ‖z - a‖⁻¹ := by
              gcongr
      _ ≤ R * ‖a‖⁻¹ * (2 * ‖a‖⁻¹) := by
              gcongr
              have hhalf_pos : 0 < ‖a‖ / 2 := by positivity
              have hinv : ‖z - a‖⁻¹ ≤ (‖a‖ / 2)⁻¹ := by
                simpa [one_div] using one_div_le_one_div_of_le hhalf_pos hza_lower
              have hhalf_inv : (‖a‖ / 2)⁻¹ = 2 * ‖a‖⁻¹ := by field_simp [ha_norm_pos.ne']
              simpa [hhalf_inv] using hinv
      _ = (2 * R) * (‖a‖⁻¹ ^ (2 : ℕ)) := by ring
  simpa [u, a] using hnorm

theorem hasProdUniformlyOn_divisorCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ) {K : Set ℂ} (hK : IsCompact K)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1))) :
    HasProdUniformlyOn
      (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) =>
        weierstrassFactor m (z / divisorZeroIndex₀Val p))
      (divisorCanonicalProduct m f (Set.univ : Set ℂ)) K := by
  rcases (isBounded_iff_forall_norm_le.1 hK.isBounded) with ⟨R0, hR0⟩
  set R : ℝ := max R0 1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hnormK : ∀ z ∈ K, ‖z‖ ≤ R := fun z hzK => le_trans (hR0 z hzK) (le_max_left _ _)
  let g : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ :=
    fun p z => weierstrassFactor m (z / divisorZeroIndex₀Val p) - 1
  let u : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
    fun p => (4 * R ^ (m + 1)) * (‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1))
  have hu : Summable u := h_sum.mul_left (4 * R ^ (m + 1))
  have h_big :
      ∀ᶠ p : divisorZeroIndex₀ f (Set.univ : Set ℂ) in Filter.cofinite,
        (2 * R : ℝ) < ‖divisorZeroIndex₀Val p‖ := by
    have hfin :
        ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀Val p‖ ≤ 2 * R} :
            Set _).Finite := by
      have : Metric.closedBall (0 : ℂ) (2 * R) ⊆ (Set.univ : Set ℂ) := by simp
      exact divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ)) (B := 2 * R) this
    have := hfin.eventually_cofinite_notMem
    filter_upwards [this] with p hp
    have : ¬ ‖divisorZeroIndex₀Val p‖ ≤ 2 * R := by simpa using hp
    exact lt_of_not_ge this
  have hBound :
      ∀ᶠ p in Filter.cofinite, ∀ z ∈ K, ‖g p z‖ ≤ u p := by
    filter_upwards [h_big] with p hp z hzK
    have hzle : ‖z‖ ≤ R := hnormK z hzK
    have hz_div : ‖z / divisorZeroIndex₀Val p‖ ≤ (1 / 2 : ℝ) := by
      exact norm_div_le_half_of_norm_le_of_two_mul_lt hRpos hzle hp
    have hE :
        ‖weierstrassFactor m (z / divisorZeroIndex₀Val p) - 1‖ ≤
          4 * ‖z / divisorZeroIndex₀Val p‖ ^ (m + 1) :=
      weierstrassFactor_sub_one_pow_bound (m := m) (z := z / divisorZeroIndex₀Val p) hz_div
    have hz_pow :
        ‖z / divisorZeroIndex₀Val p‖ ^ (m + 1) ≤
          (R ^ (m + 1)) * (‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1)) := by
      have : ‖z / divisorZeroIndex₀Val p‖ = ‖z‖ * ‖divisorZeroIndex₀Val p‖⁻¹ := by
        simp [div_eq_mul_inv]
      rw [this]
      have : (‖z‖ * ‖divisorZeroIndex₀Val p‖⁻¹) ^ (m + 1) =
          ‖z‖ ^ (m + 1) * (‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1)) := by
        simp [mul_pow]
      rw [this]
      have hzle_pow : ‖z‖ ^ (m + 1) ≤ R ^ (m + 1) :=
        pow_le_pow_left₀ (norm_nonneg z) hzle (m + 1)
      gcongr
    dsimp [g, u]
    nlinarith [hE, hz_pow]
  have hcts : ∀ p, ContinuousOn (g p) K := by
    intro p
    have hcontE : Continuous (fun z : ℂ => weierstrassFactor m z) :=
      (differentiable_weierstrassFactor m).continuous
    have hdiv : Continuous fun z : ℂ => z / divisorZeroIndex₀Val p := by
      simpa [div_eq_mul_inv] using! (continuous_id.mul continuous_const)
    have hcont : Continuous fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀Val p) :=
      hcontE.comp hdiv
    simpa only [g] using hcont.continuousOn.fun_sub continuous_const.continuousOn
  have hprod :
      HasProdUniformlyOn (fun p z ↦ 1 + g p z) (fun z ↦ ∏' p, (1 + g p z)) K := by
    simpa using
      Summable.hasProdUniformlyOn_one_add (f := g) (u := u) (K := K) hK hu hBound hcts
  simpa [g, divisorCanonicalProduct, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    using! hprod

theorem hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1))) :
    HasProdLocallyUniformlyOn
      (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) =>
        weierstrassFactor m (z / divisorZeroIndex₀Val p))
      (divisorCanonicalProduct m f (Set.univ : Set ℂ))
      (Set.univ : Set ℂ) := by
  refine hasProdLocallyUniformlyOn_of_forall_compact
      (f := fun p z => weierstrassFactor m (z / divisorZeroIndex₀Val p))
      (g := divisorCanonicalProduct m f (Set.univ : Set ℂ))
      (s := (Set.univ : Set ℂ)) isOpen_univ ?_
  intro K hKU hK
  simpa using
    (hasProdUniformlyOn_divisorCanonicalProduct_univ (m := m) (f := f) (K := K) hK h_sum)

theorem differentiableOn_divisorCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1))) :
    DifferentiableOn ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) (Set.univ : Set ℂ) := by
  have hloc :
      TendstoLocallyUniformlyOn
        (fun (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) =>
          ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀Val p))
        (divisorCanonicalProduct m f (Set.univ : Set ℂ))
        Filter.atTop (Set.univ : Set ℂ) := by
    simpa [HasProdLocallyUniformlyOn] using
      (hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum)
  have hF :
      ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in Filter.atTop,
        DifferentiableOn ℂ
          (fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀Val p))
          (Set.univ : Set ℂ) := by
    refine Filter.Eventually.of_forall ?_
    intro s
    have hdiff :
        Differentiable ℂ
          (fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀Val p)) := by
      let F : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ :=
        fun p z => weierstrassFactor m (z / divisorZeroIndex₀Val p)
      have hF' : ∀ p ∈ s, Differentiable ℂ (F p) := by
        intro p hp
        have hdiv : Differentiable ℂ (fun z : ℂ => z / divisorZeroIndex₀Val p) := by
          have : Differentiable ℂ (fun z : ℂ => z * ((divisorZeroIndex₀Val p)⁻¹)) :=
            (differentiable_id : Differentiable ℂ (fun z : ℂ => z)).mul_const
              ((divisorZeroIndex₀Val p)⁻¹)
          simp [div_eq_mul_inv]
        exact (differentiable_weierstrassFactor m).comp hdiv
      simpa [F] using (Differentiable.fun_finsetProd (𝕜 := ℂ) (f := F) (u := s) hF')
    simpa using hdiff.differentiableOn
  have : (Filter.atTop : Filter (Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))).NeBot :=
    Filter.atTop_neBot
  exact hloc.differentiableOn hF isOpen_univ

theorem differentiableAt_divisorCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1))) (z : ℂ) :
    DifferentiableAt ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z :=
  ((differentiableOn_divisorCanonicalProduct_univ m f h_sum) z (by simp)).differentiableAt
    (by simp)

theorem logDeriv_divisorCanonicalProduct_one_eq_tsum
    {f : ℂ → ℂ} {z : ℂ}
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (2 : ℕ)))
    (hz : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), z ≠ divisorZeroIndex₀Val p)
    (hprod_ne : divisorCanonicalProduct 1 f (Set.univ : Set ℂ) z ≠ 0) :
    logDeriv (divisorCanonicalProduct 1 f (Set.univ : Set ℂ)) z =
      ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
        (1 / (z - divisorZeroIndex₀Val p) + 1 / divisorZeroIndex₀Val p) := by
  let Φ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ :=
    fun p w => weierstrassFactor 1 (w / divisorZeroIndex₀Val p)
  have hf : ∀ p, Φ p z ≠ 0 := by
    intro p
    have hp0 : divisorZeroIndex₀Val p ≠ 0 := divisorZeroIndex₀Val_ne_zero p
    refine weierstrassFactor_ne_zero_of_ne_one 1 ?_
    intro h
    exact hz p ((div_eq_one_iff_eq hp0).1 h)
  have hd : ∀ p, DifferentiableOn ℂ (Φ p) (Set.univ : Set ℂ) := by
    intro p
    have hdiv : Differentiable ℂ (fun w : ℂ => w / divisorZeroIndex₀Val p) := by
      have : Differentiable ℂ (fun w : ℂ => w * ((divisorZeroIndex₀Val p)⁻¹)) :=
        (differentiable_id : Differentiable ℂ (fun w : ℂ => w)).mul_const
          ((divisorZeroIndex₀Val p)⁻¹)
      simp [div_eq_mul_inv]
    exact ((differentiable_weierstrassFactor 1).comp hdiv).differentiableOn
  have hm' : Summable fun p => logDeriv (Φ p) z := by
    have hm :
        Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
          1 / (z - divisorZeroIndex₀Val p) + 1 / divisorZeroIndex₀Val p) :=
      summable_logDerivTerms_divisorZeroIndex₀_of_summable_inv_sq h_sum hz
    refine hm.congr ?_
    intro p
    have hp0 : divisorZeroIndex₀Val p ≠ 0 := divisorZeroIndex₀Val_ne_zero p
    simpa [Φ] using
      (Complex.logDeriv_weierstrassFactor_one_div
        (a := divisorZeroIndex₀Val p) (z := z) hp0 (hz p)).symm
  have htend : MultipliableLocallyUniformlyOn Φ (Set.univ : Set ℂ) := by
    have hprod := hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ
      (m := 1) (f := f) h_sum
    simpa [Φ, divisorCanonicalProduct] using hprod.multipliableLocallyUniformlyOn
  have hnez : (∏' p, Φ p z) ≠ 0 := by
    simpa [Φ, divisorCanonicalProduct] using hprod_ne
  have hlog : logDeriv (∏' p, Φ p ·) z = ∑' p, logDeriv (Φ p) z :=
    logDeriv_tprod_eq_tsum (s := (Set.univ : Set ℂ)) isOpen_univ (by simp)
      hf hd hm' htend hnez
  calc
    logDeriv (divisorCanonicalProduct 1 f (Set.univ : Set ℂ)) z
        = ∑' p, logDeriv (Φ p) z := by
          simpa [Φ, divisorCanonicalProduct] using! hlog
    _ = ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
          (1 / (z - divisorZeroIndex₀Val p) + 1 / divisorZeroIndex₀Val p) := by
          refine tsum_congr fun p => ?_
          have hp0 : divisorZeroIndex₀Val p ≠ 0 := divisorZeroIndex₀Val_ne_zero p
          simpa [Φ] using
            Complex.logDeriv_weierstrassFactor_one_div
              (a := divisorZeroIndex₀Val p) (z := z) hp0 (hz p)

end Complex.Hadamard
end HadamardSourceScope07

section HadamardSourceScope09

noncomputable section

open Set
open scoped Topology BigOperators

namespace Complex.Hadamard

open _root_.Complex

lemma divisor_univ_eq_analyticOrderNatAt_int {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) :
    MeromorphicOn.divisor f (Set.univ : Set ℂ) z = (analyticOrderNatAt f z : ℤ) := by
  have hmero : MeromorphicOn f (Set.univ : Set ℂ) := by
    intro w hw
    exact (Differentiable.analyticAt (f := f) hf w).meromorphicAt
  simp only
    [MeromorphicOn.divisor_apply hmero (by simp : z ∈ (Set.univ : Set ℂ)), analyticOrderNatAt]
  have han : AnalyticAt ℂ f z := Differentiable.analyticAt (f := f) hf z
  cases h : analyticOrderAt f z with
  | top =>
      simp [han.meromorphicOrderAt_eq, h]
  | coe n =>
      simp [han.meromorphicOrderAt_eq, h]

theorem divisorZeroIndex₀_fiber_finite (f : ℂ → ℂ) (z₀ : ℂ) :
    ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | divisorZeroIndex₀Val p = z₀} :
      Set _).Finite := by
  have hsub :
      ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | divisorZeroIndex₀Val p = z₀} : Set _)
        ⊆ ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀Val p‖ ≤ ‖z₀‖} :
          Set _) := by
    intro p hp
    have : divisorZeroIndex₀Val p = z₀ := hp
    simp [this]
  have hfin :
      ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀Val p‖ ≤ ‖z₀‖} :
        Set _).Finite := by
    have : Metric.closedBall (0 : ℂ) ‖z₀‖ ⊆ (Set.univ : Set ℂ) := by simp
    simpa using (divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ))
      (B := ‖z₀‖) this)
  exact hfin.subset hsub

def divisorZeroIndex₀FiberFinset (f : ℂ → ℂ) (z₀ : ℂ) :
    Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) :=
  (divisorZeroIndex₀_fiber_finite (f := f) z₀).toFinset

@[simp]
lemma mem_divisorZeroIndex₀FiberFinset (f : ℂ → ℂ) (z₀ : ℂ)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    p ∈ divisorZeroIndex₀FiberFinset (f := f) z₀ ↔ divisorZeroIndex₀Val p = z₀ := by
  simp [divisorZeroIndex₀FiberFinset]

theorem eventually_atTop_subset_fiberFinset
    (f : ℂ → ℂ) (z₀ : ℂ) :
    ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
      divisorZeroIndex₀FiberFinset (f := f) z₀ ⊆ s := by
  refine (Filter.eventually_atTop.2 ?_)
  refine ⟨divisorZeroIndex₀FiberFinset (f := f) z₀, ?_⟩
  intro s hs
  exact hs

lemma divisorZeroIndex₀FiberFinset_card_eq_toNat_divisor (f : ℂ → ℂ) {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    (divisorZeroIndex₀FiberFinset (f := f) z₀).card =
      Int.toNat (MeromorphicOn.divisor f (Set.univ : Set ℂ) z₀) := by
  let S : Set (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := {p | divisorZeroIndex₀Val p = z₀}
  have hS : S.Finite := divisorZeroIndex₀_fiber_finite (f := f) z₀
  set n : ℕ := Int.toNat (MeromorphicOn.divisor f (Set.univ : Set ℂ) z₀)
  have hcard : Nat.card S = n := by
    classical
    have : Fintype S := hS.fintype
                                                                                      
    let e : S ≃ Fin n :=
      { toFun := by
          intro x
          rcases x with ⟨p, hp⟩
          rcases p with ⟨⟨z, q⟩, hz⟩
          have hzEq : z = z₀ := by simpa [divisorZeroIndex₀Val] using! hp
          subst hzEq
          simpa [n] using q
        invFun := by
          intro q
          refine ⟨⟨⟨z₀, ?_⟩, hz₀⟩, ?_⟩
          · simpa [n] using q
          · simp [S, divisorZeroIndex₀Val]
        left_inv := by
          rintro ⟨p, hp⟩
          rcases p with ⟨⟨z, q⟩, hz⟩
          have hzEq : z = z₀ := by simpa [divisorZeroIndex₀Val] using! hp
          subst hzEq
          (ext; rfl)
        right_inv := by
          intro q
          rfl }
    have h := Nat.card_congr (α := S) (β := Fin n) e
    simpa using (h.trans (by simp))
  have hSncard : S.ncard = n := by
    simpa [Nat.card_coe_set_eq] using hcard
  have hto : hS.toFinset = divisorZeroIndex₀FiberFinset (f := f) z₀ := by
    rfl
  have htoFinset : S.ncard = (divisorZeroIndex₀FiberFinset (f := f) z₀).card := by
    have h' : S.ncard = hS.toFinset.card := Set.ncard_eq_toFinset_card S hS
    simpa [hto] using h'
  exact htoFinset.symm.trans hSncard

lemma divisorZeroIndex₀FiberFinset_card_eq_analyticOrderNatAt
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    (divisorZeroIndex₀FiberFinset (f := f) z₀).card = analyticOrderNatAt f z₀ := by
  have hdiv :
      MeromorphicOn.divisor f (Set.univ : Set ℂ) z₀ = (analyticOrderNatAt f z₀ : ℤ) :=
    divisor_univ_eq_analyticOrderNatAt_int (f := f) hf z₀
  have htoNat : Int.toNat (MeromorphicOn.divisor f (Set.univ : Set ℂ) z₀) =
    analyticOrderNatAt f z₀ := by
    simp [hdiv]
  exact (divisorZeroIndex₀FiberFinset_card_eq_toNat_divisor (f := f) (z₀ := z₀) hz₀).trans htoNat

lemma not_mem_divisorZeroIndex₀FiberFinset_iff_val_ne
    {f : ℂ → ℂ} (z₀ : ℂ) (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    p ∉ divisorZeroIndex₀FiberFinset (f := f) z₀ ↔ divisorZeroIndex₀Val p ≠ z₀ := by
  simp [mem_divisorZeroIndex₀FiberFinset]

end Complex.Hadamard
end
end HadamardSourceScope09

section HadamardSourceScope10

open Filter _root_.Function _root_.Complex _root_.Erdos970.Complex Finset Topology
open scoped Topology BigOperators
open Set

namespace Complex.Hadamard

open _root_.Complex

noncomputable def divisorComplementFactor
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) : ℂ := by
  classical
  exact if p ∈ divisorZeroIndex₀FiberFinset (f := f) z₀ then (1 : ℂ)
    else weierstrassFactor m (z / divisorZeroIndex₀Val p)

@[simp]
theorem divisorComplementFactor_eq_one_of_mem
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ)
    (hp : p ∈ divisorZeroIndex₀FiberFinset (f := f) z₀) :
    divisorComplementFactor m f z₀ p z = 1 := by
  classical
  simp [divisorComplementFactor, hp]

@[simp]
theorem divisorComplementFactor_eq_weierstrassFactor_of_not_mem
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ)
    (hp : p ∉ divisorZeroIndex₀FiberFinset (f := f) z₀) :
    divisorComplementFactor m f z₀ p z =
      weierstrassFactor m (z / divisorZeroIndex₀Val p) := by
  classical
  simp [divisorComplementFactor, hp]

lemma divisorComplementFactor_def
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) :
    divisorComplementFactor m f z₀ p z =
      if divisorZeroIndex₀Val p = z₀ then (1 : ℂ)
      else weierstrassFactor m (z / divisorZeroIndex₀Val p) := by
  classical
  by_cases h : divisorZeroIndex₀Val p = z₀
  · have hp : p ∈ divisorZeroIndex₀FiberFinset (f := f) z₀ := by
      simpa [mem_divisorZeroIndex₀FiberFinset] using h
    simp [divisorComplementFactor_eq_one_of_mem, hp, h]
  · have hp : p ∉ divisorZeroIndex₀FiberFinset (f := f) z₀ := by
      intro hmem
      exact h ((mem_divisorZeroIndex₀FiberFinset f z₀ p).1 hmem)
    simp [divisorComplementFactor_eq_weierstrassFactor_of_not_mem, hp, h]

noncomputable def divisorPartialProduct (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) : ℂ :=
  ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀Val p)

theorem differentiable_weierstrassFactor_divisorZeroIndex₀ (m : ℕ) {f : ℂ → ℂ}
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    Differentiable ℂ (fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀Val p)) := by
  have hdiv : Differentiable ℂ (fun z : ℂ => z / divisorZeroIndex₀Val p) := by
    simp [div_eq_mul_inv]
  exact (differentiable_weierstrassFactor m).comp hdiv

theorem differentiable_divisorPartialProduct (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) :
    Differentiable ℂ (divisorPartialProduct m f s) := by
  let Φ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ :=
    fun p z => weierstrassFactor m (z / divisorZeroIndex₀Val p)
  have hΦ : ∀ p ∈ s, Differentiable ℂ (Φ p) := by
    intro p _hp
    exact differentiable_weierstrassFactor_divisorZeroIndex₀ m p
  simpa [divisorPartialProduct, Φ] using!
    (Differentiable.fun_finsetProd (𝕜 := ℂ) (f := Φ) (u := s) hΦ)

theorem analyticAt_divisorPartialProduct (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z₀ : ℂ) :
    AnalyticAt ℂ (divisorPartialProduct m f s) z₀ :=
  (differentiable_divisorPartialProduct m f s).analyticAt z₀

noncomputable def divisorComplementPartialProduct
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) : ℂ :=
  ∏ p ∈ s, divisorComplementFactor m f z₀ p z

@[simp]
lemma divisorComplementPartialProduct_def
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) :
    divisorComplementPartialProduct m f z₀ s z =
      ∏ p ∈ s, if divisorZeroIndex₀Val p = z₀ then (1 : ℂ)
        else weierstrassFactor m (z / divisorZeroIndex₀Val p) := by
  simp [divisorComplementPartialProduct, divisorComplementFactor,
    mem_divisorZeroIndex₀FiberFinset]

theorem differentiable_divisorComplementPartialProduct
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) :
    Differentiable ℂ (divisorComplementPartialProduct m f z₀ s) := by
  let Φ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ :=
    fun p z => divisorComplementFactor m f z₀ p z
  have hΦ : ∀ p ∈ s, Differentiable ℂ (Φ p) := by
    intro p _hp
    by_cases hpF : p ∈ divisorZeroIndex₀FiberFinset (f := f) z₀
    · have hΦp : Φ p = fun _ => (1 : ℂ) := by
        ext z
        simp only [Φ, divisorComplementFactor_eq_one_of_mem m f z₀ p z hpF]
      rw [hΦp]
      exact differentiable_const (1 : ℂ)
    · have hΦp : Φ p = fun z => weierstrassFactor m (z / divisorZeroIndex₀Val p) := by
        ext z
        simp only [Φ, divisorComplementFactor_eq_weierstrassFactor_of_not_mem m f z₀ p z hpF]
      rw [hΦp]
      exact differentiable_weierstrassFactor_divisorZeroIndex₀ m p
  have hEq : (fun z : ℂ => ∏ p ∈ s, Φ p z) =
      divisorComplementPartialProduct m f z₀ s := by
    ext z
    simp [Φ, divisorComplementPartialProduct]
  have : Differentiable ℂ (fun z : ℂ => ∏ p ∈ s, Φ p z) := by
    simpa using (Differentiable.fun_finsetProd (𝕜 := ℂ) (f := Φ) (u := s) hΦ)
  simpa [hEq] using this

noncomputable def divisorComplementCanonicalProduct
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) (z : ℂ) : ℂ :=
  ∏' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), divisorComplementFactor m f z₀ p z

theorem hasProdUniformlyOn_divisorComplementCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) {K : Set ℂ} (hK : IsCompact K)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1))) :
    HasProdUniformlyOn (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) =>
        divisorComplementFactor m f z₀ p z) (divisorComplementCanonicalProduct m f z₀)
      K := by
  rcases (isBounded_iff_forall_norm_le.1 hK.isBounded) with ⟨R0, hR0⟩
  set R : ℝ := max R0 1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hnormK : ∀ z ∈ K, ‖z‖ ≤ R := fun z hzK => le_trans (hR0 z hzK) (le_max_left _ _)
  let term : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ := fun p z =>
    divisorComplementFactor m f z₀ p z
  let g : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ := fun p z => term p z - 1
  let u : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
    fun p => (4 * R ^ (m + 1)) * (‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1))
  have hu : Summable u := h_sum.mul_left (4 * R ^ (m + 1))
  have h_big :
      ∀ᶠ p : divisorZeroIndex₀ f (Set.univ : Set ℂ) in Filter.cofinite,
        (2 * R : ℝ) < ‖divisorZeroIndex₀Val p‖ := by
    have hfin :
        ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀Val p‖ ≤ 2 * R} :
          Set _).Finite := by
      have : Metric.closedBall (0 : ℂ) (2 * R) ⊆ (Set.univ : Set ℂ) := by simp
      exact divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ)) (B := 2 * R) this
    have := hfin.eventually_cofinite_notMem
    filter_upwards [this] with p hp
    have : ¬ ‖divisorZeroIndex₀Val p‖ ≤ 2 * R := by simpa using hp
    exact lt_of_not_ge this
  have hBound :
      ∀ᶠ p in Filter.cofinite, ∀ z ∈ K, ‖g p z‖ ≤ u p := by
    filter_upwards [h_big] with p hp z hzK
    by_cases hpF : p ∈ divisorZeroIndex₀FiberFinset (f := f) z₀
    · have hval : divisorZeroIndex₀Val p = z₀ :=
        (mem_divisorZeroIndex₀FiberFinset (f := f) (z₀ := z₀) p).1 hpF
      have hu0 : 0 ≤ u p := by
        dsimp [u]
        refine mul_nonneg ?_ ?_
        · nlinarith [pow_nonneg (show 0 ≤ R from le_of_lt hRpos) (m + 1)]
        · exact pow_nonneg (inv_nonneg.2 (norm_nonneg _)) (m + 1)
      simp [g, term, divisorComplementFactor, hval, hu0, sub_eq_add_neg]
    · have hzle : ‖z‖ ≤ R := hnormK z hzK
      have hz_div : ‖z / divisorZeroIndex₀Val p‖ ≤ (1 / 2 : ℝ) := by
        have h2R_pos : 0 < (2 * R : ℝ) := by nlinarith [hRpos]
        have hinv : ‖divisorZeroIndex₀Val p‖⁻¹ < (2 * R)⁻¹ := by
          simpa [one_div] using (one_div_lt_one_div_of_lt h2R_pos hp)
        have hmul_le : ‖z‖ * ‖divisorZeroIndex₀Val p‖⁻¹ ≤ R * ‖divisorZeroIndex₀Val p‖⁻¹ := by
          refine mul_le_mul_of_nonneg_right hzle ?_
          exact inv_nonneg.2 (norm_nonneg _)
        have hmul_lt : R * ‖divisorZeroIndex₀Val p‖⁻¹ < R * (2 * R)⁻¹ :=
          mul_lt_mul_of_pos_left hinv hRpos
        have hlt : ‖z‖ * ‖divisorZeroIndex₀Val p‖⁻¹ < R * (2 * R)⁻¹ :=
          lt_of_le_of_lt hmul_le hmul_lt
        have hRhalf : R * (2 * R)⁻¹ = (1 / 2 : ℝ) := by
          have hRne : (R : ℝ) ≠ 0 := hRpos.ne'
          have : R * (2 * R)⁻¹ = R / (2 * R) := by simp [div_eq_mul_inv]
          rw [this]
          field_simp [hRne]
        have hnorm : ‖z / divisorZeroIndex₀Val p‖ = ‖z‖ * ‖divisorZeroIndex₀Val p‖⁻¹ := by
          simp [div_eq_mul_inv]
        have hzlt : ‖z / divisorZeroIndex₀Val p‖ < (1 / 2 : ℝ) := by
          calc
            ‖z / divisorZeroIndex₀Val p‖ = ‖z‖ * ‖divisorZeroIndex₀Val p‖⁻¹ := hnorm
            _ < R * (2 * R)⁻¹ := hlt
            _ = (1 / 2 : ℝ) := hRhalf
        exact le_of_lt hzlt
      have hE : ‖weierstrassFactor m (z / divisorZeroIndex₀Val p) - 1‖ ≤
            4 * ‖z / divisorZeroIndex₀Val p‖ ^ (m + 1) :=
        weierstrassFactor_sub_one_pow_bound (m := m) (z := z / divisorZeroIndex₀Val p) hz_div
      have hz_pow : ‖z / divisorZeroIndex₀Val p‖ ^ (m + 1) ≤
            (R ^ (m + 1)) * (‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1)) := by
        have : ‖z / divisorZeroIndex₀Val p‖ = ‖z‖ * ‖divisorZeroIndex₀Val p‖⁻¹ := by
          simp [div_eq_mul_inv]
        rw [this]
        have : (‖z‖ * ‖divisorZeroIndex₀Val p‖⁻¹) ^ (m + 1) =
            ‖z‖ ^ (m + 1) * (‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1)) := by
          simp [mul_pow]
        rw [this]
        have hzle_pow : ‖z‖ ^ (m + 1) ≤ R ^ (m + 1) :=
          pow_le_pow_left₀ (norm_nonneg z) hzle (m + 1)
        gcongr
      dsimp [g, term, u]
      simp [divisorComplementFactor, hpF] at *
      nlinarith [hE, hz_pow]
  have hcts : ∀ p, ContinuousOn (g p) K := by
    intro p
    by_cases hpF : p ∈ divisorZeroIndex₀FiberFinset (f := f) z₀
    · have hval : divisorZeroIndex₀Val p = z₀ :=
        (mem_divisorZeroIndex₀FiberFinset (f := f) (z₀ := z₀) p).1 hpF
      simpa [g, term, divisorComplementFactor, hval, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm] using
        (continuousOn_const : ContinuousOn (fun _ : ℂ => (0 : ℂ)) K)
    · have hvalne : divisorZeroIndex₀Val p ≠ z₀ :=
        (not_mem_divisorZeroIndex₀FiberFinset_iff_val_ne (f := f) z₀ p).1 hpF
      have hcontE : Continuous (fun z : ℂ => weierstrassFactor m z) :=
        (differentiable_weierstrassFactor m).continuous
      have hdiv : Continuous fun z : ℂ => z / divisorZeroIndex₀Val p := by
        simpa [div_eq_mul_inv] using! (continuous_id.mul continuous_const)
      have hcont : Continuous fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀Val p) :=
        hcontE.comp hdiv
      have : ContinuousOn (fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀Val p) - 1) K :=
        (hcont.continuousOn.sub continuous_const.continuousOn)
      simpa [g, term, divisorComplementFactor, mem_divisorZeroIndex₀FiberFinset, hvalne] using this
  have hprod :
      HasProdUniformlyOn (fun p z ↦ 1 + g p z) (fun z ↦ ∏' p, (1 + g p z)) K := by
    simpa using
      Summable.hasProdUniformlyOn_one_add (f := g) (u := u) (K := K) hK hu hBound hcts
  have hterm :
      HasProdUniformlyOn (fun p z ↦ term p z) (fun z ↦ ∏' p, term p z) K := by
    simpa [g, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hprod
  refine hterm.congr_right ?_
  intro z hz
  simp [term, divisorComplementCanonicalProduct, divisorComplementFactor]

theorem hasProdLocallyUniformlyOn_divisorComplementCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1))) :
    HasProdLocallyUniformlyOn
      (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) =>
        divisorComplementFactor m f z₀ p z)
      (divisorComplementCanonicalProduct m f z₀)
      (Set.univ : Set ℂ) := by
  refine hasProdLocallyUniformlyOn_of_forall_compact
      (f := fun p z => divisorComplementFactor m f z₀ p z)
      (g := divisorComplementCanonicalProduct m f z₀) (s := (Set.univ : Set ℂ))
      isOpen_univ ?_
  intro K hKU hK
  simpa using
    (hasProdUniformlyOn_divisorComplementCanonicalProduct_univ (m := m) (f := f) (z₀ := z₀)
      (K := K) hK h_sum)

theorem tendstoLocallyUniformlyOn_divisorComplementPartialProduct_univ
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1))) :
    TendstoLocallyUniformlyOn
      (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
        divisorComplementPartialProduct m f z₀ s)
      (divisorComplementCanonicalProduct m f z₀)
      Filter.atTop
      (Set.univ : Set ℂ) := by
  have hprod :
      HasProdLocallyUniformlyOn
        (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) =>
          divisorComplementFactor m f z₀ p z)
        (divisorComplementCanonicalProduct m f z₀)
        (Set.univ : Set ℂ) :=
    hasProdLocallyUniformlyOn_divisorComplementCanonicalProduct_univ (m := m) (f := f)
      (z₀ := z₀) h_sum
  have h :
      TendstoLocallyUniformlyOn
        (fun (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) =>
          ∏ p ∈ s,
            if divisorZeroIndex₀Val p = z₀ then (1 : ℂ)
            else weierstrassFactor m (z / divisorZeroIndex₀Val p))
        (divisorComplementCanonicalProduct m f z₀)
        Filter.atTop
        (Set.univ : Set ℂ) := by
    simpa [HasProdLocallyUniformlyOn, divisorComplementFactor, mem_divisorZeroIndex₀FiberFinset]
      using hprod
  refine h.congr (G := fun s z => divisorComplementPartialProduct m f z₀ s z) ?_
  intro s z hz
  simp [divisorComplementPartialProduct_def]

theorem differentiableOn_divisorComplementCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1))) :
    DifferentiableOn ℂ (divisorComplementCanonicalProduct m f z₀) (Set.univ : Set ℂ) := by
  have hloc :
      TendstoLocallyUniformlyOn
        (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          divisorComplementPartialProduct m f z₀ s)
        (divisorComplementCanonicalProduct m f z₀)
        Filter.atTop
        (Set.univ : Set ℂ) :=
    tendstoLocallyUniformlyOn_divisorComplementPartialProduct_univ (m := m) (f := f)
      (z₀ := z₀) h_sum
  have hF :
      ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in Filter.atTop,
        DifferentiableOn ℂ (divisorComplementPartialProduct m f z₀ s) (Set.univ : Set ℂ) := by
    refine Filter.Eventually.of_forall ?_
    intro s
    exact (differentiable_divisorComplementPartialProduct m f z₀ s).differentiableOn
  have : (Filter.atTop : Filter (Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))).NeBot :=
    Filter.atTop_neBot
  exact hloc.differentiableOn hF isOpen_univ

lemma divisorPartialProduct_eq_fiber_mul_complement_of_subset
    (m : ℕ) (f : ℂ → ℂ) (z₀ z : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
    (hs : divisorZeroIndex₀FiberFinset (f := f) z₀ ⊆ s) :
    divisorPartialProduct m f s z =
      divisorPartialProduct m f (divisorZeroIndex₀FiberFinset (f := f) z₀) z *
        divisorComplementPartialProduct m f z₀ s z := by
  classical          
  let fiber : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) :=
    divisorZeroIndex₀FiberFinset (f := f) z₀
  let P : divisorZeroIndex₀ f (Set.univ : Set ℂ) → Prop := fun p => p ∈ fiber
  let term : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ :=
    fun p => weierstrassFactor m (z / divisorZeroIndex₀Val p)
  have hfilter : s.filter P = fiber := by
    ext p
    constructor
    · intro hp
      exact (Finset.mem_filter.mp hp).2
    · intro hp
      exact Finset.mem_filter.mpr ⟨hs hp, hp⟩
  have hsplit :
      (∏ p ∈ s with P p, term p) * (∏ p ∈ s with ¬ P p, term p) = ∏ p ∈ s, term p := by
    simpa [term] using
      (Finset.prod_filter_mul_prod_filter_not (s := s) (p := P) (f := term))
  have hP : (∏ p ∈ s with P p, term p) = divisorPartialProduct m f fiber z := by
    have hg : ∀ x ∈ s \ fiber, (if x ∈ fiber then term x else (1 : ℂ)) = 1 := by
      intro x hx
      have hxnot : x ∉ fiber := (Finset.mem_sdiff.mp hx).2
      simp [hxnot]
    have hfg :
        ∀ x ∈ fiber, term x = (if x ∈ fiber then term x else (1 : ℂ)) := by
      intro x hx
      simp [hx]
    have hsub := (Finset.prod_subset_one_on_sdiff (s₁ := fiber) (s₂ := s)
        (f := term) (g := fun x => if x ∈ fiber then term x else (1 : ℂ)) hs hg hfg)
    simpa [divisorPartialProduct, term, P, fiber, Finset.prod_filter] using hsub.symm
  have hnotP : (∏ p ∈ s with ¬ P p, term p) = divisorComplementPartialProduct m f z₀ s z := by
    simp [divisorComplementPartialProduct, divisorComplementFactor, term, P, fiber,
      Finset.prod_filter, mem_divisorZeroIndex₀FiberFinset]
  have hsplit' : ∏ p ∈ s, term p = (∏ p ∈ s with P p, term p) * (∏ p ∈ s with ¬ P p, term p) :=
    hsplit.symm
  calc
    divisorPartialProduct m f s z
        = ∏ p ∈ s, term p := by simp [divisorPartialProduct, term]
    _ = (∏ p ∈ s with P p, term p) * (∏ p ∈ s with ¬ P p, term p) := hsplit'
    _ = divisorPartialProduct m f fiber z * divisorComplementPartialProduct m f z₀ s z := by
      simp [hP, hnotP, fiber]

end Complex.Hadamard
end HadamardSourceScope10

section HadamardSourceScope11

noncomputable section

open _root_.Complex _root_.Erdos970.Complex Filter _root_.Function Finset Topology
open scoped Topology BigOperators
open Set

namespace Complex.Hadamard

open _root_.Complex

theorem analyticOrderAt_finset_prod_weierstrassFactor_divisorZeroIndex₀
    (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z₀ : ℂ) :
    analyticOrderAt (fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀Val p))
        z₀ = ((s.filter (fun p => divisorZeroIndex₀Val p = z₀)).card : ℕ∞) := by
  classical          
  refine Finset.induction_on s ?base ?step
  · simp [analyticOrderAt_eq_zero]
  · intro p s hp hs
    by_cases hEq : divisorZeroIndex₀Val p = z₀
    · have hp0 : divisorZeroIndex₀Val p ≠ 0 := p.property
      have han_fac :
          AnalyticAt ℂ (fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀Val p)) z₀ := by
        exact (differentiable_weierstrassFactor_divisorZeroIndex₀ m p).analyticAt z₀
      have han_rest : AnalyticAt ℂ (fun z : ℂ => ∏ q ∈ s, weierstrassFactor m
          (z / divisorZeroIndex₀Val q)) z₀ := by
        simpa [divisorPartialProduct] using! analyticAt_divisorPartialProduct m f s z₀
      let fac : ℂ → ℂ := fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀Val p)
      let rest : ℂ → ℂ := fun z : ℂ => ∏ q ∈ s, weierstrassFactor m (z / divisorZeroIndex₀Val q)
      have hmul :
          analyticOrderAt (fac * rest) z₀ =
            analyticOrderAt fac z₀ + analyticOrderAt rest z₀ := by
        simpa [fac, rest] using (analyticOrderAt_mul (z₀ := z₀) han_fac han_rest)
      have hcard :
          (Finset.filter (fun q => divisorZeroIndex₀Val q = z₀) (insert p s)).card =
            (Finset.filter (fun q => divisorZeroIndex₀Val q = z₀) s).card + 1 := by
        simp [hEq, hp, Finset.filter_insert]
      have hfac : analyticOrderAt fac z₀ = (1 : ℕ∞) := by
        simpa [fac, hEq] using
          (analyticOrderAt_weierstrassFactor_div_self (m := m) (a := divisorZeroIndex₀Val p) hp0)
      have hrest : analyticOrderAt rest z₀ = ((s.filter
          (fun q => divisorZeroIndex₀Val q = z₀)).card : ℕ∞) := by
        simpa [rest] using hs
      have hcongr :
          (fun z : ℂ => ∏ q ∈ insert p s, weierstrassFactor m (z / divisorZeroIndex₀Val q))
            =ᶠ[𝓝 z₀] (fac * rest) := by
        refine Filter.Eventually.of_forall ?_
        intro z
        simp [fac, rest, Finset.prod_insert, hp, Pi.mul_apply]
      calc
        analyticOrderAt (fun z : ℂ => ∏ q ∈ insert p s, weierstrassFactor m
            (z / divisorZeroIndex₀Val q)) z₀ = analyticOrderAt (fac * rest) z₀ := by
              simpa using (analyticOrderAt_congr hcongr)
        _ = analyticOrderAt fac z₀ + analyticOrderAt rest z₀ := hmul
        _ = (1 : ℕ∞) + ((s.filter (fun q => divisorZeroIndex₀Val q = z₀)).card : ℕ∞) := by
              simp [hfac, hrest]
        _ = (((insert p s).filter (fun q => divisorZeroIndex₀Val q = z₀)).card : ℕ∞) := by
              simp [hcard, Nat.add_comm]
    · have han_fac :
          AnalyticAt ℂ (fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀Val p)) z₀ := by
        exact (differentiable_weierstrassFactor_divisorZeroIndex₀ m p).analyticAt z₀
      have hfac0 : analyticOrderAt (fun z : ℂ => weierstrassFactor m
          (z / divisorZeroIndex₀Val p)) z₀ = 0 := by
        have hp0 : divisorZeroIndex₀Val p ≠ 0 := p.property
        have hval : weierstrassFactor m (z₀ / divisorZeroIndex₀Val p) ≠ 0 := by
          have : (z₀ / divisorZeroIndex₀Val p) ≠ 1 := by
            intro h1
            have : z₀ = divisorZeroIndex₀Val p := by
              have : z₀ = (z₀ / divisorZeroIndex₀Val p) * (divisorZeroIndex₀Val p) := by
                simp [div_eq_mul_inv]
              simpa [h1, div_eq_mul_inv, hp0] using this
            exact hEq (this.symm)
          exact (weierstrassFactor_ne_zero_iff m (z₀ / divisorZeroIndex₀Val p)).2 this
        simpa using (han_fac.analyticOrderAt_eq_zero).2 (by simpa using hval)
      have hcard :
          (Finset.filter (fun q => divisorZeroIndex₀Val q = z₀) (insert p s)).card =
            (Finset.filter (fun q => divisorZeroIndex₀Val q = z₀) s).card := by
        simp [hEq, Finset.filter_insert]
      have han_rest : AnalyticAt ℂ (fun z : ℂ => ∏ q ∈ s, weierstrassFactor m
          (z / divisorZeroIndex₀Val q)) z₀ := by
        simpa [divisorPartialProduct] using! analyticAt_divisorPartialProduct m f s z₀
      let fac : ℂ → ℂ := fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀Val p)
      let rest : ℂ → ℂ := fun z : ℂ => ∏ q ∈ s, weierstrassFactor m (z / divisorZeroIndex₀Val q)
      have hmul :
          analyticOrderAt (fac * rest) z₀ =
            analyticOrderAt fac z₀ + analyticOrderAt rest z₀ := by
        simpa [fac, rest] using (analyticOrderAt_mul (z₀ := z₀) han_fac han_rest)
      have hcongr :
          (fun z : ℂ => ∏ q ∈ insert p s, weierstrassFactor m (z / divisorZeroIndex₀Val q))
            =ᶠ[𝓝 z₀] (fac * rest) := by
        refine Filter.Eventually.of_forall ?_
        intro z
        simp [fac, rest, Finset.prod_insert, hp, Pi.mul_apply]
      calc
        analyticOrderAt (fun z : ℂ => ∏ q ∈ insert p s, weierstrassFactor m
        (z / divisorZeroIndex₀Val q)) z₀
            = analyticOrderAt (fac * rest) z₀ := by
              simpa using (analyticOrderAt_congr hcongr)
        _ = analyticOrderAt rest z₀ := by
              calc
                analyticOrderAt (fac * rest) z₀ = analyticOrderAt fac z₀ +
                    analyticOrderAt rest z₀ := hmul
                _ = analyticOrderAt rest z₀ := by
                      have hfac0' : analyticOrderAt fac z₀ = 0 := by
                        simpa [fac] using hfac0
                      simp [hfac0']
        _ = ((s.filter (fun q => divisorZeroIndex₀Val q = z₀)).card : ℕ∞) := by
              simpa [rest] using hs
        _ = (((insert p s).filter (fun q => divisorZeroIndex₀Val q = z₀)).card : ℕ∞) := by
              simpa using congrArg (fun n : ℕ => (n : ℕ∞)) hcard.symm

theorem analyticOrderAt_partialProduct_eq_fiberCard_of_subset
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
    (hs : divisorZeroIndex₀FiberFinset (f := f) z₀ ⊆ s) :
    analyticOrderAt
        (fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀Val p))
        z₀ = ((divisorZeroIndex₀FiberFinset (f := f) z₀).card : ℕ∞) := by
  have h :=
    analyticOrderAt_finset_prod_weierstrassFactor_divisorZeroIndex₀
      (m := m) (f := f) (s := s) (z₀ := z₀)
  have hfilter :
      s.filter (fun p => divisorZeroIndex₀Val p = z₀) =
        divisorZeroIndex₀FiberFinset (f := f) z₀ := by
    ext p
    constructor
    · intro hp'
      have hpv : divisorZeroIndex₀Val p = z₀ := (Finset.mem_filter.mp hp').2
      simpa [mem_divisorZeroIndex₀FiberFinset] using hpv
    · intro hp_fiber
      have hpv : divisorZeroIndex₀Val p = z₀ :=
        (mem_divisorZeroIndex₀FiberFinset (f := f) (z₀ := z₀) p).1 hp_fiber
      have hps : p ∈ s := hs (by simpa [mem_divisorZeroIndex₀FiberFinset] using hpv)
      exact Finset.mem_filter.2 ⟨hps, hpv⟩
  simpa [hfilter] using h

theorem exists_analyticAt_eq_pow_smul_of_partialProduct_contains_fiber
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
    (hs : divisorZeroIndex₀FiberFinset (f := f) z₀ ⊆ s) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧
        (fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀Val p))
          =ᶠ[𝓝 z₀]
          fun z : ℂ => (z - z₀) ^ (divisorZeroIndex₀FiberFinset (f := f) z₀).card • g z := by
  let F : ℂ → ℂ := fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀Val p)
  have hF_ana : AnalyticAt ℂ F z₀ := by
    simpa [F, divisorPartialProduct] using! analyticAt_divisorPartialProduct m f s z₀
  have hOrder :
      analyticOrderAt F z₀ =
        ((divisorZeroIndex₀FiberFinset (f := f) z₀).card : ℕ∞) := by
    simpa [F] using
      (analyticOrderAt_partialProduct_eq_fiberCard_of_subset (m := m)
      (f := f) (z₀ := z₀) (s := s) hs)
  refine (hF_ana.analyticOrderAt_eq_natCast (n := (divisorZeroIndex₀FiberFinset
    (f := f) z₀).card)).1 ?_
  simp [hOrder]

end Complex.Hadamard
end
end HadamardSourceScope11

section HadamardSourceScope12

open Filter _root_.Function _root_.Complex _root_.Erdos970.Complex Finset Topology
open scoped Topology BigOperators
open Set

namespace Complex.Hadamard

open _root_.Complex

theorem tendstoLocallyUniformlyOn_divisorPartialProduct_univ
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1))) :
    TendstoLocallyUniformlyOn
      (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) => divisorPartialProduct m f s)
      (divisorCanonicalProduct m f (Set.univ : Set ℂ))
      Filter.atTop
      (Set.univ : Set ℂ) := by
  have hprod :
      HasProdLocallyUniformlyOn
        (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) =>
          weierstrassFactor m (z / divisorZeroIndex₀Val p))
        (divisorCanonicalProduct m f (Set.univ : Set ℂ))
        (Set.univ : Set ℂ) :=
    hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
  simpa [HasProdLocallyUniformlyOn, divisorPartialProduct] using! hprod

theorem tendstoUniformlyOn_divisorPartialProduct_div_pow_sub
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) (k : ℕ) {K : Set ℂ} (hK : IsCompact K) (hKz : ∀ z ∈ K, z ≠ z₀) :
    TendstoUniformlyOn
      (fun s z => (divisorPartialProduct m f s z) / (z - z₀) ^ k)
      (fun z => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k)
      (Filter.atTop : Filter (Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))))
      K := by
  have hloc :
      TendstoLocallyUniformlyOn
        (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) => divisorPartialProduct m f s)
        (divisorCanonicalProduct m f (Set.univ : Set ℂ))
        Filter.atTop
        K :=
    (tendstoLocallyUniformlyOn_divisorPartialProduct_univ (m := m) (f := f) h_sum).mono
      (by intro z hz; simp)
  have hunif :
      TendstoUniformlyOn
        (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) => divisorPartialProduct m f s)
        (divisorCanonicalProduct m f (Set.univ : Set ℂ))
        Filter.atTop
        K :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).1 hloc
  let h : ℂ → ℂ := fun z => ((z - z₀) ^ k)⁻¹
  have hh : ∃ C, ∀ z ∈ K, ‖h z‖ ≤ C := by
    have hcont : ContinuousOn h K := by
      have hpow : ContinuousOn (fun z : ℂ => (z - z₀) ^ k) K := by
        fun_prop
      refine hpow.inv₀ ?_
      intro z hz
      have hz0 : z - z₀ ≠ 0 := sub_ne_zero.mpr (hKz z hz)
      exact pow_ne_zero k hz0
    have hKimg : IsCompact (h '' K) := hK.image_of_continuousOn hcont
    rcases (isBounded_iff_forall_norm_le.1 hKimg.isBounded) with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro z hz
    exact hC (h z) ⟨z, hz, rfl⟩
  have hunif' :=
    (TendstoUniformlyOn.mul_left_bounded (p := (Filter.atTop : Filter (Finset (divisorZeroIndex₀ f
    (Set.univ : Set ℂ)))))
        (K := K)
        (F := fun s z => divisorPartialProduct m f s z)
        (f := fun z => divisorCanonicalProduct m f (Set.univ : Set ℂ) z)
        (h := h)
        hunif hh)
  simpa [h, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hunif'

theorem tendstoLocallyUniformlyOn_divisorPartialProduct_div_pow_sub
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) (k : ℕ) :
    TendstoLocallyUniformlyOn
      (fun s z => (divisorPartialProduct m f s z) / (z - z₀) ^ k)
      (fun z => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k)
      (Filter.atTop : Filter (Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))))
      ((Set.univ : Set ℂ) \ {z₀}) := by
  have hopen : IsOpen ((Set.univ : Set ℂ) \ {z₀}) := by
    have hset : ((Set.univ : Set ℂ) \ {z₀}) = ({z₀} : Set ℂ)ᶜ := by
      ext z
      simp
    simp [hset]
  refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hopen).2 ?_
  intro K hKsub hK
  have hKz : ∀ z ∈ K, z ≠ z₀ := by
    intro z hzK
    have : z ∈ (Set.univ : Set ℂ) \ {z₀} := hKsub hzK
    exact by simpa [Set.mem_sdiff, Set.mem_singleton_iff] using this.2
  exact tendstoUniformlyOn_divisorPartialProduct_div_pow_sub
    (m := m) (f := f) h_sum (z₀ := z₀) (k := k) (hK := hK) hKz

open Filter

theorem exists_ball_eq_divisorCanonicalProduct_div_pow_eq
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) :
    ∃ ε > 0, ∃ u : ℂ → ℂ, AnalyticAt ℂ u z₀ ∧
      u z₀ ≠ 0 ∧
        ∀ z : ℂ, z ∈ Metric.ball z₀ ε → z ≠ z₀ →
          (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
              (z - z₀) ^ (divisorZeroIndex₀FiberFinset (f := f) z₀).card =
            (divisorComplementCanonicalProduct m f z₀ z) * u z := by
  let fiber : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) :=
    divisorZeroIndex₀FiberFinset (f := f) z₀
  have hfib : ∃ u : ℂ → ℂ, AnalyticAt ℂ u z₀ ∧ u z₀ ≠ 0 ∧
          (fun z : ℂ => divisorPartialProduct m f fiber z) =ᶠ[𝓝 z₀]
            fun z : ℂ => (z - z₀) ^ fiber.card • u z := by
    simpa [fiber, divisorPartialProduct] using
      (exists_analyticAt_eq_pow_smul_of_partialProduct_contains_fiber (m := m) (f := f) (z₀ := z₀)
        (s := fiber) (by rfl : fiber ⊆ fiber))
  rcases hfib with ⟨u, huA, hu0, huEq⟩
  have hmem : {z : ℂ | divisorPartialProduct m f fiber z =
      (z - z₀) ^ fiber.card • u z} ∈ 𝓝 z₀ := huEq
  rcases Metric.mem_nhds_iff.1 hmem with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, u, huA, hu0, ?_⟩
  have hq :
      TendstoLocallyUniformlyOn (fun s z => (divisorPartialProduct m f s z) / (z - z₀) ^ fiber.card)
        (fun z => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ fiber.card)
        (Filter.atTop : Filter (Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))))
        ((Set.univ : Set ℂ) \ {z₀}) :=
    tendstoLocallyUniformlyOn_divisorPartialProduct_div_pow_sub
      (m := m) (f := f) (h_sum := h_sum) (z₀ := z₀) (k := fiber.card)
  have hcomp :
      TendstoLocallyUniformlyOn
        (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          divisorComplementPartialProduct m f z₀ s)
        (divisorComplementCanonicalProduct m f z₀)
        Filter.atTop
        (Set.univ : Set ℂ) :=
    tendstoLocallyUniformlyOn_divisorComplementPartialProduct_univ (m := m) (f := f)
    (z₀ := z₀) h_sum
  intro z hz hzne
  have hz' : z ∈ ((Set.univ : Set ℂ) \ {z₀}) := by
    refine ⟨by simp, ?_⟩
    simpa [Set.mem_singleton_iff] using hzne
  have hF : Tendsto (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          (divisorPartialProduct m f s z) / (z - z₀) ^ fiber.card) (Filter.atTop : Filter _)
        (𝓝 ((divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ fiber.card)) :=
    hq.tendsto_at hz'
  have hG0 : Tendsto  (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          divisorComplementPartialProduct m f z₀ s z) (Filter.atTop : Filter _)
        (𝓝 (divisorComplementCanonicalProduct m f z₀ z)) :=
    hcomp.tendsto_at (by simp : z ∈ (Set.univ : Set ℂ))
  have hG : Tendsto (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          (divisorComplementPartialProduct m f z₀ s z) * u z) (Filter.atTop : Filter _)
        (𝓝 ((divisorComplementCanonicalProduct m f z₀ z) * u z)) :=
    (hG0.mul tendsto_const_nhds)
  have hsub : ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
      fiber ⊆ s := eventually_atTop_subset_fiberFinset (f := f) z₀
  have heq_eventually :
      ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
        (divisorPartialProduct m f s z) / (z - z₀) ^ fiber.card
          = (divisorComplementPartialProduct m f z₀ s z) * u z := by
    filter_upwards [hsub] with s hs
    have hsplit :
        divisorPartialProduct m f s z =
          divisorPartialProduct m f fiber z * divisorComplementPartialProduct m f z₀ s z := by
      simpa [fiber] using
        (divisorPartialProduct_eq_fiber_mul_complement_of_subset (m := m) (f := f) (z₀ := z₀)
          (z := z) (s := s) hs)
    have hfibz :
        divisorPartialProduct m f fiber z = (z - z₀) ^ fiber.card • u z := by
      exact hball hz
    have hzpow : (z - z₀) ^ fiber.card ≠ 0 :=
      pow_ne_zero _ (sub_ne_zero.mpr hzne)
    set a : ℂ := (z - z₀) ^ fiber.card
    have ha : a ≠ 0 := by simpa [a] using hzpow
    set c : ℂ := divisorComplementPartialProduct m f z₀ s z with hc
    rw [hsplit, hfibz, smul_eq_mul]
    calc
      ((a * u z) * c) / a
          = (a * (u z * c)) / a := by simp [mul_assoc]
      _ = u z * c := by
            simpa [mul_assoc] using (mul_div_cancel_left₀ (u z * c) ha)
      _ = c * u z := by ac_rfl
      _ = (divisorComplementPartialProduct m f z₀ s z) * u z := by
            simp [c]
  have hG' :
      Tendsto
        (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          (divisorPartialProduct m f s z) / (z - z₀) ^ fiber.card)
        (Filter.atTop : Filter _)
        (𝓝 ((divisorComplementCanonicalProduct m f z₀ z) * u z)) := by
    have heq' :
        ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
          (divisorComplementPartialProduct m f z₀ s z) * u z
            = (divisorPartialProduct m f s z) / (z - z₀) ^ fiber.card := by
      filter_upwards [heq_eventually] with s hs
      exact hs.symm
    exact (hG.congr' heq')
  exact tendsto_nhds_unique hF hG'

theorem bddAbove_norm_divisorCanonicalProduct_div_pow_puncturedBall
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) : ∃ r > 0, BddAbove (norm ∘ (fun z : ℂ =>
      (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
        (z - z₀) ^ (divisorZeroIndex₀FiberFinset (f := f) z₀).card) ''
      ((Metric.ball z₀ r) \ {z₀})) := by
  rcases exists_ball_eq_divisorCanonicalProduct_div_pow_eq (m := m) (f := f) (h_sum := h_sum)
    (z₀ := z₀) with ⟨ε, hε, u, huA, hu0, hEq⟩
  have huC : ContinuousAt u z₀ := huA.continuousAt
  have hpre : {z : ℂ | ‖u z - u z₀‖ < 1} ∈ 𝓝 z₀ := by
    have : u ⁻¹' Metric.ball (u z₀) (1 : ℝ) ∈ 𝓝 z₀ :=
      huC.preimage_mem_nhds (Metric.ball_mem_nhds (u z₀) (by norm_num))
    simpa [Metric.ball, dist_eq_norm, Set.preimage] using this
  rcases Metric.mem_nhds_iff.1 hpre with ⟨r0, hr0pos, hr0sub⟩
  set r : ℝ := min (ε / 2) r0
  have hrpos : 0 < r := lt_min (by nlinarith [hε]) hr0pos
  have hr_lt_ε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by nlinarith [hε])
  have huBound : ∀ z ∈ Metric.ball z₀ r, ‖u z‖ ≤ ‖u z₀‖ + 1 := by
    intro z hz
    have hz0 : z ∈ Metric.ball z₀ r0 := by
      have : r ≤ r0 := min_le_right _ _
      exact Metric.ball_subset_ball this hz
    have hdiff : ‖u z - u z₀‖ < 1 := hr0sub hz0
    have htri : ‖u z‖ ≤ ‖u z - u z₀‖ + ‖u z₀‖ := by
      simpa [sub_eq_add_neg, add_assoc] using
        (norm_add_le (u z - u z₀) (u z₀))
    have : ‖u z‖ ≤ 1 + ‖u z₀‖ := le_trans htri (by nlinarith [le_of_lt hdiff])
    nlinarith [this]
  have hdiffC :
      DifferentiableOn ℂ (divisorComplementCanonicalProduct m f z₀) (Set.univ : Set ℂ) :=
    differentiableOn_divisorComplementCanonicalProduct_univ (m := m) (f := f) (z₀ := z₀) h_sum
  have hcontC : ContinuousOn (divisorComplementCanonicalProduct m f z₀) (Metric.closedBall z₀ r) :=
    (hdiffC.continuousOn).mono (by intro z hz; simp)
  have hK : IsCompact (Metric.closedBall z₀ r) := isCompact_closedBall _ _
  rcases (isBounded_iff_forall_norm_le.1 (hK.image_of_continuousOn hcontC).isBounded) with ⟨C, hC⟩
  refine ⟨r, hrpos, ⟨C * (‖u z₀‖ + 1), ?_⟩⟩
  rintro _ ⟨z, hzset, rfl⟩
  rcases hzset with ⟨hzr, hzne⟩
  have hz_in_ε : z ∈ Metric.ball z₀ ε := Metric.ball_subset_ball hr_lt_ε.le hzr
  have hz_ne : z ≠ z₀ := by simpa [Set.mem_singleton_iff] using hzne
  have hq :
      (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (divisorZeroIndex₀FiberFinset (f := f) z₀).card
        = divisorComplementCanonicalProduct m f z₀ z * u z :=
    hEq z hz_in_ε hz_ne
  have hCz : ‖divisorComplementCanonicalProduct m f z₀ z‖ ≤ C := by
    have hzK : z ∈ Metric.closedBall z₀ r := Metric.mem_closedBall.2 (le_of_lt hzr)
    exact hC _ ⟨z, hzK, rfl⟩
  have huZ : ‖u z‖ ≤ ‖u z₀‖ + 1 := huBound z hzr
  have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) hCz
  have hmul : ‖divisorComplementCanonicalProduct m f z₀ z * u z‖ ≤ C * (‖u z₀‖ + 1) := by
    calc
      ‖divisorComplementCanonicalProduct m f z₀ z * u z‖
          = ‖divisorComplementCanonicalProduct m f z₀ z‖ * ‖u z‖ := by simp
      _ ≤ C * (‖u z₀‖ + 1) := by
            exact mul_le_mul hCz huZ (norm_nonneg _) hCnonneg
  simpa [Function.comp, hq] using hmul

theorem divisorComplementCanonicalProduct_ne_zero_at
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1))) :
    divisorComplementCanonicalProduct m f z₀ z₀ ≠ 0 := by
  let Φ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ :=
    fun p => if divisorZeroIndex₀Val p = z₀ then (1 : ℂ)
      else weierstrassFactor m (z₀ / divisorZeroIndex₀Val p)
  let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ := fun p => Φ p - 1
  have hΦ_ne : ∀ p, Φ p ≠ 0 := by
    intro p
    by_cases hp : divisorZeroIndex₀Val p = z₀
    · simp [Φ, hp]
    · have hval : divisorZeroIndex₀Val p ≠ z₀ := hp
      have hz : z₀ / divisorZeroIndex₀Val p ≠ (1 : ℂ) := by
        intro h
        by_cases hp0 : divisorZeroIndex₀Val p = 0
        · have : z₀ / divisorZeroIndex₀Val p = (0 : ℂ) := by simp [hp0]
          have h01 := h
          rw [this] at h01
          exact (show False from (by simpa using (show (0 : ℂ) ≠ (1 : ℂ) from by simp) h01))
        · have : z₀ = divisorZeroIndex₀Val p := (div_eq_one_iff_eq hp0).1 h
          exact hval this.symm
      have hE : weierstrassFactor m (z₀ / divisorZeroIndex₀Val p) ≠ 0 := by
        intro h0
        have : z₀ / divisorZeroIndex₀Val p = (1 : ℂ) :=
          (weierstrassFactor_eq_zero_iff (m := m) (z := z₀ / divisorZeroIndex₀Val p)).1 h0
        exact hz this
      simp [Φ, hp, hE]
  have hz0_le : ‖z₀‖ ≤ max ‖z₀‖ 1 := le_max_left _ _
  set R : ℝ := max ‖z₀‖ 1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  let u : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
    fun p => (4 * R ^ (m + 1)) * (‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1))
  have hu : Summable u := h_sum.mul_left (4 * R ^ (m + 1))
  have h_big :
      ∀ᶠ p : divisorZeroIndex₀ f (Set.univ : Set ℂ) in Filter.cofinite,
        (2 * R : ℝ) < ‖divisorZeroIndex₀Val p‖ := by
    have hfin : ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀Val p‖ ≤
        2 * R} : Set _).Finite := by
      have : Metric.closedBall (0 : ℂ) (2 * R) ⊆ (Set.univ : Set ℂ) := by simp
      exact divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ)) (B := 2 * R) this
    have := hfin.eventually_cofinite_notMem
    filter_upwards [this] with p hp
    have : ¬ ‖divisorZeroIndex₀Val p‖ ≤ 2 * R := by simpa using hp
    exact lt_of_not_ge this
  have hBound :
      ∀ᶠ p in Filter.cofinite, ‖a p‖ ≤ u p := by
    filter_upwards [h_big] with p hp
    have ha_pos : 0 < ‖divisorZeroIndex₀Val p‖ := lt_trans (by nlinarith [hRpos]) hp
    have hz_div : ‖z₀ / divisorZeroIndex₀Val p‖ ≤ (1 / 2 : ℝ) := by
      have h2R_pos : 0 < (2 * R : ℝ) := by nlinarith [hRpos]
      have hinv : ‖divisorZeroIndex₀Val p‖⁻¹ < (2 * R)⁻¹ := by
        simpa [one_div] using (one_div_lt_one_div_of_lt h2R_pos hp)
      have hmul_le : ‖z₀‖ * ‖divisorZeroIndex₀Val p‖⁻¹ ≤ R * ‖divisorZeroIndex₀Val p‖⁻¹ := by
        refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 (norm_nonneg _))
        exact hz0_le
      have hmul_lt : R * ‖divisorZeroIndex₀Val p‖⁻¹ < R * (2 * R)⁻¹ :=
        mul_lt_mul_of_pos_left hinv hRpos
      have hlt : ‖z₀‖ * ‖divisorZeroIndex₀Val p‖⁻¹ < R * (2 * R)⁻¹ :=
        lt_of_le_of_lt hmul_le hmul_lt
      have hRhalf : R * (2 * R)⁻¹ = (1 / 2 : ℝ) := by
        have hRne : (R : ℝ) ≠ 0 := hRpos.ne'
        have : R * (2 * R)⁻¹ = R / (2 * R) := by simp [div_eq_mul_inv]
        rw [this]
        field_simp [hRne]
      have hnorm : ‖z₀ / divisorZeroIndex₀Val p‖ = ‖z₀‖ * ‖divisorZeroIndex₀Val p‖⁻¹ := by
        simp [div_eq_mul_inv]
      have hzlt : ‖z₀ / divisorZeroIndex₀Val p‖ < (1 / 2 : ℝ) := by
        calc
          ‖z₀ / divisorZeroIndex₀Val p‖ = ‖z₀‖ * ‖divisorZeroIndex₀Val p‖⁻¹ := hnorm
          _ < R * (2 * R)⁻¹ := hlt
          _ = (1 / 2 : ℝ) := hRhalf
      exact le_of_lt hzlt
    have hE :
        ‖weierstrassFactor m (z₀ / divisorZeroIndex₀Val p) - 1‖ ≤
          4 * ‖z₀ / divisorZeroIndex₀Val p‖ ^ (m + 1) :=
      weierstrassFactor_sub_one_pow_bound (m := m) (z := z₀ / divisorZeroIndex₀Val p) hz_div
    have hz_pow :
        ‖z₀ / divisorZeroIndex₀Val p‖ ^ (m + 1) ≤
          (R ^ (m + 1)) * (‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1)) := by
      have : ‖z₀ / divisorZeroIndex₀Val p‖ = ‖z₀‖ * ‖divisorZeroIndex₀Val p‖⁻¹ := by
        simp [div_eq_mul_inv]
      rw [this]
      have : (‖z₀‖ * ‖divisorZeroIndex₀Val p‖⁻¹) ^ (m + 1) =
          ‖z₀‖ ^ (m + 1) * (‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1)) := by
        simp [mul_pow]
      rw [this]
      have hzle_pow : ‖z₀‖ ^ (m + 1) ≤ R ^ (m + 1) :=
        pow_le_pow_left₀ (norm_nonneg z₀) hz0_le (m + 1)
      gcongr
    have hp_ne : divisorZeroIndex₀Val p ≠ z₀ := by
      intro h
      have : ‖divisorZeroIndex₀Val p‖ ≤ R := by
        simp [h, R]                        
      exact (not_lt_of_ge this) (lt_trans (by nlinarith [hRpos]) hp)
    have ha : ‖a p‖ = ‖weierstrassFactor m (z₀ / divisorZeroIndex₀Val p) - 1‖ := by
      simp [a, Φ, hp_ne, sub_eq_add_neg]
    calc
      ‖a p‖ = ‖weierstrassFactor m (z₀ / divisorZeroIndex₀Val p) - 1‖ := ha
      _ ≤ 4 * ‖z₀ / divisorZeroIndex₀Val p‖ ^ (m + 1) := by
            simpa [sub_eq_add_neg, add_comm] using hE
      _ ≤ 4 * (R ^ (m + 1) * (‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1))) := by
            gcongr
      _ = u p := by
            simp [u, mul_assoc, mul_comm]
  have hsum_norm : Summable (fun p => ‖a p‖) := by
    refine (Summable.of_norm_bounded_eventually (E := ℝ) (f := fun p => ‖a p‖) (g := u) hu ?_)
    filter_upwards [hBound] with p hp
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (a p))] using hp
  have htprod_ne :
      (∏' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), (1 + a p)) ≠ 0 :=
    tprod_one_add_ne_zero_of_summable (R := ℂ) (f := a) (hf := fun p => by
      simpa [a, Φ, add_sub_cancel] using hΦ_ne p) hsum_norm
  have : (∏' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), (1 + a p)) =
      divisorComplementCanonicalProduct m f z₀ z₀ := by
    simp [a, Φ, divisorComplementCanonicalProduct, divisorComplementFactor_def]
  exact by
    intro h0
    exact htprod_ne (by simpa [this] using h0)

end Complex.Hadamard
end HadamardSourceScope12

section HadamardSourceScope13

open Filter _root_.Function _root_.Complex _root_.Erdos970.Complex Finset Topology
open scoped Topology BigOperators
open Set

namespace Complex.Hadamard

open _root_.Complex

theorem differentiableOn_divisorPartialProduct_div_pow_sub
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) (k : ℕ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) :
    DifferentiableOn ℂ (fun z : ℂ => (divisorPartialProduct m f s z) / (z - z₀) ^ k)
      ((Set.univ : Set ℂ) \ {z₀}) := by
  have hdiff_prod : DifferentiableOn ℂ (divisorPartialProduct m f s) (Set.univ : Set ℂ) := by
    exact (differentiable_divisorPartialProduct m f s).differentiableOn
  have hdiff_den : DifferentiableOn ℂ (fun z : ℂ => (z - z₀) ^ k) ((Set.univ : Set ℂ) \ {z₀}) := by
    have : Differentiable ℂ (fun z : ℂ => (z - z₀) ^ k) := by
      fun_prop
    exact this.differentiableOn
  by_cases hk : k = 0
  · subst hk
    simpa [pow_zero] using! (hdiff_prod.mono (by intro z hz; exact hz.1))
  · have hne : ∀ z ∈ ((Set.univ : Set ℂ) \ {z₀}), (fun z : ℂ => (z - z₀) ^ k) z ≠ 0 := by
      intro z hz
      have hz' : z ≠ z₀ := by
        simpa [Set.mem_sdiff, Set.mem_singleton_iff] using hz.2
      exact pow_ne_zero _ (sub_ne_zero.mpr hz')
    have hdiff_inv :
        DifferentiableOn ℂ (fun z : ℂ => ((z - z₀) ^ k)⁻¹) ((Set.univ : Set ℂ) \ {z₀}) :=
      hdiff_den.inv hne
    simpa [div_eq_mul_inv] using! (hdiff_prod.mono (by intro z hz; exact hz.1)).mul hdiff_inv

theorem differentiableOn_divisorCanonicalProduct_div_pow_sub
    (m : ℕ) (f : ℂ → ℂ) (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) (k : ℕ) : DifferentiableOn ℂ
      (fun z : ℂ => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k)
      ((Set.univ : Set ℂ) \ {z₀}) := by
  have hopen : IsOpen ((Set.univ : Set ℂ) \ {z₀}) := by
    have hset : ((Set.univ : Set ℂ) \ {z₀}) = ({z₀} : Set ℂ)ᶜ := by
      ext z; simp
    simp [hset]
  have hconv :=
    tendstoLocallyUniformlyOn_divisorPartialProduct_div_pow_sub
      (m := m) (f := f) h_sum (z₀ := z₀) (k := k)
  refine hconv.differentiableOn ?_ hopen
  refine Filter.Eventually.of_forall ?_
  intro s
  exact differentiableOn_divisorPartialProduct_div_pow_sub (m := m) (f := f) (z₀ := z₀) (k := k) s

theorem differentiableOn_update_limUnder_divisorCanonicalProduct_div_pow
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) : ∃ r > 0, DifferentiableOn ℂ (Function.update
          (fun z : ℂ => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
            (z - z₀) ^ (divisorZeroIndex₀FiberFinset (f := f) z₀).card) z₀
          (limUnder (𝓝[≠] z₀) (fun z : ℂ => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
                (z - z₀) ^ (divisorZeroIndex₀FiberFinset (f := f) z₀).card)))
        (Metric.ball z₀ r) := by
  rcases bddAbove_norm_divisorCanonicalProduct_div_pow_puncturedBall (m := m) (f := f)
      (h_sum := h_sum) (z₀ := z₀) with ⟨r, hrpos, hbdd⟩
  refine ⟨r, hrpos, ?_⟩
  have hnhds : Metric.ball z₀ r ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ hrpos
  have hdiff : DifferentiableOn ℂ (fun z : ℂ =>
        (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (divisorZeroIndex₀FiberFinset (f := f) z₀).card)
      ((Metric.ball z₀ r) \ {z₀}) := by
    have hglob :=
      differentiableOn_divisorCanonicalProduct_div_pow_sub
        (m := m) (f := f) h_sum (z₀ := z₀)
        (k := (divisorZeroIndex₀FiberFinset (f := f) z₀).card)
    refine hglob.mono ?_
    intro z hz
    exact ⟨by simp, hz.2⟩
  have hb : BddAbove (norm ∘ (fun z : ℂ => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
      (z - z₀) ^ (divisorZeroIndex₀FiberFinset (f := f) z₀).card) ''
    ((Metric.ball z₀ r) \ {z₀})) := hbdd
  simpa using
    (Complex.differentiableOn_update_limUnder_of_bddAbove (f := fun z : ℂ =>
        (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (divisorZeroIndex₀FiberFinset (f := f) z₀).card)
      (s := Metric.ball z₀ r) (c := z₀) hnhds hdiff hb)

theorem analyticAt_update_limUnder_divisorCanonicalProduct_div_pow
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) : AnalyticAt ℂ (Function.update (fun z : ℂ =>
          (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
        (z - z₀) ^ (divisorZeroIndex₀FiberFinset (f := f) z₀).card) z₀
        (limUnder (𝓝[≠] z₀) (fun z : ℂ => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
              (z - z₀) ^ (divisorZeroIndex₀FiberFinset (f := f) z₀).card)))
      z₀ := by
  rcases
      differentiableOn_update_limUnder_divisorCanonicalProduct_div_pow
        (m := m) (f := f) h_sum (z₀ := z₀) with ⟨r, hrpos, hdiff⟩
  let g : ℂ → ℂ :=
    Function.update
      (fun z : ℂ =>
        (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (divisorZeroIndex₀FiberFinset (f := f) z₀).card)
      z₀
      (limUnder (𝓝[≠] z₀) fun z : ℂ =>
        (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (divisorZeroIndex₀FiberFinset (f := f) z₀).card)
  have hcont : ContinuousAt g z₀ :=
    (hdiff.differentiableAt (Metric.ball_mem_nhds z₀ hrpos)).continuousAt
  have hd :
      ∀ᶠ z in 𝓝[≠] z₀, DifferentiableAt ℂ g z := by
    have hballWithin : Metric.ball z₀ r ∈ 𝓝[≠] z₀ := by
      refine mem_nhdsWithin_iff_exists_mem_nhds_inter.2 ?_
      refine ⟨Metric.ball z₀ r, Metric.ball_mem_nhds z₀ hrpos, ?_⟩
      intro z hz
      exact hz.1
    filter_upwards [hballWithin] with z hz
    exact (hdiff z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)
  simpa [g] using Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hd hcont

theorem exists_analyticAt_divisorCanonicalProduct_quotient
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) :
    ∃ q : ℂ → ℂ,
      AnalyticAt ℂ q z₀ ∧
        q z₀ =
          limUnder (𝓝[≠] z₀) (fun z : ℂ =>
            (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
              (z - z₀) ^ (divisorZeroIndex₀FiberFinset (f := f) z₀).card) ∧
        ∀ z : ℂ, z ≠ z₀ →
          q z =
            (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
              (z - z₀) ^ (divisorZeroIndex₀FiberFinset (f := f) z₀).card := by
  let q : ℂ → ℂ :=
    Function.update
      (fun z : ℂ =>
        (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (divisorZeroIndex₀FiberFinset (f := f) z₀).card)
      z₀
      (limUnder (𝓝[≠] z₀) fun z : ℂ =>
        (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (divisorZeroIndex₀FiberFinset (f := f) z₀).card)
  refine ⟨q, ?_, ?_, ?_⟩
  · simpa [q] using
      analyticAt_update_limUnder_divisorCanonicalProduct_div_pow
        (m := m) (f := f) (h_sum := h_sum) (z₀ := z₀)
  · simp [q]
  · intro z hz
    simp [q, Function.update_of_ne hz]

theorem analyticOrderNatAt_divisorCanonicalProduct_eq_fiber_card
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) :
    analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z₀ =
      (divisorZeroIndex₀FiberFinset (f := f) z₀).card := by
  set k : ℕ := (divisorZeroIndex₀FiberFinset (f := f) z₀).card
  let F : ℂ → ℂ := divisorCanonicalProduct m f (Set.univ : Set ℂ)
  let q0 : ℂ → ℂ := fun z => F z / (z - z₀) ^ k
  rcases exists_analyticAt_divisorCanonicalProduct_quotient
      (m := m) (f := f) (h_sum := h_sum) (z₀ := z₀) with
    ⟨q, hqA, hq_self, hq_ne⟩
  have hdiff_univ : DifferentiableOn ℂ F (Set.univ : Set ℂ) :=
    differentiableOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
  have han : AnalyticAt ℂ F z₀ := by
    refine (Complex.analyticAt_iff_eventually_differentiableAt).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro z
    have : DifferentiableWithinAt ℂ F (Set.univ : Set ℂ) z := hdiff_univ z (by simp)
    exact this.differentiableAt (by simp)
  rcases
      exists_ball_eq_divisorCanonicalProduct_div_pow_eq (m := m) (f := f) (h_sum := h_sum)
      (z₀ := z₀)
    with ⟨ε, hε, u, huA, hu0, hEq⟩
  let g : ℂ → ℂ := fun z => (divisorComplementCanonicalProduct m f z₀ z) * u z
  have hcompDiff : DifferentiableOn ℂ (divisorComplementCanonicalProduct m f z₀)
      (Set.univ : Set ℂ) :=
    differentiableOn_divisorComplementCanonicalProduct_univ (m := m) (f := f) (z₀ := z₀) h_sum
  have hcompCont : ContinuousAt (divisorComplementCanonicalProduct m f z₀) z₀ :=
    (hcompDiff z₀ (by simp)).differentiableAt (by simp) |>.continuousAt
  have hgCont : ContinuousAt g z₀ := (hcompCont.mul huA.continuousAt)
  have hg0 : g z₀ ≠ 0 := by
    have hcomp0 : divisorComplementCanonicalProduct m f z₀ z₀ ≠ 0 :=
      divisorComplementCanonicalProduct_ne_zero_at (m := m) (f := f) (z₀ := z₀) h_sum
    exact mul_ne_zero hcomp0 hu0
  have hne_mem : ∀ᶠ z in 𝓝[≠] z₀, z ∈ (({z₀} : Set ℂ)ᶜ) :=
    Filter.eventually_of_mem
      (self_mem_nhdsWithin : (({z₀} : Set ℂ)ᶜ) ∈ 𝓝[≠] z₀) (fun _ hz => hz)
  have hne : ∀ᶠ z in 𝓝[≠] z₀, z ≠ z₀ := by
    filter_upwards [hne_mem] with z hz
    simpa [Set.mem_compl_singleton_iff] using hz
  have ht_q0 : Tendsto q0 (𝓝[≠] z₀) (𝓝 (g z₀)) := by
    have hball : ∀ᶠ z in 𝓝[≠] z₀, z ∈ Metric.ball z₀ ε :=
      Filter.eventually_of_mem
        (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z₀ hε)) (fun _ hz => hz)
    have heq : q0 =ᶠ[𝓝[≠] z₀] g := by
      filter_upwards [hball, hne] with z hz hzne
      have hq := hEq z hz hzne
      simpa [q0, F, k, g, smul_eq_mul] using hq
    exact (hgCont.continuousWithinAt.tendsto.congr' heq.symm)
  have hlim : limUnder (𝓝[≠] z₀) q0 = g z₀ := ht_q0.limUnder_eq
  have hq0 : q z₀ ≠ 0 := by
    have hq_self' : q z₀ = limUnder (𝓝[≠] z₀) q0 := by
      simpa [q0, F, k] using hq_self
    have : q z₀ = g z₀ := hq_self'.trans hlim
    exact this.symm ▸ hg0
  have heq_punct : (fun z : ℂ => F z) =ᶠ[𝓝[≠] z₀] fun z : ℂ => (z - z₀) ^ k • q z := by
    filter_upwards [hne] with z hz
    have hzpow : (z - z₀) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hz)
    have hq : q z = q0 z := by simpa [q0, F, k] using hq_ne z hz
    have hmul : (z - z₀) ^ k * q0 z = F z := by
      calc
        (z - z₀) ^ k * q0 z
            = (((z - z₀) ^ k) * F z) / ((z - z₀) ^ k) := by
                simp [q0, div_eq_mul_inv, mul_assoc]
        _ = F z := by
              simpa [mul_assoc] using (mul_div_cancel_left₀ (F z) hzpow)
    have : F z = (z - z₀) ^ k * q z := by
      calc
        F z = (z - z₀) ^ k * q0 z := hmul.symm
        _ = (z - z₀) ^ k * q z := by simp [hq]
    simpa [smul_eq_mul] using this
  have hcontF : ContinuousAt F z₀ :=
    (hdiff_univ z₀ (by simp)).differentiableAt (by simp) |>.continuousAt
  have hcontq : ContinuousAt q z₀ := hqA.continuousAt
  have h_at_z0 : F z₀ = (z₀ - z₀) ^ k • q z₀ := by
    have ht1 : Tendsto F (𝓝[≠] z₀) (𝓝 (F z₀)) := hcontF.continuousWithinAt.tendsto
    have hpow :
        Tendsto (fun z : ℂ => (z - z₀) ^ k) (𝓝[≠] z₀) (𝓝 ((z₀ - z₀) ^ k)) :=
      ((continuousAt_id.sub continuousAt_const).pow k).continuousWithinAt.tendsto
    have ht2 :
        Tendsto (fun z : ℂ => (z - z₀) ^ k • q z) (𝓝[≠] z₀)
          (𝓝 ((z₀ - z₀) ^ k • q z₀)) :=
      hpow.mul (hcontq.continuousWithinAt.tendsto)
    have ht2' : Tendsto F (𝓝[≠] z₀) (𝓝 ((z₀ - z₀) ^ k • q z₀)) :=
      ht2.congr' heq_punct.symm
    exact tendsto_nhds_unique ht1 ht2'
  have hfac : ∀ᶠ z in 𝓝 z₀, F z = (z - z₀) ^ k • q z := by
    have hball1 : Metric.ball z₀ 1 ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ (by norm_num)
    have hball1' : ∀ᶠ z in 𝓝 z₀, z ∈ Metric.ball z₀ 1 :=
      Filter.eventually_of_mem hball1 (fun _ hz => hz)
    filter_upwards [hball1'] with z _hz
    by_cases hz0 : z = z₀
    · subst hz0
      simpa using h_at_z0
    · have hzpow : (z - z₀) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hz0)
      have hq : q z = q0 z := by simpa [q0, F, k] using hq_ne z hz0
      have hmul : (z - z₀) ^ k * q0 z = F z := by
        calc
          (z - z₀) ^ k * q0 z
              = (((z - z₀) ^ k) * F z) / ((z - z₀) ^ k) := by
                  simp [q0, div_eq_mul_inv, mul_assoc]
          _ = F z := by
                simpa [mul_assoc] using (mul_div_cancel_left₀ (F z) hzpow)
      have : F z = (z - z₀) ^ k * q z := by
        calc
          F z = (z - z₀) ^ k * q0 z := hmul.symm
          _ = (z - z₀) ^ k * q z := by simp [hq]
      simpa [smul_eq_mul] using this
  have hk' : analyticOrderAt F z₀ = k :=
    (han.analyticOrderAt_eq_natCast (n := k)).2 ⟨q, hqA, hq0, hfac⟩
  have hkNat : analyticOrderNatAt F z₀ = k := by
    simp [analyticOrderNatAt, hk']
  simpa [F, k] using hkNat

theorem analyticOrderNatAt_divisorCanonicalProduct_eq_analyticOrderNatAt
    (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1)))
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z₀ =
      analyticOrderNatAt f z₀ := by
  have hcp :
      analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z₀ =
        (divisorZeroIndex₀FiberFinset (f := f) z₀).card :=
    analyticOrderNatAt_divisorCanonicalProduct_eq_fiber_card (m := m) (f := f) (h_sum := h_sum)
      (z₀ := z₀)
  have hfib :
      (divisorZeroIndex₀FiberFinset (f := f) z₀).card = analyticOrderNatAt f z₀ :=
    divisorZeroIndex₀FiberFinset_card_eq_analyticOrderNatAt (hf := hf) (z₀ := z₀) hz₀
  simpa [hfib] using hcp

end Complex.Hadamard
end HadamardSourceScope13

section HadamardSourceScope14

namespace Complex.Hadamard

open _root_.Complex

open scoped Topology
open Set

lemma analyticOrderAt_ne_top_of_exists_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnot : ∃ z : ℂ, f z ≠ 0) :
    ∀ z : ℂ, analyticOrderAt f z ≠ ⊤ := by
  rcases hnot with ⟨z1, hz1⟩
  have hf_an : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) := by
    intro z hz
    exact (Differentiable.analyticAt (f := f) hf z)
  have hz1_not_top : analyticOrderAt f z1 ≠ ⊤ := by
    have : analyticOrderAt f z1 = 0 :=
      (hf.analyticAt z1).analyticOrderAt_eq_zero.2 hz1
    simp [this]
  intro z
  exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected (hf := hf_an)
    (U := (Set.univ : Set ℂ)) (x := z1) (y := z) (by simpa using isPreconnected_univ)
    (by simp) (by simp) hz1_not_top

lemma no_zero_on_sphere_of_forall_val_norm_ne
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    {B r : ℝ} (hrpos : 0 < r) (hBr : r ≤ B) (hr_not : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
      ‖divisorZeroIndex₀Val p‖ ≤ B → r ≠ ‖divisorZeroIndex₀Val p‖) :
    ∀ u : ℂ, ‖u‖ = r → f u ≠ 0 := by
  intro u hur
  have hu0 : u ≠ 0 := by
    intro hu0
    subst hu0
    have : (0 : ℝ) = r := by simpa using hur
    exact (ne_of_gt hrpos) this.symm
  intro hfu0
  have hnotTop : analyticOrderAt f u ≠ ⊤ :=
    analyticOrderAt_ne_top_of_exists_ne_zero (f := f) hf hnot u
  have hord_ne0 : analyticOrderNatAt f u ≠ 0 := by
    intro h0
    have hEN : (analyticOrderNatAt f u : ENat) = 0 := by simp [h0]
    have hAt0 : analyticOrderAt f u = 0 := by
      have hcast : (analyticOrderNatAt f u : ENat) = analyticOrderAt f u :=
        Nat.cast_analyticOrderNatAt (f := f) (z₀ := u) hnotTop
      simpa [hcast] using hEN
    have han : AnalyticAt ℂ f u := Differentiable.analyticAt (f := f) hf u
    exact ((han.analyticOrderAt_eq_zero).1 hAt0) hfu0
  have hcard_pos : 0 < (divisorZeroIndex₀FiberFinset (f := f) u).card := by
    have hcard :=
      divisorZeroIndex₀FiberFinset_card_eq_analyticOrderNatAt (hf := hf) (z₀ := u) hu0
    have : 0 < analyticOrderNatAt f u := Nat.pos_of_ne_zero hord_ne0
    simpa [hcard] using this
  rcases Finset.card_pos.mp hcard_pos with ⟨p, hp⟩
  have hpval : divisorZeroIndex₀Val p = u :=
    (mem_divisorZeroIndex₀FiberFinset (f := f) (z₀ := u) p).1 hp
  have hpB : ‖divisorZeroIndex₀Val p‖ ≤ B := by
    have : ‖divisorZeroIndex₀Val p‖ = r := by simp [hpval, hur]
    simpa [this] using hBr
  have : r ≠ ‖divisorZeroIndex₀Val p‖ := hr_not p hpB
  exact this (by simp [hpval, hur])

theorem analyticOrderAt_divisorCanonicalProduct_eq_fiber_card
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) :
    analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z₀ =
      ((divisorZeroIndex₀FiberFinset (f := f) z₀).card : ℕ∞) := by
  let F : ℂ → ℂ := divisorCanonicalProduct m f (Set.univ : Set ℂ)
  have hNat :
      analyticOrderNatAt F z₀ = (divisorZeroIndex₀FiberFinset (f := f) z₀).card := by
    simpa [F] using
      (analyticOrderNatAt_divisorCanonicalProduct_eq_fiber_card
        (m := m) (f := f) (h_sum := h_sum) (z₀ := z₀))
  have hdiffOn : DifferentiableOn ℂ F (Set.univ : Set ℂ) := by
    simpa [F] using differentiableOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
  have hdiff : Differentiable ℂ F := by
    intro z
    exact (hdiffOn z (by simp)).differentiableAt (by simp)
  have hnotTop : analyticOrderAt F z₀ ≠ ⊤ :=
    analyticOrderAt_ne_top_of_exists_ne_zero (hf := hdiff)
      ⟨0, by simp [F, divisorCanonicalProduct_zero]⟩ z₀
  have hcast : (analyticOrderNatAt F z₀ : ℕ∞) = analyticOrderAt F z₀ :=
    Nat.cast_analyticOrderNatAt (f := F) (z₀ := z₀) hnotTop
  have hNatCast :
      (analyticOrderNatAt F z₀ : ℕ∞) =
        ((divisorZeroIndex₀FiberFinset (f := f) z₀).card : ℕ∞) := by
    simp [hNat]
  simpa [F, hcast] using hNatCast

theorem divisorCanonicalProduct_ne_zero_of_forall_ne
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1)))
    {z : ℂ} (hz : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), z ≠ divisorZeroIndex₀Val p) :
    divisorCanonicalProduct m f (Set.univ : Set ℂ) z ≠ 0 := by
  let F : ℂ → ℂ := divisorCanonicalProduct m f (Set.univ : Set ℂ)
  have hfiber_empty : divisorZeroIndex₀FiberFinset (f := f) z = ∅ := by
    ext p
    constructor
    · intro hp
      exact False.elim (hz p ((mem_divisorZeroIndex₀FiberFinset (f := f) (z₀ := z) p).1 hp).symm)
    · intro hp
      simp at hp
  have horder :
      analyticOrderAt F z = (0 : ℕ∞) := by
    have h :=
      analyticOrderAt_divisorCanonicalProduct_eq_fiber_card
        (m := m) (f := f) (h_sum := h_sum) (z₀ := z)
    simpa [F, hfiber_empty] using h
  have han : AnalyticAt ℂ F z := by
    refine (Complex.analyticAt_iff_eventually_differentiableAt).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro w
    exact (((differentiableOn_divisorCanonicalProduct_univ m f h_sum) w
      (by simp)).differentiableAt (by simp))
  exact (han.analyticOrderAt_eq_zero).1 horder

theorem logDeriv_divisorCanonicalProduct_one_eq_tsum_of_forall_ne
    {f : ℂ → ℂ} {z : ℂ}
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (2 : ℕ)))
    (hz : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), z ≠ divisorZeroIndex₀Val p) :
    logDeriv (divisorCanonicalProduct 1 f (Set.univ : Set ℂ)) z =
      ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
        (1 / (z - divisorZeroIndex₀Val p) + 1 / divisorZeroIndex₀Val p) :=
  logDeriv_divisorCanonicalProduct_one_eq_tsum h_sum hz
    (divisorCanonicalProduct_ne_zero_of_forall_ne 1 f h_sum hz)

end Hadamard
end Complex
end HadamardSourceScope14

section HadamardSourceScope16

namespace Complex.Hadamard

open _root_.Complex

open Filter Topology Set _root_.Complex _root_.Erdos970.Complex

open scoped BigOperators Topology

noncomputable def hadamardDenom (m : ℕ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  z ^ (analyticOrderNatAt f 0) * divisorCanonicalProduct m f (Set.univ : Set ℂ) z

theorem differentiable_divisorCanonicalProduct_univ (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1))) :
    Differentiable ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) := by
  intro z
  have hdiffOn :
      DifferentiableOn ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) (Set.univ : Set ℂ) :=
    differentiableOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
  exact (hdiffOn z (by simp)).differentiableAt (by simp)

theorem analyticAt_divisorCanonicalProduct_univ (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1))) (z : ℂ) :
    AnalyticAt ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z :=
  (differentiable_divisorCanonicalProduct_univ m f h_sum).analyticAt z

theorem differentiable_hadamardDenom (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1))) :
    Differentiable ℂ (hadamardDenom m f) := by
  have hcprod : Differentiable ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) := by
    exact differentiable_divisorCanonicalProduct_univ m f h_sum
  simpa [hadamardDenom] using! (differentiable_id.pow (analyticOrderNatAt f 0)).mul hcprod

theorem hadamardDenom_ne_zero_at {m : ℕ} {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnot : ∃ z : ℂ, f z ≠ 0) (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1))) {z : ℂ} (hz : f z ≠ 0) : hadamardDenom m f z ≠ 0 := by
  have hf_not_top : ∀ w : ℂ, analyticOrderAt f w ≠ ⊤ :=
    analyticOrderAt_ne_top_of_exists_ne_zero (hf := hf) hnot
  have han_f : AnalyticAt ℂ f z := hf.analyticAt z
  have horder_f : analyticOrderNatAt f z = 0 := by
    have : analyticOrderAt f z = 0 := (han_f.analyticOrderAt_eq_zero).2 hz
    have hcast : (analyticOrderNatAt f z : ℕ∞) = analyticOrderAt f z :=
      Nat.cast_analyticOrderNatAt (f := f) (z₀ := z) (hf_not_top z)
    have : (analyticOrderNatAt f z : ℕ∞) = 0 := by simp [hcast, this]
    exact_mod_cast this
  have han_cprod : AnalyticAt ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z := by
    exact analyticAt_divisorCanonicalProduct_univ m f h_sum z
  by_cases hz0 : z = 0
  · subst hz0
    have hord0 : analyticOrderNatAt f 0 = 0 := by simpa using horder_f
    simp [hadamardDenom, hord0, divisorCanonicalProduct_zero]
  · have hp : z ^ (analyticOrderNatAt f 0) ≠ 0 := pow_ne_zero _ hz0
    have hcprod_order :
        analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z = 0 := by
      simpa [horder_f] using
        (analyticOrderNatAt_divisorCanonicalProduct_eq_analyticOrderNatAt (m := m) (hf := hf)
          (h_sum := h_sum) (z₀ := z) hz0)
    have hcprod_ne : divisorCanonicalProduct m f (Set.univ : Set ℂ) z ≠ 0 := by
      have hcprod_entire :
          Differentiable ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) := by
        exact differentiable_divisorCanonicalProduct_univ m f h_sum
      have hcprod_not_top :
          analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z ≠ ⊤ :=
        analyticOrderAt_ne_top_of_exists_ne_zero (hf := hcprod_entire)
          ⟨0, by simp [divisorCanonicalProduct_zero]⟩ z
      have hcprod_cast :
          (analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z : ℕ∞) =
            analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z :=
        Nat.cast_analyticOrderNatAt
          (f := divisorCanonicalProduct m f (Set.univ : Set ℂ)) (z₀ := z) hcprod_not_top
      have : analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z = 0 := by
        have :
            (analyticOrderNatAt
              (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z : ℕ∞) = 0 := by
          exact_mod_cast hcprod_order
        simp [hcprod_cast] at this
        simpa using this
      exact (han_cprod.analyticOrderAt_eq_zero).1 this
    exact mul_ne_zero hp hcprod_ne

lemma analyticOrderNatAt_divisorCanonicalProduct_zero
    (m : ℕ) (f : ℂ → ℂ) (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1))) :
    analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 = 0 := by
  have hcprod_entire :
      Differentiable ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) := by
    exact differentiable_divisorCanonicalProduct_univ m f h_sum
  have hcprod_not_top :
      analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 ≠ ⊤ :=
    analyticOrderAt_ne_top_of_exists_ne_zero (hf := hcprod_entire)
      ⟨0, by simp [divisorCanonicalProduct_zero]⟩ 0
  have hcprodA : AnalyticAt ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 :=
    hcprod_entire.analyticAt 0
  have hcprod0 : divisorCanonicalProduct m f (Set.univ : Set ℂ) 0 ≠ 0 := by
    simp [divisorCanonicalProduct_zero]
  have : analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 = 0 :=
    (hcprodA.analyticOrderAt_eq_zero).2 hcprod0
  have hcast :
      (analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 : ℕ∞) =
        analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 :=
    Nat.cast_analyticOrderNatAt
      (f := divisorCanonicalProduct m f (Set.univ : Set ℂ)) (z₀ := (0 : ℂ)) hcprod_not_top
  have :
      (analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 : ℕ∞) =
        0 := by
    simp [hcast, this]
  exact_mod_cast this

theorem analyticOrderNatAt_hadamardDenom_eq
    (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1))) (z : ℂ) :
    analyticOrderNatAt (hadamardDenom m f) z = analyticOrderNatAt f z := by
  by_cases hz0 : z = 0
  · subst hz0
    have hpowA : AnalyticAt ℂ (fun z : ℂ => z ^ analyticOrderNatAt f 0) 0 := by
      simpa using! (analyticAt_id.pow (analyticOrderNatAt f 0))
    have hpow_not_top :
        analyticOrderAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) 0 ≠ ⊤ :=
      analyticOrderAt_ne_top_of_exists_ne_zero
        (hf := (differentiable_id.pow (analyticOrderNatAt f 0)))
        ⟨1, by simp⟩ 0
    have hcprodA : AnalyticAt ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 := by
      exact analyticAt_divisorCanonicalProduct_univ m f h_sum 0
    have hcprod0 :
        analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 = 0 :=
      analyticOrderNatAt_divisorCanonicalProduct_zero (m := m) (f := f) h_sum
    have hid0 : analyticOrderNatAt (fun z : ℂ => z) 0 = 1 := by
      have hid_entire : Differentiable ℂ (fun z : ℂ => z) := differentiable_id
      have hdiv :
          (MeromorphicOn.divisor (fun z : ℂ => z) (Set.univ : Set ℂ)) 0 =
            (analyticOrderNatAt (fun z : ℂ => z) 0 : ℤ) := by
        simpa using
          (divisor_univ_eq_analyticOrderNatAt_int
            (f := fun z : ℂ => z) hid_entire 0)
      have hdiv1 : (MeromorphicOn.divisor (fun z : ℂ => z) (Set.univ : Set ℂ)) 0 = 1 := by
        simpa using
          (MeromorphicOn.divisor_sub_const_self (z₀ := (0 : ℂ))
            (U := (Set.univ : Set ℂ)) (by simp))
      have : (analyticOrderNatAt (fun z : ℂ => z) 0 : ℤ) = 1 := by
        simpa [hdiv] using hdiv1
      exact_mod_cast this
    have hpow0 :
        analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) 0 =
          analyticOrderNatAt f 0 := by
      have hidA : AnalyticAt ℂ (fun z : ℂ => z) 0 := by
        simpa [id] using! (analyticAt_id : AnalyticAt ℂ (id : ℂ → ℂ) 0)
      simpa [hid0] using! (analyticOrderNatAt_pow (hf := hidA) (n := analyticOrderNatAt f 0))
    have hmul :
        analyticOrderNatAt (hadamardDenom m f) 0 =
          analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) 0 +
            analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 := by
      have hcprod_not_top' :
          analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 ≠ ⊤ :=
        analyticOrderAt_ne_top_of_exists_ne_zero
          (hf := differentiable_divisorCanonicalProduct_univ m f h_sum)
          ⟨0, by simp [divisorCanonicalProduct_zero]⟩ 0
      simpa [hadamardDenom] using!
        analyticOrderNatAt_mul (hf := hpowA) (hg := hcprodA)
          (hf' := hpow_not_top) (hg' := hcprod_not_top')
    simp [hmul, hpow0, hcprod0]
  · have hpowA : AnalyticAt ℂ (fun z : ℂ => z ^ analyticOrderNatAt f 0) z := by
      simpa using! (analyticAt_id.pow (analyticOrderNatAt f 0))
    have hpow_not_top :
        analyticOrderAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z ≠ ⊤ :=
      analyticOrderAt_ne_top_of_exists_ne_zero
        (hf := (differentiable_id.pow (analyticOrderNatAt f 0)))
        ⟨1, by simp⟩ z
    have hpow0 : analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z = 0 := by
      have hz' : (fun z : ℂ => z ^ analyticOrderNatAt f 0) z ≠ 0 := by
        simp [hz0]
      have : analyticOrderAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z = 0 :=
        ((hpowA).analyticOrderAt_eq_zero).2 hz'
      have hcast : (analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z : ℕ∞) =
          analyticOrderAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z :=
        Nat.cast_analyticOrderNatAt
          (f := fun z : ℂ => z ^ analyticOrderNatAt f 0) (z₀ := z) hpow_not_top
      have : (analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z : ℕ∞) = 0 := by
        simp [hcast, this]
      exact_mod_cast this
    have hcprod_eq :
        analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z =
          analyticOrderNatAt f z :=
      analyticOrderNatAt_divisorCanonicalProduct_eq_analyticOrderNatAt
        (m := m) (hf := hf) (h_sum := h_sum) (z₀ := z) hz0
    have hcprodA : AnalyticAt ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z := by
      exact analyticAt_divisorCanonicalProduct_univ m f h_sum z
    have hcprod_not_top :
        analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z ≠ ⊤ :=
      analyticOrderAt_ne_top_of_exists_ne_zero
        (hf := differentiable_divisorCanonicalProduct_univ m f h_sum)
        ⟨0, by simp [divisorCanonicalProduct_zero]⟩ z
    have hmul :
        analyticOrderNatAt (hadamardDenom m f) z =
          analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z +
            analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z := by
      simpa [hadamardDenom] using!
        analyticOrderNatAt_mul (hf := hpowA) (hg := hcprodA)
          (hf' := hpow_not_top) (hg' := hcprod_not_top)
    simp [hmul, hpow0, hcprod_eq]

theorem divisor_hadamardDenom_eq
    (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1))) :
    MeromorphicOn.divisor (hadamardDenom m f) (Set.univ : Set ℂ) =
      MeromorphicOn.divisor f (Set.univ : Set ℂ) := by
  ext z
  have hden_entire : Differentiable ℂ (hadamardDenom m f) :=
    differentiable_hadamardDenom (m := m) f h_sum
  have hf_entire : Differentiable ℂ f := hf
  have hden :
      (MeromorphicOn.divisor (hadamardDenom m f) (Set.univ : Set ℂ)) z =
        (analyticOrderNatAt (hadamardDenom m f) z : ℤ) := by
    simpa using (divisor_univ_eq_analyticOrderNatAt_int (f := hadamardDenom m f) hden_entire z)
  have hfz :
      (MeromorphicOn.divisor f (Set.univ : Set ℂ)) z =
        (analyticOrderNatAt f z : ℤ) := by
    simpa using (divisor_univ_eq_analyticOrderNatAt_int (f := f) hf_entire z)
  simp [hden, hfz, analyticOrderNatAt_hadamardDenom_eq (m := m) (hf := hf) (h_sum := h_sum) z]

theorem divisor_hadamardQuotient_eq_zero
    (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1))) :
    MeromorphicOn.divisor (fun z : ℂ => f z / hadamardDenom m f z) (Set.univ : Set ℂ) = 0 := by
  have hf_mero : MeromorphicOn f (Set.univ : Set ℂ) := by
    intro z hz
    exact (hf.analyticAt z).meromorphicAt
  have hden_entire : Differentiable ℂ (hadamardDenom m f) :=
    differentiable_hadamardDenom (m := m) f h_sum
  have hden_mero : MeromorphicOn (hadamardDenom m f) (Set.univ : Set ℂ) := by
    intro z hz
    exact (hden_entire.analyticAt z).meromorphicAt
  rcases hnot with ⟨z1, hz1⟩
  have hden1 : hadamardDenom m f z1 ≠ 0 :=
    hadamardDenom_ne_zero_at (m := m) (f := f) hf ⟨z1, hz1⟩ h_sum hz1
  have hf_order_ne_top : ∀ z ∈ (Set.univ : Set ℂ), meromorphicOrderAt f z ≠ ⊤ := by
    intro z hzU
    have hz1_ne_top : meromorphicOrderAt f z1 ≠ ⊤ := by
      have hfAt : MeromorphicAt f z1 := hf_mero z1 (by simp)
      have hcont : ContinuousAt f z1 := (hf.differentiableAt).continuousAt
      have hne_nhds : ∀ᶠ w in 𝓝 z1, f w ≠ 0 :=
        (hcont.ne_iff_eventually_ne continuousAt_const).1 hz1
      have hne_nhdsNE : ∀ᶠ w in 𝓝[≠] z1, f w ≠ 0 :=
        eventually_nhdsWithin_of_eventually_nhds hne_nhds
      exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf := hfAt)).2 hne_nhdsNE
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected (hf := hf_mero)
      (x := z1) (hU := isPreconnected_univ) (h₁x := by simp) (hy := by simp) hz1_ne_top
  have hden_order_ne_top :
      ∀ z ∈ (Set.univ : Set ℂ), meromorphicOrderAt (hadamardDenom m f) z ≠ ⊤ := by
    intro z hzU
    have hz1_ne_top : meromorphicOrderAt (hadamardDenom m f) z1 ≠ ⊤ := by
      have hdenAt : MeromorphicAt (hadamardDenom m f) z1 := hden_mero z1 (by simp)
      have hcont : ContinuousAt (hadamardDenom m f) z1 :=
        (hden_entire.differentiableAt).continuousAt
      have hne_nhds : ∀ᶠ w in 𝓝 z1, hadamardDenom m f w ≠ 0 :=
        (hcont.ne_iff_eventually_ne continuousAt_const).1 hden1
      have hne_nhdsNE : ∀ᶠ w in 𝓝[≠] z1, hadamardDenom m f w ≠ 0 :=
        eventually_nhdsWithin_of_eventually_nhds hne_nhds
      exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf := hdenAt)).2 hne_nhdsNE
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected (hf := hden_mero)
      (x := z1) (hU := isPreconnected_univ) (h₁x := by simp) (hy := by simp) hz1_ne_top
  have hinv_order_ne_top :
      ∀ z ∈ (Set.univ : Set ℂ),
        meromorphicOrderAt (fun z : ℂ => (hadamardDenom m f z)⁻¹) z ≠ ⊤ := by
    intro z hzU
    have hinv_mero :
        MeromorphicOn (fun z : ℂ => (hadamardDenom m f z)⁻¹) (Set.univ : Set ℂ) :=
      hden_mero.inv
    have hz1_ne_top :
        meromorphicOrderAt (fun z : ℂ => (hadamardDenom m f z)⁻¹) z1 ≠ ⊤ := by
      have hinvAt : MeromorphicAt (fun z : ℂ => (hadamardDenom m f z)⁻¹) z1 :=
        hinv_mero z1 (by simp)
      have hcont_denom : ContinuousAt (hadamardDenom m f) z1 :=
        (hden_entire.differentiableAt).continuousAt
      have hcont : ContinuousAt (fun z : ℂ => (hadamardDenom m f z)⁻¹) z1 :=
        hcont_denom.inv₀ hden1
      have hinv1 : (fun z : ℂ => (hadamardDenom m f z)⁻¹) z1 ≠ 0 := by
        simpa using inv_ne_zero hden1
      have hne_nhds :
          ∀ᶠ w in 𝓝 z1, (fun z : ℂ => (hadamardDenom m f z)⁻¹) w ≠ 0 :=
        (hcont.ne_iff_eventually_ne continuousAt_const).1 hinv1
      have hne_nhdsNE :
          ∀ᶠ w in 𝓝[≠] z1, (fun z : ℂ => (hadamardDenom m f z)⁻¹) w ≠ 0 :=
        eventually_nhdsWithin_of_eventually_nhds hne_nhds
      exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf := hinvAt)).2 hne_nhdsNE
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected (hf := hinv_mero)
      (x := z1) (hU := isPreconnected_univ) (h₁x := by simp) (hy := by simp) hz1_ne_top
  have hdiv_denom : MeromorphicOn.divisor (hadamardDenom m f) (Set.univ : Set ℂ) =
      MeromorphicOn.divisor f (Set.univ : Set ℂ) :=
    divisor_hadamardDenom_eq (m := m) (hf := hf) (h_sum := h_sum)
  calc
    MeromorphicOn.divisor (fun z : ℂ => f z / hadamardDenom m f z) (Set.univ : Set ℂ)
        = MeromorphicOn.divisor
            (fun z : ℂ => f z * (hadamardDenom m f z)⁻¹) (Set.univ : Set ℂ) := by
            simp [div_eq_mul_inv]
    _ = MeromorphicOn.divisor f (Set.univ : Set ℂ) +
          MeromorphicOn.divisor (fun z : ℂ => (hadamardDenom m f z)⁻¹) (Set.univ : Set ℂ) := by
          simpa using (MeromorphicOn.divisor_fun_mul (U := (Set.univ : Set ℂ))
            (f₁ := f) (f₂ := fun z => (hadamardDenom m f z)⁻¹) hf_mero (hden_mero.inv)
            hf_order_ne_top hinv_order_ne_top)
    _ = MeromorphicOn.divisor f (Set.univ : Set ℂ) -
          MeromorphicOn.divisor (hadamardDenom m f) (Set.univ : Set ℂ) := by
          simp [sub_eq_add_neg]
    _ = 0 := by
          simp [hdiv_denom]

theorem exists_entire_nonzero_hadamardQuotient
    (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1))) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ (∀ z, H z ≠ 0) ∧ ∀ z : ℂ, f z =
      H z * z ^ (analyticOrderNatAt f 0) * divisorCanonicalProduct m f (Set.univ : Set ℂ) z := by
  let denom : ℂ → ℂ := hadamardDenom m f
  let q : ℂ → ℂ := fun z => f z / denom z
  have hden_entire : Differentiable ℂ denom :=
    differentiable_hadamardDenom (m := m) f h_sum
  have hq_mero : MeromorphicOn q (Set.univ : Set ℂ) := by
    intro z hzU
    have hf_m : MeromorphicAt f z := (hf.analyticAt z).meromorphicAt
    have hden_m : MeromorphicAt denom z := (hden_entire.analyticAt z).meromorphicAt
    simpa [q, denom, div_eq_mul_inv] using! (hf_m.mul hden_m.inv)
  let H : ℂ → ℂ := toMeromorphicNFOn q (Set.univ : Set ℂ)
  have hNF : MeromorphicNFOn H (Set.univ : Set ℂ) :=
    meromorphicNFOn_toMeromorphicNFOn q (Set.univ : Set ℂ)
  have hdivH : MeromorphicOn.divisor H (Set.univ : Set ℂ) = 0 := by
    have hdivq : MeromorphicOn.divisor q (Set.univ : Set ℂ) = 0 :=
      divisor_hadamardQuotient_eq_zero (m := m) (f := f) (hf := hf)
        (hnot := hnot) (h_sum := h_sum)
    simpa [H, hdivq] using
      (MeromorphicOn.divisor_of_toMeromorphicNFOn
        (f := q) (U := (Set.univ : Set ℂ)) hq_mero)
  have hA : AnalyticOnNhd ℂ H (Set.univ : Set ℂ) := by
    have :
        (0 : Function.locallyFinsuppWithin (Set.univ : Set ℂ) ℤ) ≤
          MeromorphicOn.divisor H (Set.univ : Set ℂ) := by
      simp [hdivH]
    exact (MeromorphicNFOn.divisor_nonneg_iff_analyticOnNhd (h₁f := hNF)).1 (by simp [hdivH])
  have hH_entire : Differentiable ℂ H := by
    intro z
    exact (hA z (by simp)).differentiableAt
  rcases hnot with ⟨z1, hz1⟩
  have hden1 : denom z1 ≠ 0 :=
    hadamardDenom_ne_zero_at (m := m) (f := f) hf ⟨z1, hz1⟩ h_sum hz1
  have hqA1 : AnalyticAt ℂ q z1 := by
    have hdenA1 : AnalyticAt ℂ denom z1 := hden_entire.analyticAt z1
    exact (hf.analyticAt z1).div hdenA1 hden1
  have hqNF1 : MeromorphicNFAt q z1 := hqA1.meromorphicNFAt
  have htoEq : toMeromorphicNFAt q z1 = q := (toMeromorphicNFAt_eq_self (f := q) (x := z1)).2 hqNF1
  have hH1 : H z1 = q z1 := by
    have hx : z1 ∈ (Set.univ : Set ℂ) := by simp
    have : toMeromorphicNFOn q (Set.univ : Set ℂ) z1 = toMeromorphicNFAt q z1 z1 :=
      (toMeromorphicNFOn_eq_toMeromorphicNFAt (f := q) (U := (Set.univ : Set ℂ)) hq_mero hx)
    simpa [H, htoEq] using this
  have hH1_ne : H z1 ≠ 0 := by
    have : q z1 ≠ 0 := div_ne_zero hz1 hden1
    simpa [hH1] using this
  have hH_not_top : ∀ z : ℂ, analyticOrderAt H z ≠ ⊤ := by
    exact analyticOrderAt_ne_top_of_exists_ne_zero (hf := hH_entire) ⟨z1, hH1_ne⟩
  have hH_orderNat_zero : ∀ z : ℂ, analyticOrderNatAt H z = 0 := by
    intro z
    have hzdiv :
        (MeromorphicOn.divisor H (Set.univ : Set ℂ)) z = (analyticOrderNatAt H z : ℤ) := by
      simpa using (divisor_univ_eq_analyticOrderNatAt_int (f := H) hH_entire z)
    have : (MeromorphicOn.divisor H (Set.univ : Set ℂ)) z = 0 := by
      simp [hdivH]
    have : (analyticOrderNatAt H z : ℤ) = 0 := by simpa [hzdiv] using this
    exact_mod_cast this
  have hH_ne : ∀ z : ℂ, H z ≠ 0 := by
    intro z
    have hcast : (analyticOrderNatAt H z : ℕ∞) = analyticOrderAt H z :=
      Nat.cast_analyticOrderNatAt (f := H) (z₀ := z) (hH_not_top z)
    have : analyticOrderAt H z = 0 := by
      have : (analyticOrderNatAt H z : ℕ∞) = 0 := by exact_mod_cast (hH_orderNat_zero z)
      simpa [hcast] using this
    exact ((hA z (by simp)).analyticOrderAt_eq_zero).1 this
  have hfA : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) := fun z hzU => hf.analyticAt z
  have hdenA : AnalyticOnNhd ℂ denom (Set.univ : Set ℂ) := fun z hzU => hden_entire.analyticAt z
  have hprodA : AnalyticOnNhd ℂ (fun z => H z * denom z) (Set.univ : Set ℂ) :=
    (hA.mul hdenA)
  have hlocal : f =ᶠ[𝓝 z1] fun z => H z * denom z := by
    have hden_ne : ∀ᶠ z in 𝓝 z1, denom z ≠ 0 :=
      (hden_entire.differentiableAt.continuousAt.ne_iff_eventually_ne continuousAt_const).1 hden1
    have hH_eq_q : H =ᶠ[𝓝 z1] q := by
      have hx : z1 ∈ (Set.univ : Set ℂ) := by simp
      have hloc :
          toMeromorphicNFOn q (Set.univ : Set ℂ) =ᶠ[𝓝 z1] toMeromorphicNFAt q z1 := by
        simpa [H] using (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds (f := q)
          (U := (Set.univ : Set ℂ)) hq_mero hx)
      simpa [H, htoEq] using hloc
    filter_upwards [hden_ne, hH_eq_q] with z hzden hHz
    have hcancel : q z * denom z = f z := by
      dsimp [q]
      field_simp [hzden]
    calc
      f z = q z * denom z := hcancel.symm
      _ = H z * denom z := by simp [hHz]
  have hglob : f = fun z => H z * denom z :=
    AnalyticOnNhd.eq_of_eventuallyEq (hf := hfA) (hg := hprodA) hlocal
  refine ⟨H, hH_entire, hH_ne, ?_⟩
  intro z
  have hglobz : f z = H z * denom z := congrArg (fun g => g z) hglob
  simpa [denom, hadamardDenom, mul_assoc, mul_left_comm, mul_comm] using hglobz

end Complex.Hadamard
end HadamardSourceScope16

section HadamardSourceScope17

open Filter _root_.Function _root_.MeromorphicOn _root_.Erdos970.MeromorphicOn Metric
  _root_.Real _root_.Erdos970.Real Set

namespace Function.locallyFinsuppWithin

open _root_.Function.locallyFinsuppWithin

variable {E : Type*} [NormedAddCommGroup E]

lemma norm_le_abs_of_mem_toClosedBall_support {D : locallyFinsupp E ℤ} {r : ℝ} {z : E}
    (hz : z ∈ (toClosedBall r D).support) : ‖z‖ ≤ |r| := by
  have hz_ball : z ∈ closedBall (0 : E) |r| := (toClosedBall r D).supportWithinDomain hz
  simpa [mem_closedBall, dist_zero_right] using hz_ball

lemma toClosedBall_eval_eq_of_norm_le_abs {D : locallyFinsupp E ℤ} {r : ℝ} {z : E}
    (hz : ‖z‖ ≤ |r|) : toClosedBall r D z = D z := by
  have hz_ball : z ∈ closedBall (0 : E) |r| := by
    simpa [mem_closedBall, dist_zero_right] using hz
  simpa using toClosedBall_eval_within (f := D) hz_ball

lemma mem_toClosedBall_support_of_mem_support_of_norm_le_abs
    {D : locallyFinsupp E ℤ} {r : ℝ} {z : E} (hzD : z ∈ D.support) (hzR : ‖z‖ ≤ |r|) :
    z ∈ (toClosedBall r D).support := by
  rw [Function.mem_support]
  rw [toClosedBall_eval_eq_of_norm_le_abs hzR]
  rwa [Function.mem_support] at hzD

lemma mem_support_of_mem_toClosedBall_support {D : locallyFinsupp E ℤ} {r : ℝ} {z : E}
    (hz : z ∈ (toClosedBall r D).support) : z ∈ D.support := by
  have hnorm : ‖z‖ ≤ |r| := norm_le_abs_of_mem_toClosedBall_support hz
  rw [Function.mem_support] at hz ⊢
  rw [toClosedBall_eval_eq_of_norm_le_abs hnorm] at hz
  exact hz

noncomputable def massClosedBall₀ {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (D : locallyFinsupp E ℤ) (R : ℝ) : ℝ := by
  classical
  exact
    (((finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).toFinset).filter
      (fun z => z ≠ (0 : E))).sum fun z => (D z : ℝ)

end Function.locallyFinsuppWithin

namespace Function.locallyFinsuppWithin

open _root_.Function.locallyFinsuppWithin

theorem logCounting_divisor_eq_circleAverage_sub_const_of_differentiable
    {R : ℝ} {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hR : R ≠ 0) :
    logCounting (divisor f ⊤) R =
      circleAverage (log ‖f ·‖) 0 R - log ‖meromorphicTrailingCoeffAt f 0‖ := by
  have hmero : Meromorphic f := fun z => (hf.analyticAt z).meromorphicAt
  simpa [top_eq_univ] using
    logCounting_divisor_eq_circleAverage_sub_const (f := f) hmero hR

end Function.locallyFinsuppWithin
end HadamardSourceScope17

section HadamardSourceScope18

namespace Real

open _root_.Real

theorem log_one_add_exp_le_add_log_two {x : ℝ} (hx : 0 ≤ x) :
    log (1 + exp x) ≤ x + log 2 := by
  have hexp_one : (1 : ℝ) ≤ exp x := by
    simpa using (one_le_exp_iff.2 hx)
  have hadd : 1 + exp x ≤ 2 * exp x := by linarith
  have hlog : log (1 + exp x) ≤ log (2 * exp x) :=
    log_le_log (by positivity) hadd
  calc
    log (1 + exp x) ≤ log (2 * exp x) := hlog
    _ = log 2 + x := by simp [log_mul, add_comm]
    _ = x + log 2 := by ring

theorem log_one_add_le_add_log_two_of_le_exp {x y : ℝ} (hy : 0 ≤ y) (hx : 0 ≤ x)
    (hxy : y ≤ exp x) :
    log (1 + y) ≤ x + log 2 := by
  have hpos : 0 < (1 : ℝ) + y := by linarith
  have hle : (1 : ℝ) + y ≤ 1 + exp x := by linarith
  exact (log_le_log hpos hle).trans (log_one_add_exp_le_add_log_two hx)

theorem le_exp_of_log_one_add_le {x y : ℝ} (hy : 0 ≤ y) (hxy : log (1 + y) ≤ x) :
    y ≤ exp x := by
  have hpos : 0 < (1 : ℝ) + y := by linarith
  have hone : 1 + y ≤ exp x := (log_le_iff_le_exp hpos).1 hxy
  linarith

theorem neg_posLog_inv_le_log (x : ℝ) : -log⁺ x⁻¹ ≤ log x := by
  linarith [posLog_sub_posLog_inv (x := x), posLog_nonneg (x := x)]

end Real
end HadamardSourceScope18

section HadamardSourceScope20

namespace Real

open _root_.Real

variable {α E : Type*} [SeminormedAddCommGroup E]

theorem log_norm_le_log_one_add_norm (w : E) :
    Real.log ‖w‖ ≤ Real.log (1 + ‖w‖) := by
  by_cases h0 : ‖w‖ = 0
  · simp [h0]
  · have hpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg w) (Ne.symm h0)
    exact Real.log_le_log hpos (by linarith [norm_nonneg w])

variable {F : Type*} [NormedAddCommGroup F]

theorem log_nonneg_mul_inv_norm_of_norm_le {z : F} {r : ℝ} (hz : ‖z‖ ≤ r) :
    0 ≤ Real.log (r * ‖z‖⁻¹) := by
  by_cases hz0 : z = 0
  · simp [hz0]
  · have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
    have : (1 : ℝ) ≤ r * ‖z‖⁻¹ := by
      have : (1 : ℝ) ≤ r / ‖z‖ := (one_le_div hzpos).2 hz
      simpa [div_eq_mul_inv] using this
    exact Real.log_nonneg this

theorem log_two_le_log_two_mul_mul_inv_norm_of_norm_le {z : F} {R : ℝ} (hz0 : z ≠ 0)
    (hz : ‖z‖ ≤ R) :
    Real.log 2 ≤ Real.log ((2 * R) * ‖z‖⁻¹) := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hRdiv : (1 : ℝ) ≤ R / ‖z‖ := (one_le_div hzpos).2 hz
  have hle2 : (2 : ℝ) ≤ (2 * R) * ‖z‖⁻¹ := by
    have : (2 : ℝ) ≤ 2 * (R / ‖z‖) := by nlinarith
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  exact Real.log_le_log (by norm_num) hle2

theorem norm_le_exp_mul_rpow_of_exponent_le
    {f : α → E} {r : α → ℝ} {C ρ τ : ℝ} (hC : 0 ≤ C) (hr : ∀ x, 1 ≤ r x) (hρτ : ρ ≤ τ)
    (hbound : ∀ x, ‖f x‖ ≤ Real.exp (C * (r x) ^ ρ)) : ∀ x, ‖f x‖ ≤ Real.exp (C * (r x) ^ τ) := by
  intro x
  refine (hbound x).trans (Real.exp_le_exp.2 ?_)
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (hr x) hρτ) hC

theorem norm_le_exp_mul_rpow_of_log_growth
    {f : α → E} {r : α → ℝ} {C ρ τ : ℝ} (hC : 0 ≤ C) (hr : ∀ x, 1 ≤ r x) (hρτ : ρ ≤ τ)
    (hlog : ∀ x, Real.log (1 + ‖f x‖) ≤ C * (r x) ^ ρ) : ∀ x, ‖f x‖ ≤ Real.exp (C * (r x) ^ τ) := by
  intro x
  have hpow : (r x) ^ ρ ≤ (r x) ^ τ :=
    Real.rpow_le_rpow_of_exponent_le (hr x) hρτ
  have hlogτ : Real.log (1 + ‖f x‖) ≤ C * (r x) ^ τ :=
    (hlog x).trans (mul_le_mul_of_nonneg_left hpow hC)
  exact Real.le_exp_of_log_one_add_le (norm_nonneg (f x)) hlogτ

theorem log_growth_of_norm_le_exp_mul_rpow
    {f : α → E} {r : α → ℝ} {C τ : ℝ} (hC : 0 < C) (hτ : 0 ≤ τ)
    (hr : ∀ x, 1 ≤ r x) (hbound : ∀ x, ‖f x‖ ≤ Real.exp (C * (r x) ^ τ)) :
    ∃ C' > 0, ∀ x, Real.log (1 + ‖f x‖) ≤ C' * (r x) ^ τ := by
  refine ⟨C + Real.log 2, by
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith, ?_⟩
  intro x
  have hX : (1 : ℝ) ≤ (r x) ^ τ := Real.one_le_rpow (hr x) hτ
  have hB : 0 ≤ C * (r x) ^ τ :=
    mul_nonneg hC.le (Real.rpow_nonneg (le_trans zero_le_one (hr x)) _)
  have hlog :
      Real.log (1 + ‖f x‖) ≤ C * (r x) ^ τ + Real.log 2 :=
    Real.log_one_add_le_add_log_two_of_le_exp (norm_nonneg _) hB (hbound x)
  have hlog2_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith [hlog, hX, hlog2_nonneg]

theorem exists_norm_le_exp_mul_pow_of_rpow_bound
    {f : α → E} {r : α → ℝ} {τ : ℝ} {n : ℕ} (hr : ∀ x, 1 ≤ r x) (hτn : τ < (n : ℝ))
    (hbound : ∃ C > 0, ∀ x, ‖f x‖ ≤ Real.exp (C * (r x) ^ τ)) :
    ∃ C > 0, ∀ x, ‖f x‖ ≤ Real.exp (C * (r x) ^ n) := by
  rcases hbound with ⟨C, hCpos, hC⟩
  have hweak :
      ∀ x, ‖f x‖ ≤ Real.exp (C * (r x) ^ (n : ℝ)) :=
    norm_le_exp_mul_rpow_of_exponent_le
      (f := f) (r := r) hCpos.le hr (le_of_lt hτn) hC
  refine ⟨C, hCpos, ?_⟩
  intro x
  have hpow : (r x) ^ (n : ℝ) = (r x) ^ n := Real.rpow_natCast (r x) n
  simpa [hpow] using hweak x

theorem one_add_le_three_mul_one_add_of_le_two_mul_max {x r : ℝ} (hx : 0 ≤ x)
    (hr : r ≤ 2 * max x 1) :  1 + r ≤ 3 * (1 + x) := by
  have hmax : max x 1 ≤ 1 + x := max_le_iff.2 ⟨by linarith, by linarith⟩
  nlinarith

theorem exp_mul_rpow_le_exp_mul_rpow_of_le_mul
    {A B x y τ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hτ : 0 ≤ τ) (hxy : x ≤ B * y) : Real.exp (A * x ^ τ) ≤ Real.exp ((A * B ^ τ) * y ^ τ) := by
  refine Real.exp_le_exp.2 ?_
  have hpow : x ^ τ ≤ (B * y) ^ τ := Real.rpow_le_rpow hx hxy hτ
  have hsplit : (B * y) ^ τ = B ^ τ * y ^ τ := by
    simpa using (Real.mul_rpow (x := B) (y := y) (z := τ) hB hy)
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left (hpow.trans_eq hsplit) hA

theorem exists_between_self_and_floor_add_one_same_floor {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∃ τ : ℝ, ρ < τ ∧ τ < (Nat.floor ρ + 1 : ℝ) ∧ 0 ≤ τ ∧ Nat.floor τ = Nat.floor ρ := by
  set m : ℕ := Nat.floor ρ
  set τ : ℝ := (ρ + (m + 1 : ℝ)) / 2
  have hm : ρ < (m + 1 : ℝ) := by simpa [m] using Nat.lt_floor_add_one (a := ρ)
  have hτ : ρ < τ := by dsimp [τ]; linarith
  have hτ_lt : τ < (m + 1 : ℝ) := by dsimp [τ]; linarith
  have hτ_nonneg : 0 ≤ τ := le_trans hρ (le_of_lt hτ)
  have hfloorτ : Nat.floor τ = m := by
    have hm_le_τ : (m : ℝ) ≤ τ := le_trans (Nat.floor_le hρ) (le_of_lt hτ)
    have hτ_lt_m1 : τ < (m : ℝ) + 1 := by simpa [add_assoc, add_comm, add_left_comm] using hτ_lt
    exact (Nat.floor_eq_iff hτ_nonneg).2 ⟨hm_le_τ, hτ_lt_m1⟩
  exact ⟨τ, hτ, by simpa [m] using hτ_lt, hτ_nonneg, by simpa [m] using hfloorτ⟩

open Metric _root_.Complex _root_.Erdos970.Complex

theorem log_norm_le_of_log_one_add_growth_on_sphere {f : ℂ → ℂ} {C ρ R : ℝ}
    (hC : ∀ z : ℂ, _root_.Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) {z : ℂ}
    (hz : z ∈ sphere (0 : ℂ) |R|) : _root_.Real.log ‖f z‖ ≤ C * (1 + |R|) ^ ρ := by
  have hz_norm : ‖z‖ = |R| := by
    simpa [mem_sphere, dist_zero_right] using hz
  simpa [hz_norm] using le_trans (log_norm_le_log_one_add_norm (f z)) (hC z)

end Real
end HadamardSourceScope20

section HadamardSourceScope21

open Filter _root_.Function _root_.Erdos970.Function _root_.MeromorphicOn
  _root_.Erdos970.MeromorphicOn Metric _root_.Real _root_.Erdos970.Real Set

namespace Function.locallyFinsuppWithin

open _root_.Function.locallyFinsuppWithin

theorem logCounting_divisor_le_of_log_growth {f : ℂ → ℂ} {ρ C : ℝ} (hf : Differentiable ℂ f)
    (hC : ∀ z : ℂ, log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) {R : ℝ} (hR0 : 0 < R) :
    logCounting (divisor f (Set.univ : Set ℂ)) R
      ≤ C * (1 + |R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
  have hR : R ≠ 0 := ne_of_gt hR0
  have hEq :=
    logCounting_divisor_eq_circleAverage_sub_const_of_differentiable (f := f) hf hR
  have hf_sphere : MeromorphicOn f (sphere (0 : ℂ) |R|) := by
    intro z hz
    exact (hf.analyticAt z).meromorphicAt
  have hInt : CircleIntegrable (fun z : ℂ => log ‖f z‖) 0 R :=
    MeromorphicOn.circleIntegrable_log_norm hf_sphere
  have hbound_circle : ∀ z ∈ sphere (0 : ℂ) |R|,
      log ‖f z‖ ≤ C * (1 + |R|) ^ ρ := by
    intro z hz
    exact log_norm_le_of_log_one_add_growth_on_sphere hC hz
  have hCircleAvg_le :
      circleAverage (fun z : ℂ => log ‖f z‖) 0 R ≤ C * (1 + |R|) ^ ρ :=
    circleAverage_mono_on_of_le_circle (c := (0 : ℂ)) (R := R)
      (f := fun z => log ‖f z‖) hInt hbound_circle
  calc
    logCounting (divisor f (Set.univ : Set ℂ)) R
        = circleAverage (fun z : ℂ => log ‖f z‖) 0 R
            - log ‖meromorphicTrailingCoeffAt f 0‖ := by
            simpa [top_eq_univ] using hEq
    _ ≤ circleAverage (fun z : ℂ => log ‖f z‖) 0 R
          + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
          have :
              -log ‖meromorphicTrailingCoeffAt f 0‖
                ≤ |log ‖meromorphicTrailingCoeffAt f 0‖| :=
            neg_le_abs (log ‖meromorphicTrailingCoeffAt f 0‖)
          linarith
    _ ≤ C * (1 + |R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
          nlinarith [hCircleAvg_le]

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

theorem log_two_mul_massClosedBall₀_le_logCounting {D : locallyFinsupp E ℤ} (hDnonneg : 0 ≤ D)
    {R : ℝ} (hR : 1 ≤ R) :
    (log 2) * massClosedBall₀ D R ≤ logCounting D (2 * R) := by
  classical
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR
  set r : ℝ := 2 * R
  have hrpos : 0 < r := by dsimp [r]; nlinarith
  let Dr := toClosedBall r D
  have hDr_fin : Set.Finite Dr.support := Dr.finiteSupport (isCompact_closedBall (0 : E) |r|)
  let F : Finset E := hDr_fin.toFinset
  let SR : Finset E :=
    (finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).toFinset
  let S : Finset E := SR.filter fun z => z ≠ (0 : E)
  have hS_sub : S ⊆ F := by
    intro z hzS
    have hz_mem_SR : z ∈ SR := (Finset.mem_filter.1 hzS).1
    have hzR : z ∈ (toClosedBall R D).support := by
      exact (finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).mem_toFinset.1
        hz_mem_SR
    have hz_norm_le_R : ‖z‖ ≤ R := by
      have := norm_le_abs_of_mem_toClosedBall_support hzR
      simpa [abs_of_pos hR0] using this
    have hz_norm_le_r : ‖z‖ ≤ |r| := by
      have : ‖z‖ ≤ r := le_trans hz_norm_le_R (by dsimp [r]; nlinarith)
      simpa [abs_of_pos hrpos] using this
    have hzD : z ∈ D.support := mem_support_of_mem_toClosedBall_support hzR
    have : z ∈ Dr.support := by
      simpa [Dr] using
        mem_toClosedBall_support_of_mem_support_of_norm_le_abs (D := D) (r := r) hzD hz_norm_le_r
    exact hDr_fin.mem_toFinset.2 this
  have hlogCounting :
      logCounting D r
        = (F.sum fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) + (D 0 : ℝ) * log r := by
    have hsupp : Function.support (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) ⊆ F := by
      intro z hz
      have : Dr z ≠ 0 := by
        by_contra h0
        simp [Function.mem_support, h0] at hz
      have : z ∈ Dr.support := by simpa [Function.mem_support] using this
      exact hDr_fin.mem_toFinset.2 this
    simp [logCounting, Dr, r,
      finsum_eq_sum_of_support_subset (f := fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) (s := F) hsupp]
  have hsum_le :
      (log 2) * (S.sum fun z => (D z : ℝ))
        ≤ F.sum (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) := by
    have hterm_nonneg : ∀ z ∈ F, 0 ≤ (Dr z : ℝ) * log (r * ‖z‖⁻¹) := by
      intro z hzF
      have hz_sup : z ∈ Dr.support := hDr_fin.mem_toFinset.1 hzF
      have hDz : 0 ≤ Dr z := by
        have hDz' : 0 ≤ D z := hDnonneg z
        have hDrz : Dr z = D z :=
          toClosedBall_eval_eq_of_norm_le_abs (norm_le_abs_of_mem_toClosedBall_support hz_sup)
        simpa [hDrz] using hDz'
      have hlog : 0 ≤ log (r * ‖z‖⁻¹) := by
        have hzle : ‖z‖ ≤ r := by
          have hnorm := norm_le_abs_of_mem_toClosedBall_support hz_sup
          simpa [abs_of_pos hrpos] using hnorm
        exact log_nonneg_mul_inv_norm_of_norm_le hzle
      exact mul_nonneg (by exact_mod_cast hDz) hlog
    have hsumSF :
        S.sum (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹))
          ≤ F.sum (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hS_sub (by
        intro z hzF _; exact hterm_nonneg z hzF)
    have hterm_ge : ∀ z ∈ S, (log 2) * (D z : ℝ) ≤ (Dr z : ℝ) * log (r * ‖z‖⁻¹) := by
      intro z hzS
      have hz0 : z ≠ (0 : E) := (Finset.mem_filter.1 hzS).2
      have hz_norm_le_R : ‖z‖ ≤ R := by
        have hz_mem_SR : z ∈ SR := (Finset.mem_filter.1 hzS).1
        have hzRsup : z ∈ (toClosedBall R D).support := by
          exact (finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).mem_toFinset.1
            hz_mem_SR
        have hnorm := norm_le_abs_of_mem_toClosedBall_support hzRsup
        simpa [abs_of_pos hR0] using hnorm
      have hlog_le : log 2 ≤ log (r * ‖z‖⁻¹) := by
        simpa [r] using log_two_le_log_two_mul_mul_inv_norm_of_norm_le hz0 hz_norm_le_R
      have hDz_nonneg : 0 ≤ D z := hDnonneg z
      have hz_in_ballr : z ∈ closedBall (0 : E) |r| := by
        have : ‖z‖ ≤ r := le_trans hz_norm_le_R (by dsimp [r]; nlinarith)
        simpa [mem_closedBall, dist_zero_right, abs_of_pos hrpos] using this
      have hDrz : Dr z = D z := by
        have hz_norm_le : ‖z‖ ≤ |r| := by
          simpa [mem_closedBall, dist_zero_right] using hz_in_ballr
        simpa [Dr] using toClosedBall_eval_eq_of_norm_le_abs (D := D) (r := r) (z := z) hz_norm_le
      have : (log 2) * (D z : ℝ) ≤ (log (r * ‖z‖⁻¹)) * (D z : ℝ) :=
        mul_le_mul_of_nonneg_right hlog_le (by exact_mod_cast hDz_nonneg)
      simpa [hDrz, mul_assoc, mul_left_comm, mul_comm] using this
    calc
      (log 2) * (S.sum fun z => (D z : ℝ))
          = S.sum (fun z => (log 2) * (D z : ℝ)) := by simp [Finset.mul_sum]
      _ ≤ S.sum (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) :=
        Finset.sum_le_sum fun z hz => hterm_ge z hz
      _ ≤ F.sum (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) := hsumSF
  have hcenter_nonneg : 0 ≤ (D 0 : ℝ) * log r := by
    have hD0 : 0 ≤ D 0 := hDnonneg 0
    have hlogr : 0 ≤ log r := log_nonneg (by nlinarith [hR])
    exact mul_nonneg (by exact_mod_cast hD0) hlogr
  have : (log 2) * (S.sum fun z => (D z : ℝ)) ≤ logCounting D r := by
    rw [hlogCounting]
    nlinarith [hsum_le, hcenter_nonneg]
  simpa [massClosedBall₀, r, S, SR] using this

theorem massClosedBall₀_divisor_le_of_log_growth {f : ℂ → ℂ} {ρ C : ℝ}
    (hf : Differentiable ℂ f)
    (hC : ∀ z : ℂ, log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) {R : ℝ} (hR : 1 ≤ R) :
    massClosedBall₀ (divisor f (Set.univ : Set ℂ)) R
      ≤ (C * (1 + |2 * R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖|) / log 2 := by
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR
  have hlog2pos : 0 < log 2 := log_pos (by norm_num : (1 : ℝ) < 2)
  have hlow :
      (log 2) * massClosedBall₀ (divisor f (Set.univ : Set ℂ)) R
        ≤ logCounting (divisor f (Set.univ : Set ℂ)) (2 * R) :=
    log_two_mul_massClosedBall₀_le_logCounting
      (D := divisor f (Set.univ : Set ℂ))
      (MeromorphicOn.AnalyticOnNhd.divisor_nonneg
        (hf.differentiableOn.analyticOnNhd isOpen_univ)) hR
  have hupp :
      logCounting (divisor f (Set.univ : Set ℂ)) (2 * R)
        ≤ C * (1 + |2 * R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
    have h2R0 : 0 < 2 * R := by nlinarith [hR0]
    simpa using logCounting_divisor_le_of_log_growth (f := f) (ρ := ρ) (C := C) hf hC
      (R := 2 * R) h2R0
  have hmul :
      (log 2) * massClosedBall₀ (divisor f (Set.univ : Set ℂ)) R
        ≤ C * (1 + |2 * R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| :=
    hlow.trans hupp
  have hmul' :
      massClosedBall₀ (divisor f (Set.univ : Set ℂ)) R * log 2
        ≤ C * (1 + |2 * R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  exact (le_div_iff₀ hlog2pos).2 hmul'

end Function.locallyFinsuppWithin
end HadamardSourceScope21

section HadamardSourceScope22

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem Differentiable.divisor_nonneg {f : ℂ → E} (hf : Differentiable ℂ f) :
    0 ≤ MeromorphicOn.divisor f (univ : Set ℂ) :=
  MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hf.differentiableOn.analyticOnNhd isOpen_univ)
end HadamardSourceScope22

section HadamardSourceScope23

noncomputable section

open scoped BigOperators
open Filter

namespace Real

open _root_.Real

lemma two_pow_floor_logb_le {x : ℝ} (hx : 1 ≤ x) :
    (2 : ℝ) ^ (⌊Real.logb 2 x⌋₊ : ℝ) ≤ x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx
  have hlog_nonneg : 0 ≤ Real.logb 2 x :=
    Real.logb_nonneg (b := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2) hx
  have hfloor_le : (⌊Real.logb 2 x⌋₊ : ℝ) ≤ Real.logb 2 x := by
    simpa using (Nat.floor_le hlog_nonneg)
  exact (Real.le_logb_iff_rpow_le (b := (2 : ℝ))
    (x := (⌊Real.logb 2 x⌋₊ : ℝ)) (y := x)
    (by norm_num : (1 : ℝ) < 2) hx0).1 hfloor_le

lemma lt_two_pow_floor_logb_add_one {x : ℝ} (hx : 1 ≤ x) :
    x < (2 : ℝ) ^ ((⌊Real.logb 2 x⌋₊ : ℝ) + 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx
  have hlt : Real.logb 2 x < (⌊Real.logb 2 x⌋₊ : ℝ) + 1 := by
    simpa using (Nat.lt_floor_add_one (Real.logb 2 x))
  exact (Real.logb_lt_iff_lt_rpow (b := (2 : ℝ)) (x := x)
    (y := (⌊Real.logb 2 x⌋₊ : ℝ) + 1)
    (by norm_num : (1 : ℝ) < 2) hx0).1 hlt

lemma dyadicShell_lower_bound {r0 x : ℝ} {k : ℕ} (hr0 : 0 < r0) (hx : r0 ≤ x)
    (hk : ⌊Real.logb 2 (x / r0)⌋₊ = k) :
    r0 * (2 : ℝ) ^ (k : ℝ) ≤ x := by
  have hr0ne : r0 ≠ 0 := ne_of_gt hr0
  have hx1 : (1 : ℝ) ≤ x / r0 := by
    have : r0 / r0 ≤ x / r0 := div_le_div_of_nonneg_right hx hr0.le
    simpa [hr0ne] using this
  have hle : (2 : ℝ) ^ (k : ℝ) ≤ x / r0 := by
    have := Real.two_pow_floor_logb_le (x := x / r0) hx1
    simpa [hk] using this
  have := mul_le_mul_of_nonneg_left hle hr0.le
  have hxEq : r0 * (x / r0) = x := by
    field_simp [hr0ne]
  simpa [mul_assoc, hxEq] using this

lemma dyadicShell_upper_bound {r0 x : ℝ} {k : ℕ} (hr0 : 0 < r0) (hx : r0 ≤ x)
    (hk : ⌊Real.logb 2 (x / r0)⌋₊ = k) :
    x ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1) := by
  have hr0ne : r0 ≠ 0 := ne_of_gt hr0
  have hx1 : (1 : ℝ) ≤ x / r0 := by
    have : r0 / r0 ≤ x / r0 := div_le_div_of_nonneg_right hx hr0.le
    simpa [hr0ne] using this
  have hlt : x / r0 < (2 : ℝ) ^ ((k : ℝ) + 1) := by
    have := Real.lt_two_pow_floor_logb_add_one (x := x / r0) hx1
    simpa [hk] using this
  have := mul_lt_mul_of_pos_left hlt hr0
  have hxEq : r0 * (x / r0) = x := by
    field_simp [hr0ne]
  exact le_of_lt (by simpa [mul_assoc, hxEq] using this)

lemma exists_nat_le_two_pow (A : ℝ) :
    ∃ k0 : ℕ, ∀ n ≥ k0, A ≤ (2 : ℝ) ^ n := by
  have htend : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
  exact eventually_atTop.1 ((tendsto_atTop.1 htend) A)

lemma one_le_dyadicRadius_succ_of_inv_le_two_pow
    {r0 : ℝ} {k0 kk : ℕ} (hr0 : 0 < r0)
    (hk0 : ∀ n ≥ k0, (1 / r0 : ℝ) ≤ (2 : ℝ) ^ n) (hkk : k0 ≤ kk + 1) :
    (1 : ℝ) ≤ r0 * (2 : ℝ) ^ ((kk : ℝ) + 1) := by
  have hr0ne : r0 ≠ 0 := ne_of_gt hr0
  have hpow_nat : (1 / r0 : ℝ) ≤ (2 : ℝ) ^ (kk + 1) := hk0 (kk + 1) hkk
  have hpow_rpow : (1 / r0 : ℝ) ≤ (2 : ℝ) ^ ((kk : ℝ) + 1) := by
    have hcast : (2 : ℝ) ^ ((kk : ℝ) + 1) = (2 : ℝ) ^ (kk + 1) := by
      calc
        (2 : ℝ) ^ ((kk : ℝ) + 1) = (2 : ℝ) ^ ((kk + 1 : ℕ) : ℝ) := by
          simp [Nat.cast_add, Nat.cast_one]
        _ = (2 : ℝ) ^ (kk + 1) := by
          simpa using (Real.rpow_natCast (2 : ℝ) (kk + 1))
    simpa [hcast] using hpow_nat
  have : (r0 * (1 / r0) : ℝ) ≤ r0 * (2 : ℝ) ^ ((kk : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hpow_rpow hr0.le
  simpa [one_div, hr0ne, mul_assoc] using this

lemma one_add_abs_two_mul_dyadicRadius_rpow_le {r0 ρ : ℝ} (k : ℕ)
    (hr0 : 0 < r0) (hρ : 0 ≤ ρ) :
    (1 + |2 * (r0 * (2 : ℝ) ^ ((k : ℝ) + 1))|) ^ ρ
      ≤ (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ k := by
  let Rk : ℝ := r0 * (2 : ℝ) ^ ((k : ℝ) + 1)
  have hRk' : |2 * Rk| = 4 * r0 * (2 : ℝ) ^ (k : ℝ) := by
    have hnonneg : 0 ≤ (2 : ℝ) * Rk := by
      have : 0 ≤ Rk := by
        dsimp [Rk]
        exact mul_nonneg hr0.le (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
      nlinarith
    have hmul : (2 : ℝ) * Rk = 4 * r0 * (2 : ℝ) ^ (k : ℝ) := by
      dsimp [Rk]
      calc
        (2 : ℝ) * (r0 * (2 : ℝ) ^ ((k : ℝ) + 1))
            = (2 * r0) * (2 : ℝ) ^ ((k : ℝ) + 1) := by ring
        _ = (2 * r0) * ((2 : ℝ) ^ (k : ℝ) * (2 : ℝ) ^ (1 : ℝ)) := by
              simp [Real.rpow_add, mul_assoc]
        _ = (2 * r0) * ((2 : ℝ) ^ (k : ℝ) * 2) := by simp [Real.rpow_one]
        _ = 4 * r0 * (2 : ℝ) ^ (k : ℝ) := by ring
    calc
      |2 * Rk| = 2 * Rk := abs_of_nonneg hnonneg
      _ = 4 * r0 * (2 : ℝ) ^ (k : ℝ) := hmul
  have hbase :
      (1 + |2 * Rk|) ≤ (1 + 4 * r0) * (2 : ℝ) ^ (k : ℝ) := by
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k : ℝ) := by
      have : (1 : ℝ) ≤ (2 : ℝ) ^ (k : ℕ) := by
        simpa using (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ (2 : ℝ)))
      simpa [Real.rpow_natCast] using this
    have habs :
        1 + |2 * Rk| ≤ (2 : ℝ) ^ (k : ℝ) + (4 * r0) * (2 : ℝ) ^ (k : ℝ) := by
      rw [hRk']
      simpa [add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using
        (add_le_add_right h1 ((4 * r0) * (2 : ℝ) ^ (k : ℝ)))
    have hfac :
        (2 : ℝ) ^ (k : ℝ) + (4 * r0) * (2 : ℝ) ^ (k : ℝ)
          = (1 + 4 * r0) * (2 : ℝ) ^ (k : ℝ) := by
      ring
    exact habs.trans (le_of_eq hfac)
  have hRnonneg : 0 ≤ (1 + |2 * Rk|) := by linarith [abs_nonneg (2 * Rk)]
  have :
      (1 + |2 * Rk|) ^ ρ ≤ ((1 + 4 * r0) * (2 : ℝ) ^ (k : ℝ)) ^ ρ :=
    Real.rpow_le_rpow hRnonneg hbase hρ
  have hsplit :
      ((1 + 4 * r0) * (2 : ℝ) ^ (k : ℝ)) ^ ρ
        = (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ (k : ℝ)) ^ ρ := by
    have h1 : 0 ≤ (1 + 4 * r0) := by nlinarith [hr0.le]
    have h2 : 0 ≤ (2 : ℝ) ^ (k : ℝ) :=
      le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
    simpa using (Real.mul_rpow h1 h2 (z := ρ))
  have hpow : ((2 : ℝ) ^ (k : ℝ)) ^ ρ = ((2 : ℝ) ^ ρ) ^ k := by
    have h2nonneg : (0 : ℝ) ≤ 2 := by norm_num
    calc
      ((2 : ℝ) ^ (k : ℝ)) ^ ρ = (2 : ℝ) ^ ((k : ℝ) * ρ) := by
        simp [Real.rpow_mul]
      _ = ((2 : ℝ) ^ ρ) ^ (k : ℝ) := by
        simpa [mul_comm] using
          (Real.rpow_mul (x := (2 : ℝ)) (y := ρ) (z := (k : ℝ)) h2nonneg)
      _ = ((2 : ℝ) ^ ρ) ^ k := by
        simp [Real.rpow_natCast]
  calc
    (1 + |2 * (r0 * (2 : ℝ) ^ ((k : ℝ) + 1))|) ^ ρ
        = (1 + |2 * Rk|) ^ ρ := by rfl
    _ ≤ ((1 + 4 * r0) * (2 : ℝ) ^ (k : ℝ)) ^ ρ := this
    _ = (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ (k : ℝ)) ^ ρ := hsplit
    _ = (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ k := by
      simpa [mul_assoc] using congrArg (fun t => (1 + 4 * r0) ^ ρ * t) hpow

lemma tsum_inv_rpow_le_card_mul_of_lower_bound {α : Type*} [Fintype α] {a : α → ℝ}
    {R τ : ℝ} (hR : 0 < R) (hτ : 0 < τ) (ha_nonneg : ∀ x, 0 ≤ a x)
    (ha_lower : ∀ x, R ≤ a x) :
    (∑' x : α, (a x)⁻¹ ^ τ) ≤ (Fintype.card α : ℝ) * (R⁻¹ ^ τ) := by
  have hsum_le :
      (∑ x : α, (a x)⁻¹ ^ τ) ≤ ∑ _x : α, R⁻¹ ^ τ := by
    refine Finset.sum_le_sum ?_
    intro x _hx
    have hinv : (a x)⁻¹ ≤ R⁻¹ := by
      simpa using (inv_anti₀ hR (ha_lower x))
    exact Real.rpow_le_rpow (inv_nonneg.2 (ha_nonneg x)) hinv hτ.le
  simpa [tsum_fintype, Finset.sum_const, nsmul_eq_mul, mul_comm] using hsum_le

lemma inv_dyadicRadius_rpow_eq (r0 τ : ℝ) (k : ℕ) (hr0 : 0 ≤ r0) :
    (r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ =
      (r0⁻¹ : ℝ) ^ τ * ((2 : ℝ) ^ (-τ)) ^ k := by
  have h2k_nonneg : 0 ≤ (2 : ℝ) ^ (k : ℝ) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
  calc
    (r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ =
        (r0 * (2 : ℝ) ^ (k : ℝ)) ^ (-τ) := by
      simpa using (Real.rpow_neg_eq_inv_rpow (r0 * (2 : ℝ) ^ (k : ℝ)) τ).symm
    _ = r0 ^ (-τ) * (((2 : ℝ) ^ (k : ℝ)) ^ (-τ)) := by
      simpa using (Real.mul_rpow hr0 h2k_nonneg (z := -τ))
    _ = (r0⁻¹ : ℝ) ^ τ * ((2 : ℝ) ^ (-τ)) ^ k := by
      have hr0' : r0 ^ (-τ) = (r0⁻¹ : ℝ) ^ τ := by
        simp [Real.rpow_neg_eq_inv_rpow]
      have h2' : ((2 : ℝ) ^ (k : ℝ)) ^ (-τ) = ((2 : ℝ) ^ (-τ)) ^ k := by
        have h2nonneg : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
        calc
          ((2 : ℝ) ^ (k : ℝ)) ^ (-τ) = (2 : ℝ) ^ ((k : ℝ) * (-τ)) := by
            exact (Real.rpow_mul (x := (2 : ℝ)) (y := (k : ℝ)) (z := -τ)
              h2nonneg).symm
          _ = (2 : ℝ) ^ ((-τ) * (k : ℝ)) := by ring_nf
          _ = ((2 : ℝ) ^ (-τ)) ^ (k : ℝ) := by
            exact Real.rpow_mul (x := (2 : ℝ)) (y := -τ) (z := (k : ℝ)) h2nonneg
          _ = ((2 : ℝ) ^ (-τ)) ^ k := by
            simp [Real.rpow_natCast]
      calc
        r0 ^ (-τ) * (((2 : ℝ) ^ (k : ℝ)) ^ (-τ))
            = (r0⁻¹ : ℝ) ^ τ * (((2 : ℝ) ^ (k : ℝ)) ^ (-τ)) := by
              rw [hr0']
        _ = (r0⁻¹ : ℝ) ^ τ * ((2 : ℝ) ^ (-τ)) ^ k := by
              rw [h2']

lemma two_rpow_sub_eq_mul_neg (ρ τ : ℝ) :
    (2 : ℝ) ^ (ρ - τ) = (2 : ℝ) ^ ρ * (2 : ℝ) ^ (-τ) := by
  have h2pos : (0 : ℝ) < (2 : ℝ) := by norm_num
  calc
    (2 : ℝ) ^ (ρ - τ) = (2 : ℝ) ^ (ρ + (-τ)) := by ring_nf
    _ = (2 : ℝ) ^ ρ * (2 : ℝ) ^ (-τ) := by
      simp [Real.rpow_add h2pos]

lemma two_rpow_sub_pow_eq_mul_pow (ρ τ : ℝ) (k : ℕ) :
    ((2 : ℝ) ^ (ρ - τ)) ^ k =
      ((2 : ℝ) ^ ρ) ^ k * (((2 : ℝ) ^ (-τ)) ^ k) := by
  simp [two_rpow_sub_eq_mul_neg, mul_pow]

lemma dyadic_growth_inv_term_eq (C L M r0 ρ τ : ℝ) (k : ℕ) (hr0 : 0 ≤ r0) :
    ((C / L) * (M * ((2 : ℝ) ^ ρ) ^ k)) *
        ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)
      = (((C / L) * M) * (r0⁻¹ : ℝ) ^ τ) * ((2 : ℝ) ^ (ρ - τ)) ^ k := by
  have hrk_inv :
      (r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ =
        (r0⁻¹ : ℝ) ^ τ * (((2 : ℝ) ^ (-τ)) ^ k) :=
    inv_dyadicRadius_rpow_eq r0 τ k hr0
  rw [hrk_inv, two_rpow_sub_pow_eq_mul_pow]
  ac_rfl

lemma dyadic_trailing_inv_term_le (C L r0 τ : ℝ) (k : ℕ) (hr0 : 0 ≤ r0) :
    (C / L) * ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)
      ≤ (((C / L) + 1) * (r0⁻¹ : ℝ) ^ τ) * ((2 : ℝ) ^ (-τ)) ^ k := by
  rw [inv_dyadicRadius_rpow_eq r0 τ k hr0]
  have hcoeff : C / L ≤ C / L + 1 := by linarith
  have hr0Inv_nonneg : 0 ≤ (r0⁻¹ : ℝ) ^ τ :=
    Real.rpow_nonneg (inv_nonneg.2 hr0) _
  have hmul :
      (C / L) * ((r0⁻¹ : ℝ) ^ τ)
        ≤ ((C / L) + 1) * ((r0⁻¹ : ℝ) ^ τ) :=
    mul_le_mul_of_nonneg_right hcoeff hr0Inv_nonneg
  have hqpow_nonneg : 0 ≤ ((2 : ℝ) ^ (-τ)) ^ k :=
    pow_nonneg (le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)) _
  have := mul_le_mul_of_nonneg_right hmul hqpow_nonneg
  simpa [mul_assoc, mul_left_comm, mul_comm] using this

lemma dyadic_growth_mass_mul_inv_le_geometric {C L M X T Ctrail r0 ρ τ : ℝ} {k : ℕ}
    (hL : 0 < L) (hC : 0 ≤ C) (hr0 : 0 ≤ r0)
    (hX : X ≤ M * ((2 : ℝ) ^ ρ) ^ k)
    (hT : T ≤ ((C * X + Ctrail) / L) * ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)) :
    T ≤ (((C / L) * M) * (r0⁻¹ : ℝ) ^ τ) * ((2 : ℝ) ^ (ρ - τ)) ^ k
        + (((Ctrail / L) + 1) * (r0⁻¹ : ℝ) ^ τ) * ((2 : ℝ) ^ (-τ)) ^ k := by
  have hmul : C * X ≤ C * (M * ((2 : ℝ) ^ ρ) ^ k) :=
    mul_le_mul_of_nonneg_left hX hC
  have hnum : C * X + Ctrail ≤ C * (M * ((2 : ℝ) ^ ρ) ^ k) + Ctrail :=
    add_le_add hmul le_rfl
  have hdiv :
      (C * X + Ctrail) / L ≤ (C * (M * ((2 : ℝ) ^ ρ) ^ k) + Ctrail) / L :=
    div_le_div_of_nonneg_right hnum hL.le
  have h2k_nonneg : 0 ≤ (2 : ℝ) ^ (k : ℝ) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (k : ℝ))
  have hrk_nonneg : 0 ≤ r0 * (2 : ℝ) ^ (k : ℝ) :=
    mul_nonneg hr0 h2k_nonneg
  have hfactor_nonneg : 0 ≤ ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ) :=
    Real.rpow_nonneg (inv_nonneg.2 hrk_nonneg) τ
  have hmul' :=
    mul_le_mul_of_nonneg_right hdiv hfactor_nonneg
  have hdecomp :
      ((C * (M * ((2 : ℝ) ^ ρ) ^ k) + Ctrail) / L) *
          ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)
        =
        ((C / L) * (M * ((2 : ℝ) ^ ρ) ^ k)) *
            ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)
          + ((Ctrail / L) * ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)) := by
    let Y : ℝ := (r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ
    have :
        ((C * (M * ((2 : ℝ) ^ ρ) ^ k) + Ctrail) / L) * Y
          = ((C / L) * (M * ((2 : ℝ) ^ ρ) ^ k)) * Y
            + ((Ctrail / L) * Y) := by
      ring
    simpa [Y]
  have hpre :
      T ≤ ((C / L) * (M * ((2 : ℝ) ^ ρ) ^ k)) *
            ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)
          + ((Ctrail / L) * ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)) :=
    hT.trans (hmul'.trans_eq hdecomp)
  have hA := le_of_eq (dyadic_growth_inv_term_eq C L M r0 ρ τ k hr0)
  have hB := dyadic_trailing_inv_term_le Ctrail L r0 τ k hr0
  exact hpre.trans (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using add_le_add hA hB)

lemma two_geometric_shift_add (A B q qσ : ℝ) (k k0 : ℕ) :
    A * q ^ (k + k0) + B * qσ ^ (k + k0)
      = (A * q ^ k0) * q ^ k + (B * qσ ^ k0) * qσ ^ k := by
  rw [pow_add, pow_add]
  ac_rfl

end Real
end
end HadamardSourceScope23

section HadamardSourceScope24

noncomputable section

open Filter Topology Set _root_.Complex _root_.Erdos970.Complex
open scoped BigOperators Topology

namespace Complex.Hadamard

open _root_.Complex

open scoped _root_.Real

noncomputable def divisorMassClosedBall₀ (f : ℂ → ℂ) (R : ℝ) : ℝ :=
  Function.locallyFinsuppWithin.massClosedBall₀ (MeromorphicOn.divisor f (Set.univ : Set ℂ)) R

lemma divisorMassClosedBall₀_le_of_growth {f : ℂ → ℂ} {ρ C : ℝ}
    (hf : Differentiable ℂ f)
    (hC : ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ)
    {R : ℝ} (hR : 1 ≤ R) :
    divisorMassClosedBall₀ f R
      ≤ (C * (1 + |2 * R|) ^ ρ + |Real.log ‖meromorphicTrailingCoeffAt f 0‖|) /
          Real.log 2 := by
  simpa [divisorMassClosedBall₀] using
    (Function.locallyFinsuppWithin.massClosedBall₀_divisor_le_of_log_growth
      (f := f) (ρ := ρ) (C := C) hf hC hR)

lemma exists_r0_le_norm_divisorZeroIndex₀Val {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0) :
    ∃ r0 : ℝ, 0 < r0 ∧
      ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), r0 ≤ ‖divisorZeroIndex₀Val p‖ := by
  classical
  set U : Set ℂ := (Set.univ : Set ℂ)
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  have hDnonneg : 0 ≤ D := by
    simpa [D, U] using (Differentiable.divisor_nonneg (f := f) hf)
  have hzero : ∀ p : divisorZeroIndex₀ f U, f (divisorZeroIndex₀Val p) = 0 := by
    intro p
    set z : ℂ := divisorZeroIndex₀Val p
    have hneTop : meromorphicOrderAt f z ≠ ⊤ := by
      have hzAnal : AnalyticAt ℂ f z := hf.analyticAt z
      have hzA : analyticOrderAt f z ≠ ⊤ :=
        analyticOrderAt_ne_top_of_exists_ne_zero (f := f) (hf := hf) hnot (z := z)
      intro htop
      have hm : meromorphicOrderAt f z = (analyticOrderAt f z).map (↑) :=
        hzAnal.meromorphicOrderAt_eq (𝕜 := ℂ)
      cases h : analyticOrderAt f z with
      | top =>
          exact hzA (by simp [h])
      | coe n =>
          have : (analyticOrderAt f z).map (↑) ≠ (⊤ : WithTop ℤ) := by
            simp [h]
          exact this (by simpa [hm] using htop)
    have hmon : MeromorphicOn f U := by
      intro w hw; exact (hf.analyticAt w).meromorphicAt
    have hdiv : MeromorphicOn.divisor f U z = (meromorphicOrderAt f z).untop₀ := by
      simpa [U] using (MeromorphicOn.divisor_apply (f := f) (U := U) (z := z) hmon (by aesop))
    have hDz : MeromorphicOn.divisor f U z ≠ 0 := by
      have hzsup : z ∈ (MeromorphicOn.divisor f U).support := by
        simp [z]
      simpa [Function.mem_support] using hzsup
    have hposZ : (0 : ℤ) < (meromorphicOrderAt f z).untop₀ := by
      have hge0 : 0 ≤ (meromorphicOrderAt f z).untop₀ := by
        have : 0 ≤ MeromorphicOn.divisor f U z := by
          simpa [D, U, z] using hDnonneg z
        simpa [hdiv] using this
      have hne0 : (meromorphicOrderAt f z).untop₀ ≠ 0 := by
        simpa [hdiv] using hDz
      exact lt_of_le_of_ne hge0 (by simpa [eq_comm] using hne0)
    have hpos : (0 : WithTop ℤ) < meromorphicOrderAt f z := by
      have : (0 : WithTop ℤ) < ((meromorphicOrderAt f z).untop₀ : WithTop ℤ) :=
        WithTop.coe_lt_coe.2 hposZ
      simpa [WithTop.coe_untop₀_of_ne_top hneTop] using this
    have htend0 : Tendsto f (𝓝[≠] z) (𝓝 (0 : ℂ)) :=
      tendsto_zero_of_meromorphicOrderAt_pos (f := f) (x := z) hpos
    have hcontz : ContinuousAt f z := (hf z).continuousAt
    have htendz : Tendsto f (𝓝[≠] z) (𝓝 (f z)) :=
      (hcontz.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] z ≤ 𝓝 z))
    exact tendsto_nhds_unique htendz htend0
  by_cases h0 : f 0 = 0
  · have hD0 : D 0 ≠ 0 := by
      have hmero0 : MeromorphicAt f (0 : ℂ) := (hf.analyticAt 0).meromorphicAt
      have hneTop0 : meromorphicOrderAt f (0 : ℂ) ≠ ⊤ := by
        have hA0 : analyticOrderAt f (0 : ℂ) ≠ ⊤ :=
          analyticOrderAt_ne_top_of_exists_ne_zero (f := f) (hf := hf) hnot (z := 0)
        intro htop
        have hm : meromorphicOrderAt f (0 : ℂ) = (analyticOrderAt f (0 : ℂ)).map (↑) :=
          (hf.analyticAt 0).meromorphicOrderAt_eq (𝕜 := ℂ)
        cases h : analyticOrderAt f (0 : ℂ) with
        | top => exact (hA0 h).elim
        | coe n =>
            have : (analyticOrderAt f (0 : ℂ)).map (↑) ≠ (⊤ : WithTop ℤ) := by
              simp [h]
            exact this (by simpa [hm] using htop)
      have htend0 : Tendsto f (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := by
        have hcont0 : ContinuousAt f (0 : ℂ) := (hf 0).continuousAt
        have : Tendsto f (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by simpa [h0] using hcont0.tendsto
        exact this.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 (0 : ℂ))
      have hpos0 : (0 : WithTop ℤ) < meromorphicOrderAt f (0 : ℂ) :=
        (tendsto_zero_iff_meromorphicOrderAt_pos hmero0).1 htend0
      have hpos0' : (0 : ℤ) < (meromorphicOrderAt f (0 : ℂ)).untop₀ := by
        have : (0 : WithTop ℤ) < ((meromorphicOrderAt f (0 : ℂ)).untop₀ : WithTop ℤ) := by
          simpa [WithTop.coe_untop₀_of_ne_top hneTop0] using hpos0
        simpa using (WithTop.coe_lt_coe.1 this)
      have hdiv0 : D 0 = (meromorphicOrderAt f (0 : ℂ)).untop₀ := by
        have hmon : MeromorphicOn f U := by
          intro w hw; exact (hf.analyticAt w).meromorphicAt
        simpa [D, U] using
          (MeromorphicOn.divisor_apply (f := f) (U := U) (z := (0 : ℂ))
            hmon (by aesop))
      exact by
        have : (meromorphicOrderAt f (0 : ℂ)).untop₀ ≠ 0 := ne_of_gt hpos0'
        simpa [hdiv0] using this
    have hmem0 : (0 : ℂ) ∈ D.support := by
      simp [Function.mem_support, hD0]
    have hdisc : IsDiscrete D.support := by
      simpa [D] using (D.discreteSupport)
    rcases Metric.exists_ball_inter_eq_singleton_of_mem_discrete hdisc hmem0 with ⟨r0, hr0pos, hr0⟩
    refine ⟨r0, hr0pos, ?_⟩
    intro p
    have hp : divisorZeroIndex₀Val p ∈ D.support := by
      simp [D, divisorZeroIndex₀Val_mem_divisor_support (f := f) (U := U) p]
    have hnotBall : divisorZeroIndex₀Val p ∉ Metric.ball (0 : ℂ) r0 := by
      intro hball
      have : divisorZeroIndex₀Val p ∈ Metric.ball (0 : ℂ) r0 ∩ D.support := ⟨hball, hp⟩
      have : divisorZeroIndex₀Val p ∈ ({(0 : ℂ)} : Set ℂ) := by simp [hr0] at this
      have : divisorZeroIndex₀Val p = 0 := by simp [Set.mem_singleton_iff] at this
      exact (divisorZeroIndex₀Val_ne_zero p) this
    have : r0 ≤ ‖divisorZeroIndex₀Val p‖ := by
      have : ¬ ‖divisorZeroIndex₀Val p‖ < r0 := by
        intro hlt
        exact hnotBall (by simpa [Metric.mem_ball, dist_zero_right] using hlt)
      exact le_of_not_gt this
    exact this
  · have hcont0 : ContinuousAt f (0 : ℂ) := (hf 0).continuousAt
    have hne : ∀ᶠ z in 𝓝 (0 : ℂ), f z ≠ 0 := hcont0.eventually_ne h0
    rcases Metric.mem_nhds_iff.1 hne with ⟨r0, hr0pos, hr0⟩
    refine ⟨r0, hr0pos, ?_⟩
    intro p
    have : ¬ ‖divisorZeroIndex₀Val p‖ < r0 := by
      intro hlt
      have hzball : divisorZeroIndex₀Val p ∈ Metric.ball (0 : ℂ) r0 := by
        simpa [Metric.mem_ball, dist_zero_right] using hlt
      have : f (divisorZeroIndex₀Val p) ≠ 0 := hr0 hzball
      exact this (hzero p)
    exact le_of_not_gt this

open scoped BigOperators

lemma card_ball_le_divisorMassClosedBall₀
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {R : ℝ} (hR : 0 < R) :
    (Nat.card {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) // ‖divisorZeroIndex₀Val p‖ ≤ R} : ℝ)
      ≤ divisorMassClosedBall₀ f R := by
  set U : Set ℂ := (Set.univ : Set ℂ)
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  have :
      Fintype {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀Val p‖ ≤ R} := by
    have : Finite {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀Val p‖ ≤ R} := by
      have : Metric.closedBall (0 : ℂ) R ⊆ U := by simp [U]
      simpa using (finite_divisorZeroIndex₀_subtype_norm_le (f := f) (U := U) (B := R) this)
    exact Fintype.ofFinite _
  have hDnonneg : 0 ≤ D := by
    simpa [D, U] using (Differentiable.divisor_nonneg (f := f) hf)
  let SR : Finset ℂ :=
    (Function.locallyFinsuppWithin.finiteSupport (Function.locallyFinsuppWithin.toClosedBall R D)
          (isCompact_closedBall (0 : ℂ) |R|)).toFinset
  let S : Finset ℂ := SR.filter fun z : ℂ => z ≠ 0
  let T : Type :=
    Σ z : S, Fin (Int.toNat (D z.1))
  let φ :
      {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀Val p‖ ≤ R} → T := fun p =>
    let z0 : ℂ := divisorZeroIndex₀Val p.1
    have hz0_memSR : z0 ∈ SR := by
      have hz0_norm : ‖z0‖ ≤ |R| := by
        have : ‖z0‖ ≤ R := p.2
        simpa [abs_of_pos hR] using this
      have hz0_support : z0 ∈ (Function.locallyFinsuppWithin.toClosedBall R D).support := by
        have hz0_suppD : z0 ∈ D.support := by
          simp [z0, D]
        exact Function.locallyFinsuppWithin.mem_toClosedBall_support_of_mem_support_of_norm_le_abs
          hz0_suppD hz0_norm
      exact (Set.Finite.mem_toFinset
        (Function.locallyFinsuppWithin.finiteSupport
          (Function.locallyFinsuppWithin.toClosedBall R D)
            (isCompact_closedBall (0 : ℂ) |R|))).2 hz0_support
    have hz0_ne0 : z0 ≠ 0 := divisorZeroIndex₀Val_ne_zero p.1
    have hz0_memS : z0 ∈ S := Finset.mem_filter.2 ⟨hz0_memSR, hz0_ne0⟩
    ⟨⟨z0, hz0_memS⟩, by
        simpa [z0, divisorZeroIndex₀Val, D] using p.1.1.2⟩
  have hφ_inj : Function.Injective φ := by
    intro p q hpq
    have hσ := (Sigma.mk.inj_iff).1 hpq
    have hzS : (φ p).1 = (φ q).1 := hσ.1
    have hz : divisorZeroIndex₀Val p.1 = divisorZeroIndex₀Val q.1 := by
      simpa [φ] using congrArg Subtype.val hzS
    apply Subtype.ext
    apply Subtype.ext
    apply Sigma.ext
    · exact hz
    · simpa [φ] using hσ.2
  have hcard_le :
      Fintype.card {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀Val p‖ ≤ R} ≤ Fintype.card T :=
    Fintype.card_le_of_injective φ hφ_inj
  have hT_card :
      (Fintype.card T : ℝ) =
        (S.sum fun z : ℂ => (Int.toNat (D z) : ℝ)) := by
    have hNat :
        Fintype.card T = ∑ z : S, Int.toNat (D z.1) := by
      have h1 :
          Fintype.card T = ∑ z : S, Fintype.card (Fin (Int.toNat (D z.1))) := by
        change Fintype.card (Sigma (fun z : S => Fin (Int.toNat (D z.1))))
            = ∑ z : S, Fintype.card (Fin (Int.toNat (D z.1)))
        exact (Fintype.card_sigma (ι := S) (α := fun z : S => Fin (Int.toNat (D z.1))))
      simpa using h1
    have hR :
        (Fintype.card T : ℝ) = ∑ z : S, (Int.toNat (D z.1) : ℝ) := by
      exact_mod_cast hNat
    have hR' :
        (Fintype.card T : ℝ) = S.attach.sum (fun z : S => (Int.toNat (D z.1) : ℝ)) := by
      simpa [Finset.univ_eq_attach] using hR
    calc
      (Fintype.card T : ℝ) = S.attach.sum (fun z : S => (Int.toNat (D z.1) : ℝ)) := hR'
      _ = S.sum (fun z : ℂ => (Int.toNat (D z) : ℝ)) := by
            simpa using (Finset.sum_attach (s := S) (f := fun z : ℂ => (Int.toNat (D z) : ℝ)))
  have htoNat_le : ∀ z ∈ S, (Int.toNat (D z) : ℝ) ≤ (D z : ℝ) := by
    intro z hz
    have hDz_nonneg : 0 ≤ D z := by simpa [D] using hDnonneg z
    have hEqZ : ((Int.toNat (D z) : ℕ) : ℤ) = D z := by
      simpa using (Int.toNat_of_nonneg hDz_nonneg)
    have hEqR : (Int.toNat (D z) : ℝ) = (D z : ℝ) := by
      exact_mod_cast hEqZ
    exact le_of_eq hEqR
  calc
    (Nat.card {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀Val p‖ ≤ R} : ℝ)
        = (Fintype.card {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀Val p‖ ≤ R} : ℝ) := by
          simp [Nat.card_eq_fintype_card]
    _ ≤ (Fintype.card T : ℝ) := by exact_mod_cast hcard_le
    _ = S.sum (fun z : ℂ => (Int.toNat (D z) : ℝ)) := hT_card
    _ ≤ S.sum (fun z : ℂ => (D z : ℝ)) := by
      refine Finset.sum_le_sum ?_
      intro z hz
      exact htoNat_le z hz
    _ = divisorMassClosedBall₀ f R := by
      rfl

lemma card_subtype_le_divisorMassClosedBall₀_of_norm_le
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {s : Set (divisorZeroIndex₀ f (Set.univ : Set ℂ))} [Fintype s]
    {R : ℝ} (hR : 0 < R) (hs : ∀ p : s, ‖divisorZeroIndex₀Val p.1‖ ≤ R) :
    (Fintype.card s : ℝ) ≤ divisorMassClosedBall₀ f R := by
  let Aball : Type :=
    {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) // ‖divisorZeroIndex₀Val p‖ ≤ R}
  have : Fintype Aball := by
    have : Finite Aball := by
      have : Metric.closedBall (0 : ℂ) R ⊆ (Set.univ : Set ℂ) := by simp
      simpa [Aball] using
        (finite_divisorZeroIndex₀_subtype_norm_le (f := f) (U := (Set.univ : Set ℂ))
          (B := R) this)
    exact Fintype.ofFinite _
  have hinj : Function.Injective (fun p : s => (⟨p.1, hs p⟩ : Aball)) := by
    intro p q hpq
    apply Subtype.ext
    exact congrArg (fun x : Aball => x.1) hpq
  have hcard_le : Fintype.card s ≤ Fintype.card Aball :=
    Fintype.card_le_of_injective _ hinj
  have hAball : (Nat.card Aball : ℝ) ≤ divisorMassClosedBall₀ f R := by
    simpa [Aball] using card_ball_le_divisorMassClosedBall₀ (f := f) hf hR
  calc
    (Fintype.card s : ℝ) ≤ (Fintype.card Aball : ℝ) := by exact_mod_cast hcard_le
    _ = (Nat.card Aball : ℝ) := by simp [Nat.card_eq_fintype_card]
    _ ≤ divisorMassClosedBall₀ f R := hAball

lemma divisorZeroIndex₀_dyadicShell_upper_bound
    {f : ℂ → ℂ} {r0 : ℝ}
    (hr0pos : 0 < r0)
    (hr0 : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), r0 ≤ ‖divisorZeroIndex₀Val p‖)
    {k : ℕ} {p : divisorZeroIndex₀ f (Set.univ : Set ℂ)}
    (hp : ⌊Real.logb 2 (‖divisorZeroIndex₀Val p‖ / r0)⌋₊ = k) :
    ‖divisorZeroIndex₀Val p‖ ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1) := by
  exact Real.dyadicShell_upper_bound (r0 := r0) (x := ‖divisorZeroIndex₀Val p‖)
    hr0pos (hr0 p) hp

lemma divisorZeroIndex₀_dyadicShell_lower_bound
    {f : ℂ → ℂ} {r0 : ℝ}
    (hr0pos : 0 < r0)
    (hr0 : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), r0 ≤ ‖divisorZeroIndex₀Val p‖)
    {k : ℕ} {p : divisorZeroIndex₀ f (Set.univ : Set ℂ)}
    (hp : ⌊Real.logb 2 (‖divisorZeroIndex₀Val p‖ / r0)⌋₊ = k) :
    r0 * (2 : ℝ) ^ (k : ℝ) ≤ ‖divisorZeroIndex₀Val p‖ := by
  exact Real.dyadicShell_lower_bound (r0 := r0) (x := ‖divisorZeroIndex₀Val p‖)
    hr0pos (hr0 p) hp

lemma finite_divisorZeroIndex₀_dyadicShell
    {f : ℂ → ℂ} {r0 : ℝ}
    (hr0pos : 0 < r0)
    (hr0 : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), r0 ≤ ‖divisorZeroIndex₀Val p‖)
    (k : ℕ) :
    ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) |
      ⌊Real.logb 2 (‖divisorZeroIndex₀Val p‖ / r0)⌋₊ = k} : Set _).Finite := by
  have hsub :
      {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) |
        ⌊Real.logb 2 (‖divisorZeroIndex₀Val p‖ / r0)⌋₊ = k} ⊆
        {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) |
          ‖divisorZeroIndex₀Val p‖ ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1)} := by
    intro p hp
    exact divisorZeroIndex₀_dyadicShell_upper_bound hr0pos hr0 hp
  have hfin :
      ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) |
        ‖divisorZeroIndex₀Val p‖ ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1)} : Set _).Finite := by
    have :
        Metric.closedBall (0 : ℂ) (r0 * (2 : ℝ) ^ ((k : ℝ) + 1)) ⊆
          (Set.univ : Set ℂ) := by
      simp
    simpa using
      (divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ))
        (B := r0 * (2 : ℝ) ^ ((k : ℝ) + 1)) this)
  exact hfin.subset hsub

lemma tsum_divisorZeroIndex₀_dyadicShell_inv_rpow_le_geometric_of_growth
    {f : ℂ → ℂ} {ρ τ r0 Cgrow : ℝ}
    (hρ : 0 ≤ ρ) (hτpos : 0 < τ) (hf : Differentiable ℂ f)
    (hCgrow_pos : 0 < Cgrow)
    (hCgrow : ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ Cgrow * (1 + ‖z‖) ^ ρ)
    (hr0pos : 0 < r0)
    (hr0 : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
      r0 ≤ ‖divisorZeroIndex₀Val p‖)
    (k : ℕ) (hk_ge_one : 1 ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1)) :
    let kfun : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℕ :=
      fun p => ⌊Real.logb 2 (‖divisorZeroIndex₀Val p‖ / r0)⌋₊
    let S : Set (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := {p | kfun p = k}
    let Ctrail : ℝ := |Real.log ‖meromorphicTrailingCoeffAt f 0‖|
    let A : ℝ := ((Cgrow / Real.log 2) * (1 + 4 * r0) ^ ρ) * (r0⁻¹) ^ τ
    let B : ℝ := ((Ctrail / Real.log 2) + 1) * (r0⁻¹) ^ τ
    let q : ℝ := (2 : ℝ) ^ (ρ - τ)
    let qσ : ℝ := (2 : ℝ) ^ (-τ)
    (∑' p : S, ‖divisorZeroIndex₀Val p.1‖⁻¹ ^ τ) ≤ A * q ^ k + B * qσ ^ k := by
  classical
  intro kfun S Ctrail A B q qσ
  let rk : ℝ := r0 * (2 : ℝ) ^ (k : ℝ)
  let Rk : ℝ := r0 * (2 : ℝ) ^ ((k : ℝ) + 1)
  have hrk_pos : 0 < rk := mul_pos hr0pos (Real.rpow_pos_of_pos (by norm_num) _)
  have hrk0 : 0 ≤ rk := le_of_lt hrk_pos
  have : Finite S := by
    simpa [S, kfun] using (finite_divisorZeroIndex₀_dyadicShell
      (f := f) hr0pos hr0 k).to_subtype
  have : Fintype S := Fintype.ofFinite S
  have hk_upper : ∀ p : S, ‖divisorZeroIndex₀Val p.1‖ ≤ Rk := by
    intro p
    have hk' : kfun p.1 = k := p.2
    simpa [Rk, kfun] using
      divisorZeroIndex₀_dyadicShell_upper_bound (f := f) hr0pos hr0 hk'
  have hk_lower : ∀ p : S, rk ≤ ‖divisorZeroIndex₀Val p.1‖ := by
    intro p
    have hk' : kfun p.1 = k := p.2
    simpa [rk, kfun] using
      divisorZeroIndex₀_dyadicShell_lower_bound (f := f) hr0pos hr0 hk'
  have htsum_le :
      (∑' p : S, ‖divisorZeroIndex₀Val p.1‖⁻¹ ^ τ)
        ≤ (Fintype.card S : ℝ) * (rk⁻¹ ^ τ) := by
    exact Real.tsum_inv_rpow_le_card_mul_of_lower_bound
      (a := fun p : S => ‖divisorZeroIndex₀Val p.1‖)
      hrk_pos hτpos (fun _ => norm_nonneg _) hk_lower
  have hmass_le_growth :
      divisorMassClosedBall₀ f Rk
        ≤ (Cgrow * (1 + |2 * Rk|) ^ ρ + Ctrail) / (Real.log 2) := by
    simpa [Ctrail, Rk] using
      (divisorMassClosedBall₀_le_of_growth (f := f) (ρ := ρ) (C := Cgrow) hf hCgrow
        (R := Rk) hk_ge_one)
  have hcard_le_mass :
      (Fintype.card S : ℝ) ≤ divisorMassClosedBall₀ f Rk := by
    have hRk_pos : 0 < Rk := lt_of_lt_of_le (by norm_num) hk_ge_one
    exact card_subtype_le_divisorMassClosedBall₀_of_norm_le (f := f) hf hRk_pos hk_upper
  have htsum' :
      (∑' p : S, ‖divisorZeroIndex₀Val p.1‖⁻¹ ^ τ)
        ≤ ((Cgrow * (1 + |2 * Rk|) ^ ρ + Ctrail) / (Real.log 2)) * (rk⁻¹ ^ τ) := by
    have hcard_le_growth :
        (Fintype.card S : ℝ) ≤
          (Cgrow * (1 + |2 * Rk|) ^ ρ + Ctrail) / (Real.log 2) :=
      le_trans hcard_le_mass hmass_le_growth
    exact le_trans htsum_le <|
      mul_le_mul_of_nonneg_right hcard_le_growth (Real.rpow_nonneg (inv_nonneg.2 hrk0) τ)
  have hpow_bound :
      (1 + |2 * Rk|) ^ ρ ≤ (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ k := by
    simpa [Rk] using
      Real.one_add_abs_two_mul_dyadicRadius_rpow_le (r0 := r0) (ρ := ρ) k hr0pos hρ
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  simpa [A, B, q, qσ, rk, Ctrail, mul_assoc, mul_left_comm, mul_comm] using
    Real.dyadic_growth_mass_mul_inv_le_geometric
      (C := Cgrow) (L := Real.log 2) (M := (1 + 4 * r0) ^ ρ)
      (X := (1 + |2 * Rk|) ^ ρ)
      (T := ∑' p : S, ‖divisorZeroIndex₀Val p.1‖⁻¹ ^ τ)
      (Ctrail := Ctrail) (r0 := r0) (ρ := ρ) (τ := τ) (k := k)
      hlog2pos hCgrow_pos.le hr0pos.le hpow_bound
      (by simpa [rk] using htsum')

theorem summable_norm_inv_rpow_divisorZeroIndex₀_of_growth {f : ℂ → ℂ} {ρ τ : ℝ}
    (hρ : 0 ≤ ρ) (hτ : ρ < τ) (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    (hgrowth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) :
    Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ τ) := by
  rcases hgrowth with ⟨Cgrow, hCgrow_pos, hCgrow⟩
  have hτpos : 0 < τ := lt_of_le_of_lt hρ hτ
  rcases exists_r0_le_norm_divisorZeroIndex₀Val (f := f) hf hnot with ⟨r0, hr0pos, hr0⟩
  have hr0ne : (r0 : ℝ) ≠ 0 := ne_of_gt hr0pos
  let kfun : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℕ :=
    fun p => ⌊Real.logb 2 (‖divisorZeroIndex₀Val p‖ / r0)⌋₊
  let S : ℕ → Set (divisorZeroIndex₀ f (Set.univ : Set ℂ)) :=
    fun k => {p | kfun p = k}
  have hS : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), ∃! k : ℕ, p ∈ S k := by
    intro p
    refine ⟨kfun p, ?_, ?_⟩
    · simp [S]
    · intro k hk
      simpa [S] using hk.symm
  have hnonneg : 0 ≤ fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ τ := by
    intro p
    exact Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _
  have hSk_summable : ∀ k : ℕ, Summable fun p : S k => ‖divisorZeroIndex₀Val p.1‖⁻¹ ^ τ := by
    intro k
    have : Finite (S k) := by
      simpa [S, kfun] using (finite_divisorZeroIndex₀_dyadicShell
        (f := f) hr0pos hr0 k).to_subtype
    exact Summable.of_finite
  have hshell_summable :
      Summable fun k : ℕ => ∑' p : S k, ‖divisorZeroIndex₀Val p.1‖⁻¹ ^ τ := by
    let q : ℝ := (2 : ℝ) ^ (ρ - τ)
    let qσ : ℝ := (2 : ℝ) ^ (-τ)
    have hq_nonneg : 0 ≤ q := le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
    have hq_lt_one : q < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (x := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
        (sub_neg.2 hτ)
    have hqσ_nonneg : 0 ≤ qσ := le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
    have hqσ_lt_one : qσ < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (x := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
        (by simpa using (neg_neg_of_pos hτpos))
    have hgeom_q : Summable (fun k : ℕ => q ^ k) :=
      summable_geometric_of_lt_one hq_nonneg hq_lt_one
    have hgeom_qσ : Summable (fun k : ℕ => qσ ^ k) :=
      summable_geometric_of_lt_one hqσ_nonneg hqσ_lt_one
    let Ctrail : ℝ := |Real.log ‖meromorphicTrailingCoeffAt f 0‖|
    let A : ℝ := ((Cgrow / Real.log 2) * (1 + 4 * r0) ^ ρ) * (r0⁻¹) ^ τ
    let B : ℝ := ((Ctrail / Real.log 2) + 1) * (r0⁻¹) ^ τ
    rcases Real.exists_nat_le_two_pow (1 / r0) with ⟨k0, hk0⟩
    let A0 : ℝ := A * q ^ k0
    let B0 : ℝ := B * qσ ^ k0
    have hmajor : Summable (fun k : ℕ => A0 * q ^ k + B0 * qσ ^ k) :=
      (hgeom_q.mul_left A0).add (hgeom_qσ.mul_left B0)
    have hshell_summable_shift :
        Summable fun k : ℕ => ∑' p : S (k + k0), ‖divisorZeroIndex₀Val p.1‖⁻¹ ^ τ := by
      refine hmajor.of_nonneg_of_le
        (fun k => by
          have : ∀ p : S (k + k0), 0 ≤ ‖divisorZeroIndex₀Val p.1‖⁻¹ ^ τ := by
            intro p; exact Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _
          exact tsum_nonneg this)
        (fun k => by
          let kk : ℕ := k + k0
          let Rk : ℝ := r0 * (2 : ℝ) ^ ((kk : ℝ) + 1)
          have hRk_ge_one : (1 : ℝ) ≤ Rk := by
            have hkk : k0 ≤ kk + 1 := by
              simp [kk, Nat.add_assoc, Nat.add_comm]
            simpa [Rk] using
              Real.one_le_dyadicRadius_succ_of_inv_le_two_pow hr0pos hk0 hkk
          have hmain :
              (∑' p : S kk, ‖divisorZeroIndex₀Val p.1‖⁻¹ ^ τ) ≤ A * q ^ kk + B * qσ ^ kk := by
            simpa [S, kfun, Ctrail, A, B, q, qσ] using
              tsum_divisorZeroIndex₀_dyadicShell_inv_rpow_le_geometric_of_growth
                (f := f) (ρ := ρ) (τ := τ) hρ hτpos hf hCgrow_pos hCgrow hr0pos hr0 kk hRk_ge_one
          have : A * q ^ kk + B * qσ ^ kk = A0 * q ^ k + B0 * qσ ^ k := by
            simpa [A0, B0, kk] using Real.two_geometric_shift_add A B q qσ k k0
          simpa [kk] using (hmain.trans_eq this)
        )
    exact (summable_nat_add_iff k0).1 hshell_summable_shift
  have hpart :=
    (summable_partition (f := fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
        ‖divisorZeroIndex₀Val p‖⁻¹ ^ τ) hnonneg (s := S) hS)
  exact (hpart.2 ⟨hSk_summable, hshell_summable⟩)

theorem summable_norm_inv_pow_divisorZeroIndex₀_of_growth {f : ℂ → ℂ} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    (hgrowth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) :
    Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (Nat.floor ρ + 1)) := by
  have hτ : ρ < (Nat.floor ρ + 1 : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one (a := ρ))
  have hs :=
    summable_norm_inv_rpow_divisorZeroIndex₀_of_growth (f := f) (ρ := ρ)
      (τ := (Nat.floor ρ + 1 : ℝ)) hρ hτ hf hnot hgrowth
  exact hs.congr fun p => by
    have hcast : ((Nat.floor ρ : ℝ) + 1) = ((Nat.floor ρ + 1 : ℕ) : ℝ) := by
      norm_num
    rw [hcast, Real.rpow_natCast]

end Complex.Hadamard
end
end HadamardSourceScope24

section HadamardSourceScope25

namespace Complex

open _root_.Complex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem norm_le_of_mem_ball_of_forall_sphere_norm_le {f : ℂ → F} {r C : ℝ} {z : ℂ}
    (hd : Differentiable ℂ f) (hrpos : 0 < r)
    (hz : z ∈ Metric.ball (0 : ℂ) r) (hsphere : ∀ u : ℂ, ‖u‖ = r → ‖f u‖ ≤ C) :
    ‖f z‖ ≤ C := by
  let U : Set ℂ := Metric.ball (0 : ℂ) r
  have hfront : ∀ u ∈ frontier U, ‖f u‖ ≤ C := by
    intro u hu
    have hur : ‖u‖ = r := by
      have hfront' : frontier (Metric.ball (0 : ℂ) r) = Metric.sphere (0 : ℂ) r := by
        simpa using (frontier_ball (x := (0 : ℂ)) (r := r) (ne_of_gt hrpos))
      have : u ∈ Metric.sphere (0 : ℂ) r := by simpa [U, hfront'] using hu
      simpa [Metric.mem_sphere, dist_zero_right] using this
    exact hsphere u hur
  exact norm_le_of_forall_mem_frontier_norm_le (f := f) (U := U) Metric.isBounded_ball
    hd.diffContOnCl hfront (subset_closure hz)

end Complex
end HadamardSourceScope25

section HadamardSourceScope26

namespace Complex

open _root_.Complex
namespace CartanBound

open _root_.Real _root_.Erdos970.Real MeasureTheory intervalIntegral
open scoped Topology ENNReal

private lemma neg_log_le_sqrt_two_div {x : ℝ} (hx : 0 < x) (hxle : x ≤ 1) :
    -Real.log x ≤ Real.sqrt (2 / x) := by
  have hx0 : 0 ≤ x := le_of_lt hx
  have ht : 0 ≤ -Real.log x := by
    have : Real.log x ≤ 0 := Real.log_nonpos hx0 hxle
    linarith
  have hsq_div_two_le_exp : ∀ {t : ℝ}, 0 ≤ t → t ^ 2 / 2 ≤ Real.exp t := by
    intro t ht
    let g : ℝ → ℝ := fun u => Real.exp u - u ^ 2 / 2
    have hg_cont : ContinuousOn g (Set.Ici (0 : ℝ)) := by
      have : Continuous g := by fun_prop
      simpa using this.continuousOn
    have hg_diff : DifferentiableOn ℝ g (interior (Set.Ici (0 : ℝ))) := by
      intro u hu
      have : DifferentiableAt ℝ g u := by fun_prop
      exact this.differentiableWithinAt
    have hg'_nonneg : ∀ u ∈ interior (Set.Ici (0 : ℝ)), 0 ≤ deriv g u := by
      intro u hu
      have hu0 : 0 < u := by simpa [interior_Ici] using hu
      have hderiv : deriv g u = Real.exp u - u := by
        have hExp : HasDerivAt Real.exp (Real.exp u) u := Real.hasDerivAt_exp u
        have hpow2 : HasDerivAt (fun z : ℝ => z ^ 2) (2 * u) u := by
          simpa using! ((hasDerivAt_id u).pow 2)
        have hpow2_div : HasDerivAt (fun z : ℝ => z ^ 2 / 2) u u := by
          simpa using (hpow2.div_const (2 : ℝ))
        have hG : HasDerivAt g (Real.exp u - u) u := by
          simpa [g] using! hExp.sub hpow2_div
        exact hG.deriv
      have hu_le : u ≤ Real.exp u := by
        have h1 : u + 1 ≤ Real.exp u := Real.add_one_le_exp u
        exact (le_trans (le_add_of_nonneg_right (by norm_num)) h1)
      have : 0 ≤ Real.exp u - u := sub_nonneg.2 hu_le
      simpa [hderiv] using this
    have hg_mono : MonotoneOn g (Set.Ici (0 : ℝ)) :=
      monotoneOn_of_deriv_nonneg (D := Set.Ici (0 : ℝ)) (hD := convex_Ici 0)
        hg_cont hg_diff hg'_nonneg
    have hg0 : g 0 = 1 := by simp [g]
    have hle : g 0 ≤ g t := hg_mono (by simp) (by simpa [Set.mem_Ici] using ht) ht
    have : (1 : ℝ) ≤ Real.exp t - t ^ 2 / 2 := by simpa [g, hg0] using hle
    linarith
  have hmain : (-Real.log x) ^ 2 / 2 ≤ Real.exp (-Real.log x) := hsq_div_two_le_exp ht
  have hexp : Real.exp (-Real.log x) = x⁻¹ := by simp [Real.exp_neg, Real.exp_log hx]
  have hsq2 : (-Real.log x) ^ 2 ≤ 2 * Real.exp (-Real.log x) := by nlinarith [hmain]
  have hsq' : (-Real.log x) ^ 2 ≤ 2 / x := by simpa [hexp, div_eq_mul_inv, mul_assoc] using hsq2
  have hy : 0 ≤ 2 / x := div_nonneg (by norm_num) (le_of_lt hx)
  exact (Real.le_sqrt ht hy).2 hsq'

lemma posLog_log_one_div_abs_one_sub_le_sqrt {t : ℝ} :
    Real.posLog (1 / |1 - t|) ≤ Real.sqrt (2 / |1 - t|) := by
  by_cases ht : |1 - t| ≤ 1
  · by_cases h0 : |1 - t| = 0
    · have : t = 1 := by
        have : 1 - t = 0 := by simpa [abs_eq_zero] using h0
        linarith
      subst this
      simp
    · have hpos : 0 < |1 - t| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm h0)
      have hle : -Real.log |1 - t| ≤ Real.sqrt (2 / |1 - t|) :=
        neg_log_le_sqrt_two_div (x := |1 - t|) hpos ht
      have hlog : Real.log (1 / |1 - t|) = -Real.log |1 - t| := by simp [Real.log_inv]
      have hnonneg : 0 ≤ Real.log (1 / |1 - t|) := by
        exact Real.log_nonneg ((one_le_div hpos).2 ht)
      have hmax : Real.posLog (1 / |1 - t|) = Real.log (1 / |1 - t|) :=
        max_eq_right hnonneg
      calc
        Real.posLog (1 / |1 - t|) = Real.log (1 / |1 - t|) := hmax
        _ = -Real.log |1 - t| := hlog
        _ ≤ Real.sqrt (2 / |1 - t|) := hle
  · have hlt : 1 < |1 - t| := lt_of_not_ge ht
    have hle0 : Real.log (1 / |1 - t|) ≤ 0 := by
      have hpos : 0 < |1 - t| := lt_trans (by norm_num) hlt
      have : (1 / |1 - t| : ℝ) ≤ 1 := (div_le_one hpos).2 (le_of_lt hlt)
      exact le_trans (Real.log_le_log (by positivity) this) (by simp)
    have hmax : Real.posLog (1 / |1 - t|) = 0 := max_eq_left hle0
    have hrhs : 0 ≤ Real.sqrt (2 / |1 - t|) := by
      exact Real.sqrt_nonneg _
    rw [hmax]
    exact hrhs

noncomputable def φ (t : ℝ) : ℝ :=
  log⁺ (1 / |1 - t|)

lemma measurable_phi : Measurable φ := by
  unfold φ
  simpa [Real.posLog_def, Real.posLog] using
    (by fun_prop : Measurable fun t : ℝ => max 0 (Real.log (1 / |1 - t|)))

lemma phi_le_log_two_of_le_half {t : ℝ} (ht : t ≤ (1 / 2 : ℝ)) : φ t ≤ Real.log 2 := by
  have hnonneg : 0 ≤ (1 - t : ℝ) := by linarith
  have hden : (1 / 2 : ℝ) ≤ |1 - t| := by
    have : (1 / 2 : ℝ) ≤ (1 - t : ℝ) := by linarith
    simpa [abs_of_nonneg hnonneg] using this
  have hfrac : (1 / |1 - t| : ℝ) ≤ 2 := by
    have hhalfpos : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
    have := one_div_le_one_div_of_le hhalfpos hden
    simpa [one_div, div_eq_mul_inv] using this
  have hposLog : log⁺ (1 / |1 - t|) ≤ log⁺ (2 : ℝ) :=
    Real.posLog_le_posLog ((by trans (0 : ℝ); norm_num; positivity)) hfrac
  have habs : (1 : ℝ) ≤ |(2 : ℝ)| := by
    simp
  have hposLog2 : (log⁺ (2 : ℝ)) = Real.log 2 := by
    simpa using (Real.posLog_eq_log habs)
  simpa [φ, hposLog2] using hposLog

lemma phi_eq_zero_of_one_le_abs_one_sub {t : ℝ} (ht : (1 : ℝ) ≤ |1 - t|) : φ t = 0 := by
  have hpos : 0 < |1 - t| := lt_of_lt_of_le (by norm_num) ht
  have hfrac : (1 / |1 - t| : ℝ) ≤ 1 := (div_le_one hpos).2 ht
  have habs : |(1 / |1 - t| : ℝ)| ≤ 1 := by
    have hnonneg : 0 ≤ (1 / |1 - t| : ℝ) := by positivity
    simpa [abs_of_nonneg hnonneg] using hfrac
  have : log⁺ (1 / |1 - t|) = 0 := (Real.posLog_eq_zero_iff _).2 habs
  simpa [φ] using this

lemma φ_nonneg (t : ℝ) : 0 ≤ φ t := by
  simpa [φ] using (Real.posLog_nonneg (x := (1 / |1 - t|)))

lemma φ_le_sqrt (t : ℝ) : φ t ≤ Real.sqrt (2 / |1 - t|) := by
  simpa [φ, Real.posLog] using
    posLog_log_one_div_abs_one_sub_le_sqrt (t := t)

lemma ae_restrict_norm_phi_le_of_forall_mem {A B : ℝ} (hAB : A ≤ B) {g : ℝ → ℝ}
    (hg : ∀ t, 0 ≤ g t) (h : ∀ t ∈ Set.Icc A B, φ t ≤ g t) :
    (fun t : ℝ => ‖φ t‖) ≤ᶠ[ae (volume.restrict (Set.uIoc A B))] fun t => ‖g t‖ := by
  refine
    MeasureTheory.ae_restrict_of_forall_mem (μ := (volume : MeasureTheory.Measure ℝ))
    (s := Set.uIoc A B)
      (by simpa using (measurableSet_uIoc : MeasurableSet (Set.uIoc A B))) ?_
  intro t ht
  have htIoc : t ∈ Set.Ioc A B := by
    simpa [Set.uIoc_of_le hAB] using ht
  have htIcc : t ∈ Set.Icc A B := ⟨le_of_lt htIoc.1, htIoc.2⟩
  have hle : φ t ≤ g t := h t htIcc
  have hφ0 : 0 ≤ φ t := φ_nonneg t
  have hg0 : 0 ≤ g t := hg t
  simpa [Real.norm_eq_abs, abs_of_nonneg hφ0, abs_of_nonneg hg0] using hle

lemma log_norm_one_sub_div_ge_neg_phi {u a : ℂ} {r : ℝ}
    (hur : ‖u‖ = r) (ha : a ≠ 0) (hr : r ≠ ‖a‖) :
    Real.log ‖(1 : ℂ) - u / a‖ ≥ -φ (r / ‖a‖) := by
  have ha_norm : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hnorm_eq : ‖(1 : ℂ) - u / a‖ = ‖a - u‖ / ‖a‖ := by
    have : (1 : ℂ) - u / a = (a - u) / a := by
      field_simp [ha]
    calc
      ‖(1 : ℂ) - u / a‖ = ‖(a - u) / a‖ := by simp [this]
      _ = ‖a - u‖ / ‖a‖ := by simp
  have hrev : |‖a‖ - ‖u‖| ≤ ‖a - u‖ := by
    simpa using (abs_norm_sub_norm_le a u)
  have hdiv : |‖a‖ - ‖u‖| / ‖a‖ ≤ ‖a - u‖ / ‖a‖ :=
    div_le_div_of_nonneg_right hrev (le_of_lt ha_norm)
  have habs : |1 - (r / ‖a‖)| = |‖a‖ - ‖u‖| / ‖a‖ := by
    have hu : ‖u‖ = r := hur
    have ha0 : (‖a‖ : ℝ) ≠ 0 := ha_norm.ne'
    have h1 : (1 : ℝ) - (r / ‖a‖) = (‖a‖ - r) / ‖a‖ := by
      field_simp [ha0]
    calc
      |1 - (r / ‖a‖)| = |(‖a‖ - r) / ‖a‖| := by simp [h1]
      _ = |‖a‖ - r| / ‖a‖ := by simp [abs_div, abs_of_pos ha_norm]
      _ = |‖a‖ - ‖u‖| / ‖a‖ := by simp [hu]
  have hnorm_ge : |1 - (r / ‖a‖)| ≤ ‖(1 : ℂ) - u / a‖ := by
    have : |1 - (r / ‖a‖)| ≤ ‖a - u‖ / ‖a‖ := by
      rw [habs]
      exact hdiv
    rwa [hnorm_eq]
  have hx0 : 0 < |1 - (r / ‖a‖)| := by
    have : (1 - (r / ‖a‖) : ℝ) ≠ 0 := by
      intro h0
      have : r = ‖a‖ := by
        have : r / ‖a‖ = (1 : ℝ) := by linarith
        simpa using (div_eq_iff ha_norm.ne').1 this
      exact hr this
    have : |1 - (r / ‖a‖)| ≠ 0 := by
      simpa [abs_eq_zero] using this
    exact lt_of_le_of_ne (abs_nonneg _) (Ne.symm this)
  have hlogx :
      Real.log |1 - (r / ‖a‖)| ≥ -φ (r / ‖a‖) := by
    have := Real.neg_posLog_inv_le_log (x := |1 - (r / ‖a‖)|)
    simpa [φ, one_div, inv_inv, abs_sub_comm, sub_eq_add_neg] using this
  have hlog_mono :
      Real.log |1 - (r / ‖a‖)| ≤ Real.log ‖(1 : ℂ) - u / a‖ :=
    Real.log_le_log (by positivity) hnorm_ge
  linarith [hlog_mono, hlogx]

noncomputable def K : ℝ :=
  ∫ (t : ℝ) in (1 / 4 : ℝ)..(4 : ℝ), Real.sqrt (2 / |1 - t|) ∂volume

lemma K_nonneg : 0 ≤ K := by
  have hle : (1 / 4 : ℝ) ≤ (4 : ℝ) := by norm_num
  have hnn : ∀ t ∈ Set.Icc (1 / 4 : ℝ) (4 : ℝ), 0 ≤ Real.sqrt (2 / |1 - t|) := by
    intro _t _ht
    exact Real.sqrt_nonneg _
  simpa [K] using (intervalIntegral.integral_nonneg
    (μ := (volume : MeasureTheory.Measure ℝ)) hle hnn)

noncomputable def Cφ : ℝ :=
  Real.log 2 + 4 * K + 1

lemma Cφ_pos : 0 < Cφ := by
  have hlog : 0 < Real.log 2 := by
    simpa using Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hK : 0 ≤ K := K_nonneg
  have : 0 < Real.log 2 + 4 * K := by nlinarith
  have : 0 < Real.log 2 + 4 * K + 1 := by linarith
  simpa [Cφ] using this

lemma intervalIntegrable_sqrt_two_div_abs_one_sub_Icc :
    IntervalIntegrable
      (fun t : ℝ => Real.sqrt (2 / |1 - t|))
      volume (1 / 4 : ℝ) (4 : ℝ) := by
  let f : ℝ → ℝ := fun u => Real.sqrt (2 / |u|)
  have hf0 : IntervalIntegrable f volume (0 : ℝ) (3 : ℝ) := by
    have hpow :
        IntervalIntegrable (fun u : ℝ => u ^ (- (2⁻¹ : ℝ))) volume (0 : ℝ) (3 : ℝ) := by
      simpa using
        (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := (3 : ℝ))
          (r := (- (2⁻¹ : ℝ))) (by linarith : (-1 : ℝ) < - (2⁻¹ : ℝ)))
    have hpow2 :
        IntervalIntegrable (fun u : ℝ => Real.sqrt 2 * u ^ (- (2⁻¹ : ℝ))) volume (0 : ℝ) (3 : ℝ) :=
      hpow.const_mul (Real.sqrt 2)
    have hEq :
        Set.EqOn f (fun u : ℝ => Real.sqrt 2 * u ^ (- (2⁻¹ : ℝ))) (Set.uIoc (0 : ℝ) (3 : ℝ)) := by
      intro u hu
      have hu' : u ∈ Set.Ioc (0 : ℝ) (3 : ℝ) := by
        simpa [Set.uIoc_of_le (show (0 : ℝ) ≤ 3 by norm_num)] using hu
      have hu0 : 0 < u := hu'.1
      have hu0' : 0 ≤ u := le_of_lt hu0
      have habs : |u| = u := abs_of_nonneg hu0'
      have : f u = Real.sqrt (2 / u) := by simp [f, habs]
      calc
        f u = Real.sqrt (2 / u) := this
        _ = Real.sqrt 2 / Real.sqrt u := by simp
        _ = Real.sqrt 2 * (Real.sqrt u)⁻¹ := by simp [div_eq_mul_inv]
        _ = Real.sqrt 2 * (u ^ (2⁻¹ : ℝ))⁻¹ := by simp [Real.sqrt_eq_rpow]
        _ = Real.sqrt 2 * u ^ (- (2⁻¹ : ℝ)) := by
              have h : (u ^ (2⁻¹ : ℝ))⁻¹ = u ^ (- (2⁻¹ : ℝ)) := by
                simpa using (Real.rpow_neg hu0' (2⁻¹ : ℝ)).symm
              simp [h]
    exact
      (IntervalIntegrable.congr (a := (0 : ℝ)) (b := (3 : ℝ))
          (μ := (volume : MeasureTheory.Measure ℝ))
          (f := fun u : ℝ => Real.sqrt 2 * u ^ (- (2⁻¹ : ℝ))) (g := f) hEq.symm)
        hpow2
  have hf0' : IntervalIntegrable f volume (0 : ℝ) (3 / 4 : ℝ) :=
    hf0.mono_set (by
      intro u hu
      have hsub : Set.uIcc (0 : ℝ) (3 / 4 : ℝ) ⊆ Set.uIcc (0 : ℝ) (3 : ℝ) := by
        refine Set.uIcc_subset_uIcc ?_ ?_
        · simp
        · have h0 : (0 : ℝ) ≤ (3 / 4 : ℝ) := by nlinarith
          have h1 : (3 / 4 : ℝ) ≤ (3 : ℝ) := by nlinarith
          exact (Set.mem_uIcc).2 (Or.inl ⟨h0, h1⟩)
      exact hsub hu)
  have hleft :
      IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|)) volume (1 / 4 : ℝ) (1 : ℝ) := by
    have htmp :
        IntervalIntegrable (fun t : ℝ => f (1 - t)) volume (1 : ℝ) ((1 : ℝ) - (3 / 4 : ℝ)) := by
      simpa using (hf0'.comp_sub_left (c := (1 : ℝ)))
    have htmp' :
        IntervalIntegrable (fun t : ℝ => f (1 - t)) volume ((1 : ℝ) - (3 / 4 : ℝ)) (1 : ℝ) :=
      htmp.symm
    have hsub : ((1 : ℝ) - (3 / 4 : ℝ)) = (1 / 4 : ℝ) := by norm_num
    have htmp'' : IntervalIntegrable (fun t : ℝ => f (1 - t)) volume (1 / 4 : ℝ) (1 : ℝ) := by
      simpa [hsub] using htmp'
    simpa [f] using htmp''
  have hright :
      IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|)) volume (1 : ℝ) (4 : ℝ) := by
    have htmp :
        IntervalIntegrable (fun t : ℝ => f (t - 1)) volume (1 : ℝ) ((3 : ℝ) + (1 : ℝ)) := by
      simpa using (hf0.comp_sub_right (c := (1 : ℝ)))
    have hsub : ((3 : ℝ) + (1 : ℝ)) = (4 : ℝ) := by norm_num
    have htmp' : IntervalIntegrable (fun t : ℝ => f (t - 1)) volume (1 : ℝ) (4 : ℝ) := by
      simpa [hsub] using htmp
    have hcongr :
        Set.EqOn (fun t : ℝ => f (t - 1)) (fun t : ℝ => Real.sqrt (2 / |1 - t|))
          (Set.uIoc (1 : ℝ) (4 : ℝ)) := by
      intro t _ht
      simp [f, abs_sub_comm]
    exact
      (IntervalIntegrable.congr (a := (1 : ℝ)) (b := (4 : ℝ))
          (μ := (volume : MeasureTheory.Measure ℝ))
          (f := fun t : ℝ => f (t - 1)) (g := fun t : ℝ => Real.sqrt (2 / |1 - t|)) hcongr)
        htmp'
  exact hleft.trans hright

lemma phi_le_log_two_on_dyadic_of_le_quarter {A t : ℝ} (hA : A ≤ (1 / 4 : ℝ))
    (ht : t ∈ Set.Icc A (2 * A)) :
    φ t ≤ Real.log 2 := by
  have ht_le : t ≤ (1 / 2 : ℝ) := by
    exact ht.2.trans (by nlinarith [hA])
  exact phi_le_log_two_of_le_half ht_le

lemma phi_eq_zero_of_two_le {t : ℝ} (ht : (2 : ℝ) ≤ t) : φ t = 0 := by
  have hden : (1 : ℝ) ≤ |1 - t| := by
    have : (1 : ℝ) ≤ t - 1 := by linarith
    have : (1 : ℝ) ≤ |t - 1| := by
      simpa [abs_of_nonneg (by linarith : 0 ≤ t - 1)] using this
    simpa [abs_sub_comm] using this
  exact phi_eq_zero_of_one_le_abs_one_sub hden

lemma intervalIntegrable_phi_dyadic_small {A : ℝ} (hA0 : 0 ≤ A)
    (hA : A ≤ (1 / 4 : ℝ)) :
    IntervalIntegrable φ volume A (2 * A) := by
  have hA_le : A ≤ 2 * A := by nlinarith
  have hconst : IntervalIntegrable (fun _ : ℝ => (Real.log 2 : ℝ)) volume A (2 * A) :=
    intervalIntegrable_const
  have hmeas :
      AEStronglyMeasurable (fun t : ℝ => φ t) (volume.restrict (Set.uIoc A (2 * A))) :=
    (measurable_phi.aestronglyMeasurable : _)
  have hdom :
      (fun t : ℝ => ‖φ t‖) ≤ᶠ[ae (volume.restrict (Set.uIoc A (2 * A)))]
        fun _ => ‖(Real.log 2 : ℝ)‖ := by
    refine ae_restrict_norm_phi_le_of_forall_mem (A := A) (B := 2 * A) hA_le
      (g := fun _ => (Real.log 2 : ℝ)) (hg := fun _ => ?_) ?_
    · simpa using (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
    · intro t ht
      exact phi_le_log_two_on_dyadic_of_le_quarter hA ht
  exact IntervalIntegrable.mono_fun hconst hmeas hdom

lemma intervalIntegrable_phi_dyadic_large {A : ℝ} (hA : (2 : ℝ) ≤ A) :
    IntervalIntegrable φ volume A (2 * A) := by
  have hA_le : A ≤ 2 * A := by nlinarith
  have hEq : Set.EqOn (fun t : ℝ => φ t) (fun _ => (0 : ℝ)) (Set.uIoc A (2 * A)) := by
    intro t ht
    have htIoc : t ∈ Set.Ioc A (2 * A) := by
      simpa [Set.uIoc_of_le hA_le] using ht
    exact phi_eq_zero_of_two_le (le_trans hA (le_of_lt htIoc.1))
  have hz : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume A (2 * A) :=
    intervalIntegrable_const
  exact (IntervalIntegrable.congr (a := A) (b := (2 * A))
    (μ := (volume : MeasureTheory.Measure ℝ))
    (f := fun _ => (0 : ℝ)) (g := fun t => φ t) (by
      intro t ht
      simpa using (hEq (x := t) ht).symm)) hz

lemma intervalIntegrable_sqrt_two_div_abs_one_sub_dyadic_middle {A : ℝ}
    (hA_lower : (1 / 4 : ℝ) ≤ A) (hA_upper : A ≤ (2 : ℝ)) :
    IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|)) volume A (2 * A) := by
  have hsqrt_big :
      IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|))
        (volume : MeasureTheory.Measure ℝ) (1 / 4 : ℝ) (4 : ℝ) :=
    intervalIntegrable_sqrt_two_div_abs_one_sub_Icc
  refine hsqrt_big.mono_set ?_
  refine Set.uIcc_subset_uIcc ?_ ?_
  · exact (Set.mem_uIcc).2 (Or.inl ⟨hA_lower, by nlinarith [hA_upper]⟩)
  · exact (Set.mem_uIcc).2 (Or.inl ⟨by nlinarith [hA_lower], by nlinarith [hA_upper]⟩)

lemma intervalIntegrable_phi_dyadic_middle {A : ℝ}
    (hA_lower : (1 / 4 : ℝ) ≤ A) (hA_upper : A ≤ (2 : ℝ)) :
    IntervalIntegrable φ volume A (2 * A) := by
  have hA_le : A ≤ 2 * A := by nlinarith [hA_lower]
  have hsqrt :
      IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|)) volume A (2 * A) :=
    intervalIntegrable_sqrt_two_div_abs_one_sub_dyadic_middle hA_lower hA_upper
  have hmeas :
      AEStronglyMeasurable (fun t : ℝ => φ t) (volume.restrict (Set.uIoc A (2 * A))) :=
    (measurable_phi.aestronglyMeasurable : _)
  have hdom :
      (fun t : ℝ => ‖φ t‖) ≤ᶠ[ae (volume.restrict (Set.uIoc A (2 * A)))]
        fun t => ‖Real.sqrt (2 / |1 - t|)‖ := by
    refine ae_restrict_norm_phi_le_of_forall_mem (A := A) (B := 2 * A) hA_le
      (g := fun t => Real.sqrt (2 / |1 - t|)) (hg := fun _ => Real.sqrt_nonneg _) ?_
    intro t _ht
    exact φ_le_sqrt t
  exact IntervalIntegrable.mono_fun hsqrt hmeas hdom

lemma intervalIntegrable_phi_dyadic {A : ℝ} (hA : 0 ≤ A) :
    IntervalIntegrable φ volume A (2 * A) := by
  by_cases hA0 : A = 0
  · subst hA0
    simp
  cases le_total A (1 / 4 : ℝ) with
  | inl hsmall =>
      exact intervalIntegrable_phi_dyadic_small hA hsmall
  | inr hge_quarter =>
      cases le_total (2 : ℝ) A with
      | inl hbig =>
          exact intervalIntegrable_phi_dyadic_large hbig
      | inr hA_le_two =>
          exact intervalIntegrable_phi_dyadic_middle hge_quarter hA_le_two

lemma intervalIntegrable_phi_div {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
    IntervalIntegrable (fun r : ℝ => φ (r / a)) volume R (2 * R) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hRa_nonneg : 0 ≤ R / a := by
    exact div_nonneg hR (le_of_lt ha)
  have hφ : IntervalIntegrable φ volume (R / a) (2 * (R / a)) :=
    intervalIntegrable_phi_dyadic (A := (R / a)) hRa_nonneg
  have := (hφ.comp_mul_right (c := (a⁻¹ : ℝ)))
  have hupper : a * (R * (a⁻¹ * 2)) = (2 * R) := by
    field_simp [ha0]
  simpa [div_eq_mul_inv, ha0, hupper, mul_assoc, mul_left_comm, mul_comm] using this

lemma log_two_le_Cφ : Real.log 2 ≤ Cφ := by
  dsimp [Cφ]
  have hK : 0 ≤ K := K_nonneg
  linarith [hK]

lemma four_mul_K_add_one_le_Cφ : (4 * K + 1 : ℝ) ≤ Cφ := by
  dsimp [Cφ]
  have hlog_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  linarith [hlog_nonneg]

lemma integral_phi_le_Cφ_mul_small {A : ℝ} (hA0 : 0 ≤ A) (hA : A ≤ (1 / 4 : ℝ)) :
    (∫ (t : ℝ) in A..(2 * A), φ t ∂volume) ≤ Cφ * A := by
  have hA_le : A ≤ 2 * A := by nlinarith
  have hφ_int : IntervalIntegrable φ volume A (2 * A) :=
    intervalIntegrable_phi_dyadic_small hA0 hA
  have hconst : IntervalIntegrable (fun _ : ℝ => (Real.log 2 : ℝ)) volume A (2 * A) :=
    intervalIntegrable_const
  have hle_int :
      (∫ (t : ℝ) in A..(2 * A), φ t ∂volume)
        ≤ ∫ (t : ℝ) in A..(2 * A), (Real.log 2 : ℝ) ∂volume := by
    refine intervalIntegral.integral_mono_on (μ := (volume : MeasureTheory.Measure ℝ))
      hA_le hφ_int hconst ?_
    intro t ht
    exact phi_le_log_two_on_dyadic_of_le_quarter hA ht
  have hRHS :
      (∫ (t : ℝ) in A..(2 * A), (Real.log 2 : ℝ) ∂volume) = A * Real.log 2 := by
    simp [intervalIntegral.integral_const, sub_eq_add_neg, add_assoc, two_mul]
  have hcoef : A * Real.log 2 ≤ Cφ * A := by
    have := mul_le_mul_of_nonneg_left log_two_le_Cφ hA0
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  exact le_trans (by simpa [hRHS] using hle_int) hcoef

lemma integral_phi_le_Cφ_mul_large {A : ℝ} (hA : (2 : ℝ) ≤ A) :
    (∫ (t : ℝ) in A..(2 * A), φ t ∂volume) ≤ Cφ * A := by
  have hA_le : A ≤ 2 * A := by nlinarith
  have hφ0 : Set.EqOn (fun t : ℝ => φ t) (fun _ => (0 : ℝ)) (Set.uIcc A (2 * A)) := by
    intro t ht
    have ht' : t ∈ Set.Icc A (2 * A) := by
      simpa [Set.uIcc_of_le hA_le] using ht
    exact phi_eq_zero_of_two_le (le_trans hA ht'.1)
  have hzero : (∫ (t : ℝ) in A..(2 * A), φ t ∂volume) = 0 := by
    simpa using intervalIntegral.integral_congr (μ := (volume : MeasureTheory.Measure ℝ)) hφ0
  have hnonneg : (0 : ℝ) ≤ Cφ * A := mul_nonneg (le_of_lt Cφ_pos) (by linarith)
  simpa [hzero] using hnonneg

lemma integral_sqrt_two_div_abs_one_sub_le_K_dyadic_middle {A : ℝ}
    (hA_lower : (1 / 4 : ℝ) ≤ A) (hA_upper : A ≤ (2 : ℝ)) :
    (∫ (t : ℝ) in A..(2 * A), Real.sqrt (2 / |1 - t|) ∂volume) ≤ K := by
  let s (t : ℝ) : ℝ := Real.sqrt (2 / |1 - t|)
  have hA_le : A ≤ 2 * A := by nlinarith [hA_lower]
  have hA_upper' : (2 * A : ℝ) ≤ 4 := by nlinarith [hA_upper]
  have hsqrt_big : IntervalIntegrable s volume (1 / 4 : ℝ) (4 : ℝ) := by
    simpa [s] using intervalIntegrable_sqrt_two_div_abs_one_sub_Icc
  have hle_K :
      (∫ (t : ℝ) in A..(2 * A), s t ∂volume)
        ≤ ∫ (t : ℝ) in (1 / 4 : ℝ)..(4 : ℝ), s t ∂volume := by
    refine intervalIntegral.integral_mono_interval (μ := (volume : MeasureTheory.Measure ℝ))
      (c := (1 / 4 : ℝ)) (d := (4 : ℝ)) (a := A) (b := (2 * A))
      hA_lower hA_le hA_upper' ?_ hsqrt_big
    exact Filter.Eventually.of_forall (fun _t => Real.sqrt_nonneg _)
  simpa [K, s] using hle_K

lemma K_le_four_mul_K_add_one_mul_of_quarter_le {A : ℝ} (hA : (1 / 4 : ℝ) ≤ A) :
    K ≤ (4 * K + 1) * A := by
  have hcoef : 1 ≤ 4 * A := by nlinarith [hA]
  have hK : 0 ≤ K := K_nonneg
  nlinarith [hK, hcoef]

lemma integral_phi_le_Cφ_mul_middle {A : ℝ}
    (hA_lower : (1 / 4 : ℝ) ≤ A) (hA_upper : A ≤ (2 : ℝ)) :
    (∫ (t : ℝ) in A..(2 * A), φ t ∂volume) ≤ Cφ * A := by
  let s (t : ℝ) : ℝ := Real.sqrt (2 / |1 - t|)
  have hA_le : A ≤ 2 * A := by nlinarith [hA_lower]
  have hφ_int : IntervalIntegrable φ volume A (2 * A) :=
    intervalIntegrable_phi_dyadic_middle hA_lower hA_upper
  have hsqrt : IntervalIntegrable s volume A (2 * A) := by
    simpa [s] using
      intervalIntegrable_sqrt_two_div_abs_one_sub_dyadic_middle hA_lower hA_upper
  have hle_int :
      (∫ (t : ℝ) in A..(2 * A), φ t ∂volume)
        ≤ ∫ (t : ℝ) in A..(2 * A), s t ∂volume := by
    refine intervalIntegral.integral_mono_on
      (μ := (volume : MeasureTheory.Measure ℝ)) hA_le hφ_int hsqrt ?_
    intro t _ht
    exact φ_le_sqrt t
  have hsqrt_le : (∫ (t : ℝ) in A..(2 * A), s t ∂volume) ≤ (4 * K + 1) * A := by
    have hK : (∫ (t : ℝ) in A..(2 * A), s t ∂volume) ≤ K := by
      simpa [s] using integral_sqrt_two_div_abs_one_sub_le_K_dyadic_middle hA_lower hA_upper
    exact le_trans hK (K_le_four_mul_K_add_one_mul_of_quarter_le hA_lower)
  have hcoef : (4 * K + 1 : ℝ) * A ≤ Cφ * A :=
    mul_le_mul_of_nonneg_right four_mul_K_add_one_le_Cφ (by nlinarith [hA_lower])
  exact le_trans hle_int (le_trans hsqrt_le hcoef)

lemma integral_phi_le_Cφ_mul {A : ℝ} (hA : 0 ≤ A) :
    (∫ (t : ℝ) in A..(2 * A), φ t ∂volume) ≤ Cφ * A := by
  by_cases hA0 : A = 0
  · subst hA0
    simp [Cφ, φ, K]
  cases le_total A (1 / 4 : ℝ) with
  | inl hsmall =>
      exact integral_phi_le_Cφ_mul_small hA hsmall
  | inr hge_quarter =>
      cases le_total (2 : ℝ) A with
      | inl hbig =>
          exact integral_phi_le_Cφ_mul_large hbig
      | inr hA_le_two =>
          exact integral_phi_le_Cφ_mul_middle hge_quarter hA_le_two

open scoped BigOperators

lemma volume_Ioc_two_mul_ne_zero {R : ℝ} (hR : 0 < R) :
    (volume : MeasureTheory.Measure ℝ) (Set.Ioc R (2 * R)) ≠ 0 := by
  have hpos : (0 : ℝ) < 2 * R - R := by nlinarith [hR]
  simp [Real.volume_Ioc, ENNReal.ofReal_eq_zero, not_le_of_gt hpos]

lemma volume_Ioc_two_mul_diff_finset_ne_zero (bad : Finset ℝ) {R : ℝ} (hR : 0 < R) :
    (volume : MeasureTheory.Measure ℝ) (Set.Ioc R (2 * R) \ (bad : Set ℝ)) ≠ 0 := by
  have hbad_meas : (volume : MeasureTheory.Measure ℝ) (bad : Set ℝ) = 0 := by
    simpa using (bad.measure_zero (μ := (volume : MeasureTheory.Measure ℝ)))
  have hdiff :
      (volume : MeasureTheory.Measure ℝ) (Set.Ioc R (2 * R) \ (bad : Set ℝ))
        = (volume : MeasureTheory.Measure ℝ) (Set.Ioc R (2 * R)) := by
    simpa [Set.sdiff_eq, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
      (MeasureTheory.measure_sdiff_null (s := Set.Ioc R (2 * R)) (t := (bad : Set ℝ))
        hbad_meas)
  simpa [hdiff] using volume_Ioc_two_mul_ne_zero hR

lemma restrict_volume_Ioc_two_mul_diff_finset_ne_zero (bad : Finset ℝ) {R : ℝ} (hR : 0 < R) :
    (volume.restrict (Set.Ioc R (2 * R))) (Set.Ioc R (2 * R) \ (bad : Set ℝ)) ≠ 0 := by
  have hsubset : Set.Ioc R (2 * R) \ (bad : Set ℝ) ⊆ Set.Ioc R (2 * R) := by
    intro r hr
    exact hr.1
  have hinter :
      (Set.Ioc R (2 * R) \ (bad : Set ℝ)) ∩ Set.Ioc R (2 * R)
        = (Set.Ioc R (2 * R) \ (bad : Set ℝ)) := by
    exact Set.inter_eq_left.mpr hsubset
  simpa [MeasureTheory.Measure.restrict_apply, measurableSet_Ioc, hinter] using
    volume_Ioc_two_mul_diff_finset_ne_zero bad hR

lemma integral_phi_div_le_Cφ_mul {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
    (∫ (r : ℝ) in R..(2 * R), φ (r / a) ∂volume) ≤ Cφ * R := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hrew :
      (∫ (r : ℝ) in R..(2 * R), φ (r / a) ∂volume)
        = a * (∫ (t : ℝ) in (R / a)..(2 * R / a), φ t ∂volume) := by
    simp [smul_eq_mul, mul_left_comm, mul_comm, div_eq_mul_inv, ha0]
  rw [hrew]
  have hA : 0 ≤ R / a := by
    exact div_nonneg hR ha.le
  have hle : (∫ (t : ℝ) in (R / a)..(2 * (R / a)), φ t ∂volume) ≤ Cφ * (R / a) :=
    integral_phi_le_Cφ_mul (A := R / a) hA
  have hEq : (2 * R / a) = 2 * (R / a) := by ring
  have hle' :
      (∫ (t : ℝ) in (R / a)..(2 * R / a), φ t ∂volume) ≤ Cφ * (R / a) := by
    simpa [hEq] using hle
  have ha_nonneg : 0 ≤ a := ha.le
  have := mul_le_mul_of_nonneg_left hle' ha_nonneg
  have hRHS : a * (Cφ * (R / a)) = Cφ * R := by
    field_simp [ha0]
  simpa [hRHS, mul_assoc, mul_left_comm, mul_comm] using this

lemma intervalIntegrable_sum_mul_phi_div
    {ι : Type} (s : Finset ι) (w : ι → ℝ) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) {R : ℝ} (hR : 0 ≤ R) :
    IntervalIntegrable (∑ i ∈ s, fun r : ℝ => w i * φ (r / a i))
      volume R (2 * R) := by
  refine IntervalIntegrable.sum (μ := volume) (a := R) (b := 2 * R)
    (s := s) (f := fun i : ι => fun r : ℝ => w i * φ (r / a i)) ?_
  intro i hi
  have hφi : IntervalIntegrable (fun r : ℝ => φ (r / a i)) volume R (2 * R) :=
    intervalIntegrable_phi_div (a := a i) (R := R) (ha i hi) hR
  simpa [mul_assoc] using hφi.const_mul (w i)

lemma integral_sum_mul_phi_div_le_Cφ_mul_sum
    {ι : Type} (s : Finset ι) (w : ι → ℝ) (a : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (ha : ∀ i ∈ s, 0 < a i) {R : ℝ} (hR : 0 ≤ R) :
    (∫ r in R..(2 * R), (∑ i ∈ s, fun r : ℝ => w i * φ (r / a i)) r ∂volume)
      ≤ Cφ * (∑ i ∈ s, w i) * R := by
  have hint : ∀ i ∈ s, IntervalIntegrable (fun r : ℝ => w i * φ (r / a i))
      volume R (2 * R) := by
    intro i hi
    have hφi : IntervalIntegrable (fun r : ℝ => φ (r / a i)) volume R (2 * R) :=
      intervalIntegrable_phi_div (a := a i) (R := R) (ha i hi) hR
    simpa [mul_assoc] using hφi.const_mul (w i)
  have hsum_int :
      (∫ r in R..(2 * R), (∑ i ∈ s, fun r : ℝ => w i * φ (r / a i)) r ∂volume)
        = ∑ i ∈ s, ∫ r in R..(2 * R), (fun r : ℝ => w i * φ (r / a i)) r
            ∂volume := by
    simpa using
      (intervalIntegral.integral_finsetSum (μ := volume) (a := R) (b := 2 * R)
        (s := s) (f := fun i : ι => fun r : ℝ => w i * φ (r / a i)) hint)
  rw [hsum_int]
  have hsum_le :
      (∑ i ∈ s, ∫ r in R..(2 * R), (fun r : ℝ => w i * φ (r / a i)) r ∂volume)
        ≤ ∑ i ∈ s, w i * (Cφ * R) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hphi :
        (∫ r in R..(2 * R), φ (r / a i) ∂volume) ≤ Cφ * R :=
      integral_phi_div_le_Cφ_mul (a := a i) (R := R) (ha i hi) hR
    have := mul_le_mul_of_nonneg_left hphi (hw i hi)
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  refine le_trans hsum_le ?_
  have : (∑ i ∈ s, w i * (Cφ * R)) = Cφ * (∑ i ∈ s, w i) * R := by
    calc
      (∑ i ∈ s, w i * (Cφ * R)) = (∑ i ∈ s, w i) * (Cφ * R) := by
        simp [Finset.sum_mul]
      _ = Cφ * (∑ i ∈ s, w i) * R := by
        ac_rfl
  exact le_of_eq this

lemma exists_radius_Ioc_sum_mul_phi_div_le_Cφ_mul_sum_avoid
    {ι : Type} (s : Finset ι) (w : ι → ℝ) (a : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (ha : ∀ i ∈ s, 0 < a i)
    (bad : Finset ℝ) {R : ℝ} (hR : 0 < R) :
    ∃ r ∈ Set.Ioc R (2 * R), r ∉ bad ∧
      (∑ i ∈ s, w i * φ (r / a i)) ≤ Cφ * (∑ i ∈ s, w i) := by
  by_contra hbad
  have hforall :
      ∀ r ∈ Set.Ioc R (2 * R), r ∉ bad →
        Cφ * (∑ i ∈ s, w i) < (∑ i ∈ s, w i * φ (r / a i)) := by
    intro r hr hrbad
    have : ¬(∑ i ∈ s, w i * φ (r / a i)) ≤ Cφ * (∑ i ∈ s, w i) := by
      intro hle
      exact hbad ⟨r, hr, hrbad, hle⟩
    exact lt_of_not_ge this
  let g : ℝ → ℝ := ∑ i ∈ s, fun r : ℝ => w i * φ (r / a i)
  have hg_int : IntervalIntegrable g volume R (2 * R) := by
    simpa [g] using intervalIntegrable_sum_mul_phi_div s w a ha hR.le
  have hconst_int :
      IntervalIntegrable (fun _r : ℝ => Cφ * (∑ i ∈ s, w i)) volume R (2 * R) :=
    intervalIntegrable_const
  have hlt_meas :
      (volume.restrict (Set.Ioc R (2 * R)))
        {r | Cφ * (∑ i ∈ s, w i) < g r} ≠ 0 := by
    have hall : Set.Ioc R (2 * R) \ (bad : Set ℝ) ⊆ {r | Cφ * (∑ i ∈ s, w i) < g r} := by
      intro r hr
      have hrIoc : r ∈ Set.Ioc R (2 * R) := hr.1
      have hrbad : r ∉ bad := by simpa using hr.2
      simpa [g] using hforall r hrIoc hrbad
    have hle :
        (volume.restrict (Set.Ioc R (2 * R))) (Set.Ioc R (2 * R) \ (bad : Set ℝ))
          ≤ (volume.restrict (Set.Ioc R (2 * R))) {r | Cφ * (∑ i ∈ s, w i) < g r} :=
      MeasureTheory.measure_mono hall
    have hpos' :
        (volume.restrict (Set.Ioc R (2 * R))) (Set.Ioc R (2 * R) \ (bad : Set ℝ)) ≠ 0 := by
      exact restrict_volume_Ioc_two_mul_diff_finset_ne_zero bad hR
    intro hzero
    have : (volume.restrict (Set.Ioc R (2 * R))) (Set.Ioc R (2 * R) \ (bad : Set ℝ)) = 0 :=
      le_antisymm (le_trans hle (le_of_eq hzero)) (by positivity)
    exact hpos' this
  have hlt_int :
      (∫ r in R..(2 * R), (Cφ * (∑ i ∈ s, w i)) ∂volume)
        < ∫ r in R..(2 * R), g r ∂volume := by
    have hab : R ≤ 2 * R := by nlinarith [hR.le]
    refine intervalIntegral.integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero (μ := volume)
      (a := R) (b := 2 * R) (f := fun _ => (Cφ * (∑ i ∈ s, w i))) (g := g)
      hab hconst_int hg_int ?_ hlt_meas
    have hmem : ∀ᵐ r ∂ (volume.restrict (Set.Ioc R (2 * R))), r ∈ Set.Ioc R (2 * R) :=
      MeasureTheory.ae_restrict_mem (by simp)
    have hnotBad :
        ∀ᵐ r ∂ (volume.restrict (Set.Ioc R (2 * R))), r ∉ (bad : Set ℝ) := by
      simpa using
        (bad.finite_toSet.countable.ae_notMem (μ := (volume.restrict (Set.Ioc R (2 * R)))))
    filter_upwards [hmem, hnotBad] with r hrIoc hrNotBad
    have hrNotBad' : r ∉ bad := by simpa using hrNotBad
    exact le_of_lt (by simpa [g] using hforall r hrIoc hrNotBad')
  have hconst_eval :
      (∫ r in R..(2 * R), (Cφ * (∑ i ∈ s, w i)) ∂volume) = Cφ * (∑ i ∈ s, w i) * R := by
    simp [intervalIntegral.integral_const, sub_eq_add_neg, mul_comm]
    ring
  have hg_le :
      (∫ r in R..(2 * R), g r ∂volume) ≤ Cφ * (∑ i ∈ s, w i) * R := by
    simpa [g] using integral_sum_mul_phi_div_le_Cφ_mul_sum s w a hw ha hR.le
  have : ¬(Cφ * (∑ i ∈ s, w i) * R < Cφ * (∑ i ∈ s, w i) * R) := lt_irrefl _
  have hcontra : Cφ * (∑ i ∈ s, w i) * R < Cφ * (∑ i ∈ s, w i) * R := by
    have := hlt_int
    simpa [hconst_eval] using (this.trans_le hg_le)
  exact this hcontra

end CartanBound
end Complex
end HadamardSourceScope26

section HadamardSourceScope27

noncomputable section

namespace Complex.Hadamard

open _root_.Complex

open _root_.Complex _root_.Erdos970.Complex _root_.Real _root_.Erdos970.Real

lemma max_one_norm_div_pow_le_one_add_rpow
    {m : ℕ} {τ r : ℝ} {u a : ℂ}
    (hur : ‖u‖ = r)
    (hmτ : (m : ℝ) ≤ τ) :
    max 1 (‖u / a‖ ^ m) ≤ 1 + (r / ‖a‖) ^ τ := by
  by_cases hx : ‖u / a‖ ≤ 1
  · have hpowm_le1 : ‖u / a‖ ^ m ≤ 1 := pow_le_one₀ (norm_nonneg (u / a)) hx
    have hr0 : 0 ≤ r := by simpa [hur] using (norm_nonneg u)
    have hbase : 0 ≤ r / ‖a‖ := div_nonneg hr0 (norm_nonneg a)
    have hnonneg : 0 ≤ (r / ‖a‖) ^ τ := Real.rpow_nonneg hbase τ
    have hle1 : (1 : ℝ) ≤ 1 + (r / ‖a‖) ^ τ := le_add_of_nonneg_right hnonneg
    have hle2 : ‖u / a‖ ^ m ≤ 1 + (r / ‖a‖) ^ τ := hpowm_le1.trans hle1
    exact (max_le_iff).2 ⟨hle1, hle2⟩
  · have hx1 : 1 < ‖u / a‖ := lt_of_not_ge hx
    have hpow :
        (‖u / a‖ : ℝ) ^ (m : ℝ) ≤ (‖u / a‖ : ℝ) ^ τ :=
      Real.rpow_le_rpow_of_exponent_le (le_of_lt hx1) hmτ
    have hpow' : ‖u / a‖ ^ m ≤ (‖u / a‖ : ℝ) ^ τ := by
      simpa [Real.rpow_natCast] using hpow
    have hmax_add : max 1 (‖u / a‖ ^ m) ≤ 1 + ‖u / a‖ ^ m := by
      refine max_le (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_left (by positivity))
    have : max 1 (‖u / a‖ ^ m) ≤ 1 + (‖u / a‖ : ℝ) ^ τ :=
      hmax_add.trans (by nlinarith [hpow'])
    simpa [norm_div, hur] using this

lemma norm_inv_weierstrassFactor_le_exp_near
    {m : ℕ} {τ r : ℝ} {u a : ℂ}
    (hur : ‖u‖ = r) (ha : a ≠ 0) (hr : r ≠ ‖a‖)
    (hmτ : (m : ℝ) ≤ τ) :
    ‖(weierstrassFactor m (u / a))⁻¹‖
      ≤ Real.exp (CartanBound.φ (r / ‖a‖) + (m : ℝ) * (1 + (r / ‖a‖) ^ τ)) := by
  have hlog_one :
      Real.log ‖(1 : ℂ) - u / a‖ ≥ -CartanBound.φ (r / ‖a‖) :=
    CartanBound.log_norm_one_sub_div_ge_neg_phi (hur := hur) (ha := ha) (hr := hr)
  have hbase :=
    log_norm_weierstrassFactor_ge_log_norm_one_sub_sub (m := m) (z := (u / a))
  have hlogE :
      Real.log ‖weierstrassFactor m (u / a)‖
        ≥ -CartanBound.φ (r / ‖a‖) - (m : ℝ) * max 1 (‖u / a‖ ^ m) := by
    have hpls :=
      norm_partialLogSum_le_nat_mul_max_one_norm_pow m (u / a)
    linarith [hbase, hlog_one, hpls]
  have hmax :
      max 1 (‖u / a‖ ^ m) ≤ 1 + (r / ‖a‖) ^ τ :=
    max_one_norm_div_pow_le_one_add_rpow (m := m) (τ := τ) (r := r) (u := u) (a := a) hur hmτ
  have hneglog :
      -Real.log ‖weierstrassFactor m (u / a)‖
        ≤ CartanBound.φ (r / ‖a‖) + (m : ℝ) * (1 + (r / ‖a‖) ^ τ) := by
    have : -Real.log ‖weierstrassFactor m (u / a)‖
        ≤ CartanBound.φ (r / ‖a‖) + (m : ℝ) * max 1 (‖u / a‖ ^ m) := by
      linarith [hlogE]
    have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    exact this.trans (by nlinarith [mul_le_mul_of_nonneg_left hmax hm0])
  have hpos : 0 < ‖weierstrassFactor m (u / a)‖ := by
    have : weierstrassFactor m (u / a) ≠ 0 := by
      intro h0
      have : u / a = (1 : ℂ) := (weierstrassFactor_eq_zero_iff m (u / a)).1 h0
      have : u = a := (div_eq_one_iff_eq ha).1 this
      have : r = ‖a‖ := by simpa [this] using hur.symm
      exact (hr this).elim
    exact norm_pos_iff.2 this
  have hEq :
      ‖(weierstrassFactor m (u / a))⁻¹‖ =
        Real.exp (-Real.log ‖weierstrassFactor m (u / a)‖) := by
    simp [norm_inv, Real.exp_neg, Real.exp_log hpos]
  have := Real.exp_le_exp.2 hneglog
  simpa [hEq] using this

lemma norm_inv_weierstrassFactor_le_exp_far
    {m : ℕ} {τ r : ℝ} {u a : ℂ}
    (hur : ‖u‖ = r) (ha : a ≠ 0)
    (hz : ‖u / a‖ ≤ (1 / 2 : ℝ)) (hτ_le : τ ≤ (m + 1 : ℝ)) :
    ‖(weierstrassFactor m (u / a))⁻¹‖ ≤ Real.exp ((2 : ℝ) * (r / ‖a‖) ^ τ) := by
  by_cases hu : u = 0
  · subst hu
    have hr0 : r = 0 := by simpa [hur] using (norm_zero : ‖(0 : ℂ)‖ = 0)
    subst hr0
    have h0 : 0 ≤ ((0 : ℝ) / ‖a‖) ^ τ := by
      exact Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 0 / ‖a‖) τ
    have h0' : 0 ≤ (2 : ℝ) * ((0 : ℝ) / ‖a‖) ^ τ := mul_nonneg (by norm_num) h0
    have hexp : (1 : ℝ) ≤ Real.exp ((2 : ℝ) * ((0 : ℝ) / ‖a‖) ^ τ) :=
      (Real.one_le_exp_iff).2 h0'
    simpa using hexp
  have hlogE :=
    log_norm_weierstrassFactor_ge_neg_two_pow (m := m) (z := (u / a)) hz
  have hneglog : -Real.log ‖weierstrassFactor m (u / a)‖ ≤ (2 : ℝ) * (r / ‖a‖) ^ τ := by
    have h1 : -Real.log ‖weierstrassFactor m (u / a)‖ ≤ (2 : ℝ) * ‖u / a‖ ^ (m + 1) := by
      linarith [hlogE]
    set x : ℝ := ‖u / a‖
    have hx1 : x ≤ 1 := le_trans (by simpa [x] using hz) (by norm_num)
    have hxpos : 0 < x := by
      simpa [x] using (norm_pos_iff.2 (div_ne_zero hu ha))
    have hτ_le' : τ ≤ ((m + 1 : ℕ) : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one] using hτ_le
    have hpow_rpow : x ^ ((m + 1 : ℕ) : ℝ) ≤ x ^ τ :=
      Real.rpow_le_rpow_of_exponent_ge hxpos hx1 hτ_le'
    have hpow : x ^ (m + 1) ≤ x ^ τ := by
      simpa [← Real.rpow_natCast] using hpow_rpow
    have h2x : (2 : ℝ) * x ^ (m + 1) ≤ (2 : ℝ) * x ^ τ :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    have h2 : (2 : ℝ) * ‖u / a‖ ^ (m + 1) ≤ (2 : ℝ) * (‖u / a‖ : ℝ) ^ τ := by
      simpa [x] using h2x
    have h3 : (‖u‖ / ‖a‖) ^ τ = (r / ‖a‖) ^ τ := by
      simp [hur]
    exact (h1.trans h2).trans_eq (by simp [h3])
  have hpos : 0 < ‖weierstrassFactor m (u / a)‖ := by
    have : weierstrassFactor m (u / a) ≠ 0 := by
      intro h0
      have : u / a = (1 : ℂ) := (weierstrassFactor_eq_zero_iff m (u / a)).1 h0
      have : u = a := (div_eq_one_iff_eq ha).1 this
      have : (‖u / a‖ : ℝ) = 1 := by simpa [this] using (by simp [ha])
      linarith [hz, this]
    exact norm_pos_iff.2 this
  have hEq :
      ‖(weierstrassFactor m (u / a))⁻¹‖ =
        Real.exp (-Real.log ‖weierstrassFactor m (u / a)‖) := by
    simp [norm_inv, Real.exp_neg, Real.exp_log hpos]
  have := Real.exp_le_exp.2 hneglog
  simpa [hEq] using this

end Complex.Hadamard
end
end HadamardSourceScope27

section HadamardSourceScope28

noncomputable section

namespace Complex.Hadamard

open _root_.Complex

open scoped BigOperators
open Filter Finset _root_.Real _root_.Erdos970.Real Topology

section CartanFiniteSum

variable {α : Type*}

private lemma summable_ite_mem_finset [DecidableEq α] (s : Finset α) (u : α → ℝ) :
    Summable (fun a => if a ∈ s then u a else 0) :=
  summable_of_ne_finset_zero (s := s) fun a ha => by simp [ite_eq_right ha]

private lemma tsum_ite_mem_finset [DecidableEq α] (s : Finset α) (u : α → ℝ) :
    (∑' a, if a ∈ s then u a else 0) = ∑ a ∈ s, u a := by
  classical
  simpa [Finset.sum_ite] using
    (hasSum_sum_of_ne_finset_zero (s := s) (f := fun a => if a ∈ s then u a else 0)
      fun a ha => by simp [ite_eq_right ha]).tsum_eq

private lemma tsum_add_four (u₁ u₂ u₃ u₄ : α → ℝ)
    (h₁ : Summable u₁) (h₂ : Summable u₂) (h₃ : Summable u₃) (h₄ : Summable u₄) :
    tsum (fun a => ((u₁ a + u₂ a) + u₃ a) + u₄ a)
      = tsum u₁ + tsum u₂ + tsum u₃ + tsum u₄ := by
  calc
    tsum (fun a => ((u₁ a + u₂ a) + u₃ a) + u₄ a)
        = tsum (fun a => (u₁ a + u₂ a) + (u₃ a + u₄ a)) := by
          simp [add_comm, add_left_comm]
    _ = tsum (fun a => u₁ a + u₂ a) + tsum (fun a => u₃ a + u₄ a) :=
        Summable.tsum_add (h₁.add h₂) (h₃.add h₄)
    _ = tsum u₁ + tsum u₂ + tsum u₃ + tsum u₄ := by
        rw [Summable.tsum_add h₁ h₂, Summable.tsum_add h₃ h₄]
        ring

end CartanFiniteSum

noncomputable def cartanProductConstant (m : ℕ) (τ Sτ : ℝ) : ℝ :=
  ((CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 3) * (Sτ + 1)

lemma cartanProductConstant_nonneg {m : ℕ} {τ Sτ : ℝ} (hSτ : 0 ≤ Sτ) :
    0 ≤ cartanProductConstant m τ Sτ := by
  have hS : 0 ≤ Sτ + 1 := by linarith
  have hA : 0 ≤ (CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 3 := by
    have hCφ : 0 ≤ CartanBound.Cφ := le_of_lt CartanBound.Cφ_pos
    have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    have h4τ : 0 ≤ (4 : ℝ) ^ τ := by positivity
    nlinarith [hCφ, hm0, h4τ]
  simpa [cartanProductConstant] using mul_nonneg hA hS

lemma rpow_div_norm_divisorZeroIndex₀_eq
    {f : ℂ → ℂ} {r τ : ℝ} (hr : 0 ≤ r)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    (r / ‖divisorZeroIndex₀Val p‖) ^ τ =
      (r ^ τ) * ((‖divisorZeroIndex₀Val p‖⁻¹ : ℝ) ^ τ) := by
  have hp : 0 ≤ (‖divisorZeroIndex₀Val p‖⁻¹ : ℝ) := by positivity
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (Real.mul_rpow (x := r) (y := (‖divisorZeroIndex₀Val p‖⁻¹ : ℝ)) (z := τ) hr hp)

lemma tsum_rpow_div_norm_divisorZeroIndex₀_eq
    {f : ℂ → ℂ} {r τ : ℝ} (hr : 0 ≤ r) :
    (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
        (r / ‖divisorZeroIndex₀Val p‖) ^ τ)
      = (r ^ τ) * ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
          ‖divisorZeroIndex₀Val p‖⁻¹ ^ τ := by
  calc
    (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
        (r / ‖divisorZeroIndex₀Val p‖) ^ τ)
        = ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
            (r ^ τ) * (‖divisorZeroIndex₀Val p‖⁻¹ : ℝ) ^ τ := by
            refine tsum_congr ?_
            intro p
            exact rpow_div_norm_divisorZeroIndex₀_eq (f := f) (τ := τ) hr p
    _ = (r ^ τ) * ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
          ‖divisorZeroIndex₀Val p‖⁻¹ ^ τ := by
        simp [tsum_mul_left]

lemma tsum_two_mul_rpow_div_norm_divisorZeroIndex₀_le
    {f : ℂ → ℂ} {r τ : ℝ} (hr : 0 ≤ r) (hτ_nonneg : 0 ≤ τ) :
    (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
        (2 : ℝ) * (r / ‖divisorZeroIndex₀Val p‖) ^ τ)
      ≤ (2 : ℝ) * ((∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
          ‖divisorZeroIndex₀Val p‖⁻¹ ^ τ) + 1) * (1 + r) ^ τ := by
  set Sτ : ℝ :=
    ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), ‖divisorZeroIndex₀Val p‖⁻¹ ^ τ
  have htsum :
      (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
          (2 : ℝ) * (r / ‖divisorZeroIndex₀Val p‖) ^ τ)
        = (2 : ℝ) * (r ^ τ) * Sτ := by
    calc
      (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
          (2 : ℝ) * (r / ‖divisorZeroIndex₀Val p‖) ^ τ)
          = (2 : ℝ) * ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
              (r / ‖divisorZeroIndex₀Val p‖) ^ τ := by
              simp [tsum_mul_left]
      _ = (2 : ℝ) * ((r ^ τ) * Sτ) := by
              rw [tsum_rpow_div_norm_divisorZeroIndex₀_eq (f := f) (τ := τ) hr]
      _ = (2 : ℝ) * (r ^ τ) * Sτ := by ring
  have hSτ_nonneg : 0 ≤ Sτ :=
    tsum_nonneg (fun _ => Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _)
  have h1r : r ^ τ ≤ (1 + r) ^ τ :=
    Real.rpow_le_rpow (by positivity) (by linarith) hτ_nonneg
  have hS : Sτ ≤ Sτ + 1 := by linarith
  have hle : (r ^ τ) * Sτ ≤ (1 + r) ^ τ * (Sτ + 1) :=
    mul_le_mul h1r hS (by linarith) (by positivity)
  rw [htsum]
  have : (2 : ℝ) * (r ^ τ) * Sτ ≤ (2 : ℝ) * (Sτ + 1) * (1 + r) ^ τ := by
    nlinarith [hle]
  simpa [Sτ, mul_assoc, mul_left_comm, mul_comm] using this

lemma sum_rpow_div_norm_divisorZeroIndex₀_le
    {f : ℂ → ℂ} {r τ : ℝ} (small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
    (hr : 0 ≤ r) (hτ_nonneg : 0 ≤ τ)
    (hsumτ :
      Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
        ‖divisorZeroIndex₀Val p‖⁻¹ ^ τ)) :
    (∑ p ∈ small, (r / ‖divisorZeroIndex₀Val p‖) ^ τ)
      ≤ ((∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
          ‖divisorZeroIndex₀Val p‖⁻¹ ^ τ) + 1) * (1 + r) ^ τ := by
  set Sτ : ℝ :=
    ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), ‖divisorZeroIndex₀Val p‖⁻¹ ^ τ
  have hsum_inv :
      (∑ p ∈ small, (‖divisorZeroIndex₀Val p‖⁻¹ : ℝ) ^ τ) ≤ Sτ := by
    have hnn : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
        0 ≤ (‖divisorZeroIndex₀Val p‖⁻¹ : ℝ) ^ τ := by
      intro p
      positivity
    simpa [Sτ] using
      (Summable.sum_le_tsum (s := small)
        (f := fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
          (‖divisorZeroIndex₀Val p‖⁻¹ : ℝ) ^ τ)
        (fun p _ => hnn p) hsumτ)
  have hsum_eq :
      ∑ p ∈ small, (r / ‖divisorZeroIndex₀Val p‖) ^ τ =
        (r ^ τ) * ∑ p ∈ small, (‖divisorZeroIndex₀Val p‖⁻¹ : ℝ) ^ τ := by
    simp [rpow_div_norm_divisorZeroIndex₀_eq (f := f) (τ := τ) hr, Finset.mul_sum]
  have h1r : r ^ τ ≤ (1 + r) ^ τ :=
    Real.rpow_le_rpow (by positivity) (by linarith) hτ_nonneg
  have hS : (∑ p ∈ small, (‖divisorZeroIndex₀Val p‖⁻¹ : ℝ) ^ τ) ≤ Sτ + 1 := by
    linarith [hsum_inv]
  have hle :
      (r ^ τ) * (∑ p ∈ small, (‖divisorZeroIndex₀Val p‖⁻¹ : ℝ) ^ τ)
        ≤ (1 + r) ^ τ * (Sτ + 1) :=
    mul_le_mul h1r hS (by positivity) (by positivity)
  simpa [Sτ, hsum_eq, mul_assoc, mul_left_comm, mul_comm] using hle

lemma add_four_le_add_two_mul_of_le {x₁ x₂ x₃ x₄ A B C : ℝ}
    (h₁ : x₁ ≤ A) (h₂ : x₂ ≤ B) (h₃ : x₃ ≤ B) (h₄ : x₄ ≤ C) :
    x₁ + x₂ + x₃ + x₄ ≤ A + 2 * B + C := by
  nlinarith

lemma cartan_majorant_four_term_bound
    {xφ x0 xm xt Cφ m q Y T : ℝ}
    (hφ : xφ ≤ Cφ * q * Y * T)
    (h0 : x0 ≤ m * q * Y * T)
    (hm : xm ≤ m * q * Y * T)
    (ht : xt ≤ (2 : ℝ) * Y * T) :
    xφ + x0 + xm + xt ≤ (Cφ + (2 : ℝ) * m) * q * Y * T + (2 : ℝ) * Y * T := by
  have h :=
    add_four_le_add_two_mul_of_le hφ h0 hm ht
  have hring :
      Cφ * (q * (Y * T)) + 2 * (m * (q * (Y * T))) + 2 * (Y * T)
        = (Cφ + (2 : ℝ) * m) * (q * (Y * T)) + (2 : ℝ) * (Y * T) := by
    ring
  simpa [mul_assoc, hring] using h

lemma cartan_majorant_add_two_factor (A Y T : ℝ) :
    A * Y * T + (2 : ℝ) * Y * T = ((A + 2) * Y) * T := by
  ring

lemma cartan_majorant_pad_two_to_three {A S T : ℝ} (hS : 0 ≤ S + 1) (hT : 0 ≤ T) :
    ((A + 2) * (S + 1)) * T ≤ ((A + 3) * (S + 1)) * T := by
  have h : (A + 2) * (S + 1) ≤ (A + 3) * (S + 1) := by
    nlinarith
  exact mul_le_mul_of_nonneg_right h hT

lemma cartan_majorant_nonneg
    {f : ℂ → ℂ} {m : ℕ} {τ r : ℝ} (hr : 0 ≤ r)
    (small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) :
    letI : DecidableEq (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := Classical.decEq _
    let ap : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀Val p‖
    let b : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p =>
        if p ∈ small then
          CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
        else
          (2 : ℝ) * (r / ap p) ^ τ
    ∀ p, 0 ≤ b p := by
  classical
  dsimp
  intro p
  let ap : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun q => ‖divisorZeroIndex₀Val q‖
  have hap : ap p = ‖divisorZeroIndex₀Val p‖ := rfl
  by_cases hp : p ∈ small
  · have hφ : 0 ≤ CartanBound.φ (r / ap p) := CartanBound.φ_nonneg (t := r / ap p)
    have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    have h1 : 0 ≤ (1 + (r / ap p) ^ τ) := by positivity
    have : 0 ≤ CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ) := by
      nlinarith [hφ, hm0, h1]
    simpa [hap, hp, ap] using this
  · have hbase : 0 ≤ r / ap p := div_nonneg hr (by positivity)
    have hpow : 0 ≤ (r / ap p) ^ τ := Real.rpow_nonneg hbase τ
    have : 0 ≤ (2 : ℝ) * (r / ap p) ^ τ := mul_nonneg (by norm_num) hpow
    simpa [hap, hp, ap] using this

lemma cartan_majorant_summable
    {f : ℂ → ℂ} {m : ℕ} {τ r : ℝ} (hr : 0 ≤ r)
    (small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
    (hsumτ :
      Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
        ‖divisorZeroIndex₀Val p‖⁻¹ ^ τ)) :
    letI : DecidableEq (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := Classical.decEq _
    let ap : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀Val p‖
    let b : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p =>
        if p ∈ small then
          CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
        else
          (2 : ℝ) * (r / ap p) ^ τ
    Summable b := by
  classical
  dsimp
  let ap : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun q => ‖divisorZeroIndex₀Val q‖
  let b : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
    fun p =>
      if p ∈ small then
        CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
      else
        (2 : ℝ) * (r / ap p) ^ τ
  have hb : Summable b := by
    let b₁ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p =>
        if p ∈ small then
          CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
        else 0
    let b₂ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p => if p ∈ small then 0 else (2 : ℝ) * (r / ap p) ^ τ
    have hb_decomp : b = fun p => b₁ p + b₂ p := by
      funext p
      by_cases hp : p ∈ small <;> simp [b, b₁, b₂, hp]
    have hb₁ : Summable b₁ := by
      simpa [b₁] using
        summable_ite_mem_finset small
          (fun p => CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ))
    have hb₂ : Summable b₂ := by
      have hconst :
          Summable (fun p =>
            (2 : ℝ) * (r ^ τ) * (‖divisorZeroIndex₀Val p‖⁻¹ ^ τ)) :=
        hsumτ.mul_left ((2 : ℝ) * (r ^ τ))
      refine Summable.of_nonneg_of_le
        (fun p => by
          by_cases hp : p ∈ small
          · simp [b₂, hp]
          · have : 0 ≤ (2 : ℝ) * (r / ap p) ^ τ := by positivity
            simpa [b₂, hp] using this)
        (fun p => ?_) hconst
      by_cases hp : p ∈ small
      · have : 0 ≤ (2 : ℝ) * (r ^ τ) * (‖divisorZeroIndex₀Val p‖⁻¹ ^ τ) := by positivity
        simpa [b₂, hp] using this
      · have hrpow : (r / ap p) ^ τ = (r ^ τ) * (‖divisorZeroIndex₀Val p‖⁻¹ ^ τ) := by
          simpa [ap] using rpow_div_norm_divisorZeroIndex₀_eq (f := f) (τ := τ) hr p
        simp [b₂, hp, hrpow, mul_assoc, mul_left_comm, mul_comm]
    simpa [hb_decomp] using hb₁.add hb₂
  refine hb.congr ?_
  intro p
  by_cases hp : p ∈ small <;> simp [b, ap, hp]

lemma cartan_card_small_le
    {f : ℂ → ℂ} {τ R : ℝ} (hRpos : 0 < R) (hτ_nonneg : 0 ≤ τ)
    (small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
    (hsmall : ∀ p ∈ small, ‖divisorZeroIndex₀Val p‖ ≤ 4 * R)
    (hsumτ :
      Summable
        (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
          ‖divisorZeroIndex₀Val p‖⁻¹ ^ τ)) :
    (small.card : ℝ)
      ≤ (4 * R) ^ τ
          * ((∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
                ‖divisorZeroIndex₀Val p‖⁻¹ ^ τ) + 1) := by
  classical
  set Sτ : ℝ :=
    ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), ‖divisorZeroIndex₀Val p‖⁻¹ ^ τ
  have hsum_le : (∑ p ∈ small, ‖divisorZeroIndex₀Val p‖⁻¹ ^ τ) ≤ Sτ := by
    have hnn :
        ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
          0 ≤ ‖divisorZeroIndex₀Val p‖⁻¹ ^ τ := by
      intro p
      exact Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _
    simpa [Sτ] using
      (Summable.sum_le_tsum (s := small)
        (f := fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
          ‖divisorZeroIndex₀Val p‖⁻¹ ^ τ)
        (fun p _ => hnn p) hsumτ)
  have hgeom_sum :
      (small.card : ℝ) ≤ ∑ p ∈ small, (4 * R) ^ τ * ‖divisorZeroIndex₀Val p‖⁻¹ ^ τ := by
    have hcard_eq : (small.card : ℝ) = ∑ p ∈ small, (1 : ℝ) := by simp
    rw [hcard_eq]
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hp_le : ‖divisorZeroIndex₀Val p‖ ≤ 4 * R := hsmall p hp
    have hap : 0 < ‖divisorZeroIndex₀Val p‖ :=
      norm_pos_iff.2 (divisorZeroIndex₀Val_ne_zero p)
    have hbase : (1 : ℝ) ≤ (4 * R) / ‖divisorZeroIndex₀Val p‖ := by
      exact (le_div_iff₀ hap).2 (by simpa [mul_one] using hp_le)
    have : (1 : ℝ) ≤ ((4 * R) / ‖divisorZeroIndex₀Val p‖) ^ τ :=
      Real.one_le_rpow hbase hτ_nonneg
    have hdiv :
        ((4 * R) / ‖divisorZeroIndex₀Val p‖) ^ τ =
          (4 * R) ^ τ * (‖divisorZeroIndex₀Val p‖)⁻¹ ^ τ := by
      have h4 : 0 ≤ (4 * R : ℝ) := by nlinarith [le_of_lt hRpos]
      have ha : 0 ≤ (‖divisorZeroIndex₀Val p‖ : ℝ)⁻¹ := by positivity
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (Real.mul_rpow (x := (4 * R : ℝ))
          (y := (‖divisorZeroIndex₀Val p‖ : ℝ)⁻¹) (z := τ) h4 ha)
    have : (1 : ℝ) ≤ (4 * R) ^ τ * ‖divisorZeroIndex₀Val p‖⁻¹ ^ τ := by
      simpa [hdiv] using this
    exact this
  have hgeom :
      (small.card : ℝ) ≤ (4 * R) ^ τ * (∑ p ∈ small, ‖divisorZeroIndex₀Val p‖⁻¹ ^ τ) := by
    simpa [Finset.mul_sum] using hgeom_sum
  have hsmall_le : (small.card : ℝ) ≤ (4 * R) ^ τ * Sτ := by
    exact hgeom.trans (mul_le_mul_of_nonneg_left hsum_le (by positivity))
  have hS_le : (4 * R) ^ τ * Sτ ≤ (4 * R) ^ τ * (Sτ + 1) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  have : (small.card : ℝ) ≤ (4 * R) ^ τ * (Sτ + 1) := hsmall_le.trans hS_le
  simpa [Sτ, add_comm, add_left_comm, add_assoc, mul_assoc] using this

lemma cartan_rpow_mul_le
    {τ R r : ℝ} (hRpos : 0 < R) (hrpos : 0 < r) (hR_le_r : R ≤ r) (hτ_nonneg : 0 ≤ τ) :
    (4 * R) ^ τ ≤ (4 : ℝ) ^ τ * (1 + r) ^ τ := by
  have hR_le_1r : R ≤ 1 + r := by linarith [hR_le_r, le_of_lt hrpos]
  have hbase0 : 0 ≤ (4 * R : ℝ) := by nlinarith [le_of_lt hRpos]
  have : (4 * R) ^ τ ≤ (4 * (1 + r)) ^ τ := by
    refine Real.rpow_le_rpow hbase0 ?_ hτ_nonneg
    nlinarith [hR_le_1r]
  have hmul : (4 * (1 + r)) ^ τ = (4 : ℝ) ^ τ * (1 + r) ^ τ := by
    have h4 : 0 ≤ (4 : ℝ) := by norm_num
    have h1 : 0 ≤ (1 + r : ℝ) := by positivity
    simpa [mul_assoc] using
      (Real.mul_rpow (x := (4 : ℝ)) (y := (1 + r : ℝ)) (z := τ) h4 h1)
  simpa [hmul] using this

open Classical in
theorem cartan_sum_majorant_le
    {f : ℂ → ℂ} {m : ℕ} {τ R r : ℝ}
    (hRpos : 0 < R)
    (hrpos : 0 < r)
    (hR_le_r : R ≤ r)
    (hτ_nonneg : 0 ≤ τ)
    (smallSet : Set (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
    (hsmall_fin : smallSet.Finite)
    (hsmallSet :
      smallSet = {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀Val p‖ ≤ 4 * R})
    (hsumτ :
      Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) => ‖divisorZeroIndex₀Val p‖⁻¹ ^ τ))
    (hr_phi :
      let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
      let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀Val p‖
      (∑ p ∈ small, CartanBound.φ (r / a p)) ≤ CartanBound.Cφ * (small.card : ℝ)) :
    let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
    letI : DecidableEq (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := Classical.decEq _
    let ap : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀Val p‖
    let b : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p =>
        if p ∈ small then
          CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
        else
          (2 : ℝ) * (r / ap p) ^ τ
    let Sτ : ℝ := ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), ‖divisorZeroIndex₀Val p‖⁻¹ ^ τ
    let Cprod : ℝ := cartanProductConstant m τ Sτ
    ∀ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)),
      (∑ p ∈ s, b p) ≤ Cprod * (1 + r) ^ τ := by
  classical
  intro small ap b Sτ Cprod s
  have hr : 0 ≤ r := le_of_lt hrpos
  have hSτ_nonneg : 0 ≤ Sτ :=
    tsum_nonneg (fun _ => Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _)
  have hsmall_mem : ∀ p, p ∈ small ↔ p ∈ smallSet := by
    intro p
    simp [small, hsmall_fin.mem_toFinset]
  have hphi_sum :
      (∑ p ∈ small, CartanBound.φ (r / ap p)) ≤ CartanBound.Cφ * (small.card : ℝ) := by
    simpa [small, ap] using hr_phi
  have hb_nonneg : ∀ p, 0 ≤ b p := by
    simpa [ap, b] using (cartan_majorant_nonneg (f := f) (m := m) (τ := τ) (r := r) hr small)
  have hb_summable : Summable b := by
    simpa [ap, b] using
      (cartan_majorant_summable (f := f) (m := m) (τ := τ) (r := r) hr small hsumτ)
  have hsmall_norm : ∀ p ∈ small, ‖divisorZeroIndex₀Val p‖ ≤ 4 * R := by
    intro p hp
    have : p ∈ smallSet := (hsmall_mem p).1 hp
    simpa [hsmallSet] using this
  have hcard_le : (small.card : ℝ) ≤ (4 * R) ^ τ * (Sτ + 1) := by
    simpa [Sτ, mul_assoc, add_assoc, add_left_comm, add_comm] using
      (cartan_card_small_le (f := f) (τ := τ) (R := R) hRpos hτ_nonneg small hsmall_norm hsumτ)
  have hpowR : (4 * R) ^ τ ≤ (4 : ℝ) ^ τ * (1 + r) ^ τ :=
    cartan_rpow_mul_le (τ := τ) (R := R) (r := r) hRpos hrpos hR_le_r hτ_nonneg
  have hcard_le' : (small.card : ℝ) ≤ (4 : ℝ) ^ τ * (1 + r) ^ τ * (Sτ + 1) := by
    have : (4 * R) ^ τ * (Sτ + 1) ≤ (4 : ℝ) ^ τ * (1 + r) ^ τ * (Sτ + 1) := by
      exact mul_le_mul_of_nonneg_right hpowR (by linarith [hSτ_nonneg])
    exact le_trans hcard_le this
  have hb_tsum_le :
      (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b p) ≤ Cprod * (1 + r) ^ τ := by
    let bφ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p => if p ∈ small then CartanBound.φ (r / ap p) else 0
    let b0 : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p => if p ∈ small then (m : ℝ) else 0
    let bmτ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p => if p ∈ small then (m : ℝ) * (r / ap p) ^ τ else 0
    let bt : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p => (2 : ℝ) * (r / ap p) ^ τ
    have hb_pointwise : ∀ p, b p ≤ bφ p + b0 p + bmτ p + bt p := by
      intro p
      by_cases hp : p ∈ small
      · have hbase : 0 ≤ r / ap p := div_nonneg hr (by positivity)
        have hx : 0 ≤ (r / ap p) ^ τ := Real.rpow_nonneg hbase τ
        have hpos : 0 ≤ (2 : ℝ) * (r / ap p) ^ τ := mul_nonneg (by norm_num) hx
        simp [b, bφ, b0, bmτ, bt, hp]
        nlinarith
      · simp [b, bφ, b0, bmτ, bt, hp]
    have hmaj_summ : Summable (fun p => bφ p + b0 p + bmτ p + bt p) := by
      have hbφ_summ : Summable bφ := by
        simpa [bφ] using summable_ite_mem_finset small (fun p => CartanBound.φ (r / ap p))
      have hb0_summ : Summable b0 := by
        simpa [b0] using summable_ite_mem_finset small (fun _ => (m : ℝ))
      have hbmτ_summ : Summable bmτ := by
        simpa [bmτ] using summable_ite_mem_finset small (fun p => (m : ℝ) * (r / ap p) ^ τ)
      have hbt_summ : Summable bt := by
        have hconst : Summable (fun p =>
            (2 : ℝ) * (r ^ τ) * (‖divisorZeroIndex₀Val p‖⁻¹ ^ τ)) :=
          hsumτ.mul_left ((2 : ℝ) * (r ^ τ))
        refine hconst.congr ?_
        intro p
        simp [bt, ap, rpow_div_norm_divisorZeroIndex₀_eq (f := f) (τ := τ) hr p,
          mul_assoc, mul_left_comm, mul_comm]
      have h' : Summable (fun p => bφ p + b0 p + (bmτ p + bt p)) :=
        (hbφ_summ.add hb0_summ).add (hbmτ_summ.add hbt_summ)
      simpa [add_assoc] using h'
    have htsum_le :
        (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b p)
          ≤ ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), (bφ p + b0 p + bmτ p + bt p) :=
      (hasSum_le hb_pointwise hb_summable.hasSum hmaj_summ.hasSum)
    have htsum_bφ :
        (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bφ p)
          = ∑ p ∈ small, CartanBound.φ (r / ap p) := by
      classical
      simpa [bφ] using tsum_ite_mem_finset small (fun p => CartanBound.φ (r / ap p))
    have htsum_b0 :
        (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b0 p)
          = (m : ℝ) * (small.card : ℝ) := by
      classical
      have : (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b0 p) = ∑ p ∈ small, (m : ℝ) := by
        simpa [b0] using tsum_ite_mem_finset small (fun _ => (m : ℝ))
      simp [this, Finset.sum_const, nsmul_eq_mul, mul_comm]
    have htsum_bmτ :
        (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bmτ p)
          = (m : ℝ) * ∑ p ∈ small, (r / ap p) ^ τ := by
      classical
      have :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bmτ p)
            = ∑ p ∈ small, (m : ℝ) * (r / ap p) ^ τ := by
        simpa [bmτ] using tsum_ite_mem_finset small (fun p => (m : ℝ) * (r / ap p) ^ τ)
      simp [this, Finset.mul_sum]
    have htsum_bt :
        (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bt p)
          ≤ (2 : ℝ) * (Sτ + 1) * (1 + r) ^ τ := by
      simpa [bt, ap, Sτ] using
        tsum_two_mul_rpow_div_norm_divisorZeroIndex₀_le (f := f) (τ := τ) hr hτ_nonneg
    have hsum_small_rpow_le :
        (∑ p ∈ small, (r / ap p) ^ τ) ≤ (Sτ + 1) * (1 + r) ^ τ := by
      simpa [ap, Sτ] using
        sum_rpow_div_norm_divisorZeroIndex₀_le (f := f) (τ := τ) small hr hτ_nonneg hsumτ
    have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    have hCφ : 0 ≤ CartanBound.Cφ := le_of_lt CartanBound.Cφ_pos
    have hS : 0 ≤ Sτ + 1 := by linarith [hSτ_nonneg]
    have htsum_majorant :
        (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), (bφ p + b0 p + bmτ p + bt p))
          ≤ (((CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 2) * (Sτ + 1))
              * (1 + r) ^ τ := by
      have hφ_le :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bφ p)
            ≤ CartanBound.Cφ * (small.card : ℝ) := by
        simpa [htsum_bφ] using hphi_sum
      have hb0_le :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b0 p)
            ≤ (m : ℝ) * (small.card : ℝ) := by
        simp [htsum_b0]
      have hbmτ_le :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bmτ p) ≤
            (m : ℝ) * (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ := by
        have h0 :
            (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bmτ p)
              ≤ (m : ℝ) * ((Sτ + 1) * (1 + r) ^ τ) := by
          have hmul := mul_le_mul_of_nonneg_left hsum_small_rpow_le hm0
                                                                    
          simpa [htsum_bmτ, mul_assoc, mul_left_comm, mul_comm] using hmul
        have h1 : (1 : ℝ) ≤ (4 : ℝ) ^ τ :=
          Real.one_le_rpow (by norm_num) hτ_nonneg
        have hscale :
            (m : ℝ) * ((Sτ + 1) * (1 + r) ^ τ)
              ≤ (m : ℝ) * (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ := by
          have hnonneg : 0 ≤ (m : ℝ) * ((Sτ + 1) * (1 + r) ^ τ) := by
            have : 0 ≤ (Sτ + 1) * (1 + r) ^ τ := by positivity
            exact mul_nonneg hm0 this
          simpa [mul_assoc, mul_left_comm, mul_comm] using (mul_le_mul_of_nonneg_right h1 hnonneg)
        exact h0.trans hscale
      have hbt_le :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bt p)
            ≤ (2 : ℝ) * (Sτ + 1) * (1 + r) ^ τ := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using htsum_bt
      have hsplit :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), (bφ p + b0 p + bmτ p + bt p))
            = (∑' p, bφ p) + (∑' p, b0 p) + (∑' p, bmτ p) + (∑' p, bt p) := by
        classical
        have hbφ_summ : Summable bφ := by
          simpa [bφ] using summable_ite_mem_finset small (fun p => CartanBound.φ (r / ap p))
        have hb0_summ : Summable b0 := by
          simpa [b0] using summable_ite_mem_finset small (fun _ => (m : ℝ))
        have hbmτ_summ : Summable bmτ := by
          simpa [bmτ] using summable_ite_mem_finset small (fun p => (m : ℝ) * (r / ap p) ^ τ)
        have hbt_summ : Summable bt := by
          have hconst :
              Summable
                (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
                  (2 : ℝ) * (r ^ τ) * ((‖divisorZeroIndex₀Val p‖⁻¹ : ℝ) ^ τ)) :=
            hsumτ.mul_left ((2 : ℝ) * (r ^ τ))
          refine hconst.congr ?_
          intro p
          simp [bt, ap, rpow_div_norm_divisorZeroIndex₀_eq (f := f) (τ := τ) hr p,
            mul_assoc, mul_left_comm, mul_comm]
        exact tsum_add_four bφ b0 bmτ bt hbφ_summ hb0_summ hbmτ_summ hbt_summ
      have hcard_le'' :
          (small.card : ℝ) ≤ (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hcard_le'
      have hφ_le' :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bφ p) ≤
            CartanBound.Cφ * (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ := by
        have : CartanBound.Cφ * (small.card : ℝ) ≤
            CartanBound.Cφ * ((4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ) :=
          mul_le_mul_of_nonneg_left hcard_le'' hCφ
        exact hφ_le.trans (by simpa [mul_assoc, mul_left_comm, mul_comm] using this)
      have hb0_le' :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b0 p) ≤
            (m : ℝ) * (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ := by
        have : (m : ℝ) * (small.card : ℝ) ≤ (m : ℝ) * ((4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ) :=
          mul_le_mul_of_nonneg_left hcard_le'' hm0
        exact hb0_le.trans (by simpa [mul_assoc, mul_left_comm, mul_comm] using this)
      have htsum_majorant' :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), (bφ p + b0 p + bmτ p + bt p))
            ≤ (CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ
              + (2 : ℝ) * (Sτ + 1) * (1 + r) ^ τ := by
        rw [hsplit]
        set Y : ℝ := Sτ + 1 with hY
        set T : ℝ := (1 + r) ^ τ with hT
        have hφ_leY :
            (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bφ p)
              ≤ CartanBound.Cφ * (4 : ℝ) ^ τ * Y * T := by
          simpa [hY, hT, mul_assoc] using hφ_le'
        have hb0_leY :
            (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b0 p)
              ≤ (m : ℝ) * (4 : ℝ) ^ τ * Y * T := by
          simpa [hY, hT, mul_assoc] using hb0_le'
        have hbmτ_leY :
            (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bmτ p)
              ≤ (m : ℝ) * (4 : ℝ) ^ τ * Y * T := by
          simpa [hY, hT, mul_assoc] using hbmτ_le
        have hbt_leY :
            (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bt p) ≤ (2 : ℝ) * Y * T := by
          simpa [hY, hT, mul_assoc] using hbt_le
        have hmain :=
          cartan_majorant_four_term_bound
            (q := (4 : ℝ) ^ τ) hφ_leY hb0_leY hbmτ_leY hbt_leY
        simpa [Y, T, add_assoc] using hmain
      have hring :
          (CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ
              + (2 : ℝ) * (Sτ + 1) * (1 + r) ^ τ
            = (((CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 2) * (Sτ + 1)) * (1 + r) ^ τ := by
        exact cartan_majorant_add_two_factor
          ((CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ) (Sτ + 1) ((1 + r) ^ τ)
      rw [← hring]
      exact htsum_majorant'
    have hCprod' :
        (((CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 2) * (Sτ + 1)) * (1 + r) ^ τ
          ≤ Cprod * (1 + r) ^ τ := by
      simpa [Cprod, cartanProductConstant, mul_assoc, mul_left_comm, mul_comm] using
        cartan_majorant_pad_two_to_three
          (A := (CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ)
          (S := Sτ) (T := (1 + r) ^ τ) hS (by positivity)
    exact (le_trans (le_trans htsum_le htsum_majorant) hCprod')
  have hsum_fin_le :
      (∑ p ∈ s, b p) ≤ (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b p) := by
    simpa using
      (Summable.sum_le_tsum (s := s) (f := b) (fun p _ => hb_nonneg p) hb_summable)
  exact hsum_fin_le.trans hb_tsum_le

end Complex.Hadamard
end
end HadamardSourceScope28

section HadamardSourceScope29

noncomputable section

open scoped BigOperators
open Filter Finset _root_.Real _root_.Erdos970.Real Topology

lemma Finset.prod_le_exp_sum {α : Type} (s : Finset α) (a : α → ℝ) (b : α → ℝ)
    (ha : ∀ x ∈ s, 0 ≤ a x) (hab : ∀ x ∈ s, a x ≤ Real.exp (b x)) :
    (∏ x ∈ s, a x) ≤ Real.exp (∑ x ∈ s, b x) := by
  calc
    (∏ x ∈ s, a x) ≤ ∏ x ∈ s, Real.exp (b x) := Finset.prod_le_prod₀ ha hab
    _ = Real.exp (∑ x ∈ s, b x) := by
      simpa using (Real.exp_sum (s := s) (f := b)).symm

lemma hasProd_le_of_prod_le_exp {α : Type} {f : α → ℝ} {a : ℝ}
    (hf : HasProd f a (SummationFilter.unconditional α))
    {B : ℝ} (hB : ∀ s : Finset α, (∏ x ∈ s, f x) ≤ Real.exp B) :
    a ≤ Real.exp B :=
  hasProd_le_of_prod_le (L := (SummationFilter.unconditional α)) hf hB

lemma hasProd_inv_unconditional {α : Type} {fac : α → ℂ} {F : ℂ}
    (hfac : HasProd fac F (SummationFilter.unconditional α)) (hF : F ≠ 0) :
    HasProd (fun x => (fac x)⁻¹) (F⁻¹) (SummationFilter.unconditional α) := by
  change
    Tendsto (fun s : Finset α => ∏ x ∈ s, (fac x)⁻¹)
      (SummationFilter.unconditional α).filter (𝓝 (F⁻¹))
  have hprod :
      Tendsto (fun s : Finset α => ∏ x ∈ s, fac x)
        (SummationFilter.unconditional α).filter (𝓝 F) := by
    simpa [HasProd] using hfac
  have hinv :
      Tendsto (fun s : Finset α => (∏ x ∈ s, fac x)⁻¹)
        (SummationFilter.unconditional α).filter (𝓝 (F⁻¹)) :=
    hprod.inv₀ hF
  refine hinv.congr' (Filter.Eventually.of_forall ?_)
  intro s
  simp [Finset.prod_inv_distrib]

lemma hasProd_norm_inv_unconditional {α : Type} {fac : α → ℂ} {F : ℂ}
    (hfac : HasProd fac F (SummationFilter.unconditional α)) (hF : F ≠ 0) :
    HasProd (fun x => ‖(fac x)⁻¹‖) ‖F⁻¹‖ (SummationFilter.unconditional α) := by
  change
    Tendsto (fun s : Finset α => ∏ x ∈ s, ‖(fac x)⁻¹‖)
      (SummationFilter.unconditional α).filter (𝓝 ‖F⁻¹‖)
  have hnorm := (hasProd_inv_unconditional hfac hF).norm
  refine hnorm.congr' (Filter.Eventually.of_forall ?_)
  intro s
  simp [norm_inv, Finset.prod_inv_distrib]

lemma hasProd_norm_inv_le_exp_of_pointwise_le_exp {α : Type} {fac : α → ℂ} {F : ℂ}
    (hfac : HasProd fac F (SummationFilter.unconditional α))
    (b : α → ℝ) (B : ℝ)
    (hterm : ∀ x, ‖(fac x)⁻¹‖ ≤ Real.exp (b x))
    (hsum : ∀ s : Finset α, (∑ x ∈ s, b x) ≤ B) :
    ‖F⁻¹‖ ≤ Real.exp B := by
  by_cases hF : F = 0
  · subst hF
    simpa using exp_nonneg B
  have hnorm :
      HasProd (fun x => ‖(fac x)⁻¹‖) ‖F⁻¹‖ (SummationFilter.unconditional α) :=
    hasProd_norm_inv_unconditional hfac hF
  have hprod : ∀ s : Finset α, (∏ x ∈ s, ‖(fac x)⁻¹‖) ≤ Real.exp B := by
    intro s
    have h0 : ∀ x ∈ s, 0 ≤ ‖(fac x)⁻¹‖ := by intro _ _; positivity
    have h1 : (∏ x ∈ s, ‖(fac x)⁻¹‖) ≤ Real.exp (∑ x ∈ s, b x) := by
      refine Finset.prod_le_exp_sum s (a := fun x => ‖(fac x)⁻¹‖) (b := b) h0 ?_
      intro x hx
      simpa using hterm x
    have h2 : Real.exp (∑ x ∈ s, b x) ≤ Real.exp B :=
      Real.exp_le_exp.2 (hsum s)
    exact h1.trans h2
  exact hasProd_le_of_prod_le_exp hnorm hprod
end
end HadamardSourceScope29

section HadamardSourceScope30

open Metric

namespace Complex

open _root_.Complex

theorem borelCaratheodory_zero_closedBall {f : ℂ → ℂ} {M r R : ℝ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    (hr : 0 < r) (hlt : r < R) (hM : 0 < M) (hf0 : f 0 = 0)
    (hf_re : ∀ w, ‖w‖ ≤ R → (f w).re ≤ M) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖f z‖ ≤ 2 * M * r / (R - r) := by
  have hR : 0 < R := lt_trans hr hlt
  have hz_ball : z ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hz.trans_lt hlt
  have hf_diff : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R) := by
    intro w hw
    have hw' : w ∈ Metric.closedBall (0 : ℂ) R := ball_subset_closedBall hw
    exact (hf w hw').differentiableAt.differentiableWithinAt
  have hf_map : Set.MapsTo f (Metric.ball (0 : ℂ) R) {w | w.re ≤ M} := by
    intro w hw
    simp only [Set.mem_ofPred_eq]
    have hw' : ‖w‖ < R := by simpa [Metric.mem_ball, dist_zero_right] using hw
    exact hf_re w hw'.le
  have hbc :=
    borelCaratheodory_zero hM hf_diff hf_map hR hz_ball hf0
  have hzR : ‖z‖ < R := by
    rw [Metric.mem_ball, dist_zero_right] at hz_ball
    exact hz_ball
  have hmono : ‖z‖ / (R - ‖z‖) ≤ r / (R - r) := by
    have hrden : 0 < R - r := sub_pos.mpr hlt
    have hden : 0 < R - ‖z‖ := sub_pos.mpr hzR
    rw [div_le_div_iff₀ hden hrden]
    nlinarith [hz, norm_nonneg z]
  have hM' : 0 ≤ 2 * M := mul_nonneg (by norm_num) (le_of_lt hM)
  calc ‖f z‖
      ≤ 2 * M * ‖z‖ / (R - ‖z‖) := hbc
    _ ≤ 2 * M * (r / (R - r)) := by
        simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left hmono hM'
    _ = 2 * M * r / (R - r) := by ring

end Complex
end HadamardSourceScope30

section HadamardSourceScope31

noncomputable section

namespace Complex

open _root_.Complex
namespace Hadamard

open _root_.Complex _root_.Erdos970.Complex _root_.Real _root_.Erdos970.Real
  BigOperators _root_.Finset Set Filter Topology Metric

open scoped Topology

theorem zero_free_polynomial_growth_is_exp_poly {H : ℂ → ℂ} {n : ℕ}
    (hH : Differentiable ℂ H)
    (h_nonzero : ∀ z, H z ≠ 0)
    (h_bound : ∃ C > 0, ∀ z, ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ n)) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ n ∧ ∀ z, H z = Complex.exp (Polynomial.eval z P) := by
  classical
  rcases h_bound with ⟨C, hCpos, hC⟩
  let L : ℂ → ℂ := fun z => deriv H z / H z
  have hderivH : Differentiable ℂ (deriv H) := by
    intro z
    exact ((hH.analyticAt z).deriv).differentiableAt
  have hL : Differentiable ℂ L := by
    simpa [L] using! (hderivH.div hH h_nonzero)
  let h : ℂ → ℂ := fun z => Complex.wedgeIntegral (0 : ℂ) z L
  have hh_deriv : ∀ z, HasDerivAt h (L z) z := by
    intro z
    let r : ℝ := ‖z‖ + 1
    have hrpos : 0 < r := by
      dsimp [r]; linarith [norm_nonneg z]
    have hz_ball : z ∈ Metric.ball (0 : ℂ) r := by
      have : dist z (0 : ℂ) < r := by simp [r, dist_zero_right]
      simpa [Metric.mem_ball] using this
    have hconserv : Complex.IsConservativeOn L (Metric.ball (0 : ℂ) r) :=
      (hL.differentiableOn).isConservativeOn
    have hcont : ContinuousOn L (Metric.ball (0 : ℂ) r) :=
      hL.continuous.continuousOn
    simpa [h, r] using hconserv.hasDerivAt_wedgeIntegral (f_cont := hcont) (hz := hz_ball)
  have hh : Differentiable ℂ h := fun z => (hh_deriv z).differentiableAt
  have hderiv_h : ∀ z, deriv h z = L z := fun z => (hh_deriv z).deriv
  let k : ℂ → ℂ := fun z => h z + Complex.log (H 0)
  have hk : Differentiable ℂ k := hh.add_const (Complex.log (H 0))
  have hk_exp : ∀ z, H z = Complex.exp (k z) := by
    let F : ℂ → ℂ := fun z => Complex.exp (k z) / H z
    have hF_deriv : ∀ z, deriv F z = 0 := by
      intro z
      have hH_has : HasDerivAt H (deriv H z) z := (hH z).hasDerivAt
      have hk_has : HasDerivAt k (L z) z := by
        have hh_has : HasDerivAt h (L z) z := hh_deriv z
        simpa [k, L] using hh_has.add_const (Complex.log (H 0))
      have hExp : HasDerivAt (fun w => Complex.exp (k w)) (Complex.exp (k z) * L z) z :=
        (HasDerivAt.cexp hk_has)
      have hDiv := (HasDerivAt.div hExp hH_has (h_nonzero z))
      have :
          deriv F z =
            ((Complex.exp (k z) * L z) * H z - Complex.exp (k z) * deriv H z) / (H z) ^ 2 := by
        simpa [F] using! hDiv.deriv
      rw [this]
      have hnum :
          (Complex.exp (k z) * L z) * H z - Complex.exp (k z) * deriv H z = 0 := by
        dsimp [L]
        field_simp [h_nonzero z]
        ring
      simp [hnum]
    have hF_diff : Differentiable ℂ F := (hk.cexp).div hH h_nonzero
    have hF_const : ∀ z, F z = F 0 := by
      intro z
      exact is_const_of_deriv_eq_zero hF_diff hF_deriv z 0
    have hF0 : F 0 = 1 := by
      have hh0 : h 0 = 0 := by simp [h, Complex.wedgeIntegral]
      have hk0 : k 0 = Complex.log (H 0) := by simp [k, hh0]
      have hH0 : H 0 ≠ 0 := h_nonzero 0
      simp [F, hk0, Complex.exp_log hH0, hH0]
    intro z
    have : F z = 1 := by simpa [hF0] using (hF_const z)
    have hHz : H z ≠ 0 := h_nonzero z
    have : Complex.exp (k z) / H z = 1 := by simpa [F] using this
    have : Complex.exp (k z) = H z := by
      field_simp [hHz] at this
      simpa using this
    exact this.symm
  have hk_re_bound : ∀ z, (k z).re ≤ C * (1 + ‖z‖) ^ n := by
    intro z
    have hHz : H z ≠ 0 := h_nonzero z
    have hpos : 0 < ‖H z‖ := norm_pos_iff.mpr hHz
    have hlog_le : Real.log ‖H z‖ ≤ C * (1 + ‖z‖) ^ n := by
      have := Real.log_le_log hpos (hC z)
      simpa [Real.log_exp] using this
    have hlog_eq : Real.log ‖H z‖ = (k z).re := by
      have : ‖H z‖ = Real.exp (k z).re := by
        simpa [hk_exp z] using (Complex.norm_exp (k z))
      calc
        Real.log ‖H z‖ = Real.log (Real.exp (k z).re) := by simp [this]
        _ = (k z).re := by simp
    simpa [hlog_eq] using hlog_le
  have hk_iteratedDeriv_eq_zero : ∀ m : ℕ, n < m → iteratedDeriv m k 0 = 0 := by
    intro m hm
    have hm' : 0 < (m - n : ℕ) := Nat.sub_pos_of_lt hm
    have hmne : m - n ≠ 0 := (Nat.pos_iff_ne_zero.1 hm')
    let f : ℂ → ℂ := fun z => k z - k 0
    have hf : Differentiable ℂ f := hk.sub_const (k 0)
    have hf0 : f 0 = 0 := by simp [f]
    have hf_re_bound : ∀ R : ℝ, 0 < R →
        ∀ z, ‖z‖ ≤ R → (f z).re ≤ C * (1 + R) ^ n + ‖k 0‖ := by
      intro R hRpos z hzR
      have hkz : (k z).re ≤ C * (1 + ‖z‖) ^ n := hk_re_bound z
      have hkz' : (k z).re ≤ C * (1 + R) ^ n := by
        have h1 : (1 + ‖z‖ : ℝ) ≤ 1 + R := by linarith
        have hpow : (1 + ‖z‖ : ℝ) ^ n ≤ (1 + R) ^ n :=
          pow_le_pow_left₀ (by linarith [norm_nonneg z]) h1 n
        exact hkz.trans (mul_le_mul_of_nonneg_left hpow (le_of_lt hCpos))
      have hRe0 : -(k 0).re ≤ ‖k 0‖ := by
        have habs : |(k 0).re| ≤ ‖k 0‖ := Complex.abs_re_le_norm (k 0)
        have hneg : -(k 0).re ≤ |(k 0).re| := by simpa using (neg_le_abs (k 0).re)
        exact hneg.trans habs
      have : (f z).re ≤ C * (1 + R) ^ n + ‖k 0‖ := by
        have : (f z).re = (k z).re - (k 0).re := by simp [f, sub_eq_add_neg]
        nlinarith [this, hkz', hRe0]
      exact this
    have hf_bound_on_ball : ∀ R : ℝ, 0 < R →
        ∀ z, ‖z‖ ≤ R / 2 → ‖f z‖ ≤ 2 * (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
      intro R hRpos z hz
      have hR2pos : 0 < R / 2 := by nlinarith
      have hlt : R / 2 < R := by nlinarith
      have hMpos : 0 < (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
        have : 0 ≤ C * (1 + R) ^ n := by
          refine mul_nonneg (le_of_lt hCpos) ?_
          exact pow_nonneg (by linarith) _
        nlinarith [this, norm_nonneg (k 0)]
      have hf_anal : AnalyticOnNhd ℂ f (Metric.closedBall 0 R) := by
        intro w _hw
        exact (hf.analyticAt w)
      have hf_re : ∀ w, ‖w‖ ≤ R → (f w).re ≤ (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
        intro w hw
        have := hf_re_bound R hRpos w hw
        linarith
      have hf_bc :=
        borelCaratheodory_zero_closedBall (f := f) (r := R / 2) (R := R)
          (M := (C * (1 + R) ^ n + ‖k 0‖ + 1))
          hf_anal hR2pos hlt hMpos hf0 hf_re (z := z) hz
      have hconst :
          2 * (C * (1 + R) ^ n + ‖k 0‖ + 1) * (R / 2) / (R - R / 2)
            = 2 * (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
        field_simp [hRpos.ne'] ; ring
      simpa [hconst] using hf_bc
    have hCauchy : ∀ R : ℝ, 0 < R →
        ‖iteratedDeriv m f 0‖ ≤
          (m.factorial : ℝ) * (2 * (C * (1 + R) ^ n + ‖k 0‖ + 1)) / (R / 2) ^ m := by
      intro R hRpos
      have hR2pos : 0 < R / 2 := by nlinarith
      have hf_diffCont : DiffContOnCl ℂ f (Metric.ball (0 : ℂ) (R / 2)) := hf.diffContOnCl
      have hbound_sphere :
          ∀ z ∈ Metric.sphere (0 : ℂ) (R / 2),
            ‖f z‖ ≤ 2 * (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
        intro z hz
        have hz' : ‖z‖ ≤ R / 2 := by
          simpa [Metric.mem_sphere, dist_zero_right] using (le_of_eq hz)
        exact hf_bound_on_ball R hRpos z hz'
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (n := m) (c := (0 : ℂ))
          (R := R / 2) (C := 2 * (C * (1 + R) ^ n + ‖k 0‖ + 1))
          (hR := hR2pos) hf_diffCont hbound_sphere)
    have hf_iter_eq : iteratedDeriv m f 0 = 0 := by
      by_contra hne
      have ha : 0 < ‖iteratedDeriv m f 0‖ := norm_pos_iff.2 hne
      let RHS : ℝ → ℝ := fun R =>
        (m.factorial : ℝ) * (2 * (C * (1 + R) ^ n + ‖k 0‖ + 1)) / (R / 2) ^ m
      have hle_RHS : ∀ R : ℝ, 0 < R → ‖iteratedDeriv m f 0‖ ≤ RHS R := by
        intro R hRpos
        simpa [RHS] using hCauchy R hRpos
      have hRHS_tendsto : Tendsto RHS atTop (𝓝 0) := by
        let K : ℝ := ‖k 0‖ + 1
        have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le n) hm
        have hm0 : m ≠ 0 := ne_of_gt hmpos
        have hratio : Tendsto (fun R : ℝ => R ^ n / (R / 2) ^ m) atTop (𝓝 0) := by
          have hident :
              (fun R : ℝ => R ^ n / (R / 2) ^ m) = fun R : ℝ => (2 : ℝ) ^ m * (R ^ n / R ^ m) := by
            funext R
            simp [div_eq_mul_inv, mul_pow, mul_assoc, mul_comm]
          have hmain : Tendsto (fun R : ℝ => R ^ n / R ^ m) atTop (𝓝 0) := by
            have hp : m - n ≠ 0 := (Nat.pos_iff_ne_zero.1 (Nat.sub_pos_of_lt hm))
            have hmain' : Tendsto (fun R : ℝ => (R ^ (m - n))⁻¹) atTop (𝓝 0) := by
              simpa using (tendsto_pow_neg_atTop (𝕜 := ℝ) (n := m - n) hp)
            have hEq : (fun R : ℝ => (R ^ (m - n))⁻¹) =ᶠ[atTop] fun R : ℝ => R ^ n / R ^ m := by
              have hEq' : (fun R : ℝ => R ^ n / R ^ m) =ᶠ[atTop] fun R : ℝ => (R ^ (m - n))⁻¹ := by
                filter_upwards [eventually_ne_atTop (0 : ℝ)] with R hR
                have hle : n ≤ m := le_of_lt hm
                have hm_eq : n + (m - n) = m := Nat.add_sub_of_le hle
                have hn0 : R ^ n ≠ 0 := pow_ne_zero n hR
                calc
                  R ^ n / R ^ m = R ^ n / R ^ (n + (m - n)) := by simp [hm_eq]
                  _ = R ^ n * ((R ^ (m - n))⁻¹ * (R ^ n)⁻¹) := by
                        simp [pow_add, div_eq_mul_inv, mul_comm]
                  _ = (R ^ (m - n))⁻¹ := by
                        ring_nf
                        simp [hn0]
              exact hEq'.symm
            exact Filter.Tendsto.congr' hEq hmain'
          have : Tendsto (fun R : ℝ => (2 : ℝ) ^ m * (R ^ n / R ^ m)) atTop (𝓝 ((2 : ℝ) ^ m * 0)) :=
            tendsto_const_nhds.mul hmain
          simpa [hident] using this
        have hinv : Tendsto (fun R : ℝ => ((R / 2) ^ m)⁻¹) atTop (𝓝 0) := by
          have hdiv : Tendsto (fun R : ℝ => R / 2) atTop atTop :=
            (tendsto_id.atTop_div_const (r := (2 : ℝ)) (by norm_num : (0 : ℝ) < 2))
          have hpow : Tendsto (fun R : ℝ => (R / 2) ^ m) atTop atTop :=
            (Filter.tendsto_pow_atTop (α := ℝ) (n := m) hm0).comp hdiv
          simpa using! hpow.inv_tendsto_atTop
        have hdiv : Tendsto (fun R : ℝ => (1 + R) / R) atTop (𝓝 (1 : ℝ)) := by
          have hinv' : Tendsto (fun R : ℝ => (R : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero
          have hadd : Tendsto (fun R : ℝ => (1 : ℝ) + (R : ℝ)⁻¹) atTop (𝓝 (1 : ℝ)) := by
            simpa using (tendsto_const_nhds.add hinv')
          have hEq : (fun R : ℝ => (1 + R) / R) =ᶠ[atTop] fun R : ℝ => (1 : ℝ) + (R : ℝ)⁻¹ := by
            filter_upwards [eventually_ne_atTop (0 : ℝ)] with R hR
            field_simp [hR]; ring
          exact Filter.Tendsto.congr' hEq.symm hadd
        have hdiv_pow : Tendsto (fun R : ℝ => ((1 + R) / R) ^ n) atTop (𝓝 (1 : ℝ)) := by
          simpa using (hdiv.pow n)
        have hone_add_ratio :
            Tendsto (fun R : ℝ => (1 + R) ^ n / (R / 2) ^ m) atTop (𝓝 (0 : ℝ)) := by
          have hEq :
              (fun R : ℝ => (1 + R) ^ n / (R / 2) ^ m)
                =ᶠ[atTop] fun R : ℝ => ((1 + R) / R) ^ n * (R ^ n / (R / 2) ^ m) := by
            filter_upwards [eventually_ne_atTop (0 : ℝ)] with R hR
            have hRpow : (R ^ n : ℝ) ≠ 0 := pow_ne_zero n hR
            have hident :
                ((1 + R) / R) ^ n * (R ^ n / (R / 2) ^ m) = (1 + R) ^ n / (R / 2) ^ m := by
              calc
                ((1 + R) / R) ^ n * (R ^ n / (R / 2) ^ m)
                    = ((1 + R) ^ n / R ^ n) * (R ^ n / (R / 2) ^ m) := by
                        simp [div_pow]
                _ = ((1 + R) ^ n * R ^ n) / (R ^ n * (R / 2) ^ m) := by
                        simp [div_mul_div_comm, mul_comm]
                _ = ((1 + R) ^ n * R ^ n) / ((R / 2) ^ m * R ^ n) := by
                        simp [mul_comm]
                _ = (1 + R) ^ n / (R / 2) ^ m := by
                        simpa [mul_assoc, mul_comm, mul_left_comm] using
                          (mul_div_mul_right (a := (1 + R) ^ n) (b := (R / 2) ^ m) hRpow)
            exact hident.symm
          have hmul :
              Tendsto
                (fun R : ℝ => ((1 + R) / R) ^ n * (R ^ n / (R / 2) ^ m))
                atTop (𝓝 (0 : ℝ)) := by
            simpa [mul_zero] using (hdiv_pow.mul hratio)
          exact Filter.Tendsto.congr' hEq.symm hmul
        have h1 : Tendsto (fun R : ℝ => C * ((1 + R) ^ n / (R / 2) ^ m)) atTop (𝓝 0) := by
          simpa using (tendsto_const_nhds.mul hone_add_ratio)
        have h2 : Tendsto (fun R : ℝ => K * ((R / 2) ^ m)⁻¹) atTop (𝓝 0) := by
          simpa using (tendsto_const_nhds.mul hinv)
        have hsum :
            Tendsto
              (fun R : ℝ => C * ((1 + R) ^ n / (R / 2) ^ m) + K * ((R / 2) ^ m)⁻¹)
              atTop (𝓝 0) := by
          simpa using (h1.add h2)
        have hrew :
            (fun R : ℝ => (C * (1 + R) ^ n + K) / (R / 2) ^ m)
              = fun R : ℝ => C * ((1 + R) ^ n / (R / 2) ^ m) + K * ((R / 2) ^ m)⁻¹ := by
          funext R
          simp [div_eq_mul_inv, mul_add, mul_assoc, mul_comm]
        have hbase : Tendsto (fun R : ℝ => (C * (1 + R) ^ n + K) / (R / 2) ^ m) atTop (𝓝 0) := by
          simpa [hrew] using hsum
        have hconst :
            Tendsto (fun _ : ℝ => (m.factorial : ℝ) * (2 : ℝ)) atTop
              (𝓝 ((m.factorial : ℝ) * (2 : ℝ))) := tendsto_const_nhds
        have hmul : Tendsto (fun R : ℝ => ((m.factorial : ℝ) * (2 : ℝ)) *
              ((C * (1 + R) ^ n + K) / (R / 2) ^ m)) atTop (𝓝 0) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using (hconst.mul hbase)
        have hRHS_rw : RHS = fun R : ℝ => ((m.factorial : ℝ) * (2 : ℝ)) *
              ((C * (1 + R) ^ n + K) / (R / 2) ^ m) := by
          funext R
          dsimp [RHS, K]
          ring_nf
        simpa [hRHS_rw] using hmul
      have hsmall : ∀ᶠ R in atTop, RHS R < ‖iteratedDeriv m f 0‖ / 2 :=
        (tendsto_order.1 hRHS_tendsto).2 _ (half_pos ha)
      have hle_eventually : ∀ᶠ R in atTop, ‖iteratedDeriv m f 0‖ ≤ RHS R := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hRpos
        exact hle_RHS R hRpos
      rcases (hle_eventually.and hsmall).exists with ⟨R, hle, hlt⟩
      have : ‖iteratedDeriv m f 0‖ < ‖iteratedDeriv m f 0‖ :=
        (lt_of_le_of_lt hle hlt).trans (half_lt_self ha)
      exact lt_irrefl _ this
    have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le n) hm
    have hm0 : m ≠ 0 := ne_of_gt hmpos
    have hkcd : ContDiffAt ℂ (↑m) k (0 : ℂ) := (hk.analyticAt 0).contDiffAt
    have hccd : ContDiffAt ℂ (↑m) (fun _ : ℂ => k 0) (0 : ℂ) := contDiffAt_const
    have hsub :
        iteratedDeriv m f 0 =
          iteratedDeriv m k 0 - iteratedDeriv m (fun _ : ℂ => k 0) 0 := by
      simpa [f] using! (iteratedDeriv_sub (n := m) (x := (0 : ℂ)) hkcd hccd)
    have hconst0 : iteratedDeriv m (fun _ : ℂ => k 0) 0 = 0 := by
      simp [iteratedDeriv_const, hm0]
    have hf_eq : iteratedDeriv m f 0 = iteratedDeriv m k 0 := by
      simp [hsub, hconst0]
    simpa [hf_eq] using hf_iter_eq
  let P : Polynomial ℂ :=
    ∑ m ∈ Finset.range (n + 1), Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)
  have hPdeg : P.natDegree ≤ n := by
    have hnat :
        P.natDegree ≤
          Finset.fold max 0
            (fun m : ℕ =>
              (Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)).natDegree)
            (Finset.range (n + 1)) := by
      simpa [P, Function.comp] using
        (Polynomial.natDegree_sum_le (s := Finset.range (n + 1))
          (f := fun m : ℕ =>
            Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)))
    have hfold :
        Finset.fold max 0
            (fun m : ℕ =>
              (Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)).natDegree)
            (Finset.range (n + 1)) ≤ n := by
      refine (Finset.fold_max_le (f := fun m : ℕ =>
        (Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)).natDegree)
        (b := 0) (s := Finset.range (n + 1)) (c := n)).2 ?_
      refine ⟨Nat.zero_le n, ?_⟩
      intro m hm
      have hmon :
          (Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)).natDegree ≤ m :=
        Polynomial.natDegree_monomial_le _
      have hm_le : m ≤ n := Nat.le_of_lt_succ (Finset.mem_range.1 hm)
      exact hmon.trans hm_le
    exact hnat.trans hfold
  have hk_poly : ∀ z, k z = Polynomial.eval z P := by
    intro z
    have htaylor := Complex.taylorSeries_eq_of_entire' (c := (0 : ℂ)) (z := z) hk
    have htail : ∀ m : ℕ, m ∉ Finset.range (n + 1) →
        ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * (z - 0) ^ m) = 0 := by
      intro m hm'
      have hmgt : n < m := by
        have : n + 1 ≤ m := Nat.le_of_not_lt (by simpa [Finset.mem_range] using hm')
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self n) this
      have hz : iteratedDeriv m k 0 = 0 := hk_iteratedDeriv_eq_zero m hmgt
      simp [hz]
    have htsum :
        (∑' m : ℕ, (m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * (z - 0) ^ m)
          = ∑ m ∈ Finset.range (n + 1), (m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * z ^ m := by
      simpa [sub_zero] using (tsum_eq_sum (s := Finset.range (n + 1)) htail)
    have hfinite :
        k z = ∑ m ∈ Finset.range (n + 1), (m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * z ^ m := by
      calc
        k z = ∑' m : ℕ, (m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * (z - 0) ^ m := by
          simpa using htaylor.symm
        _ = _ := htsum
    have hEval :
        Polynomial.eval z P =
          ∑ m ∈ Finset.range (n + 1), z ^ m * ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0) := by
      classical
      change Polynomial.eval₂ (RingHom.id ℂ) z P = _
      let φ : Polynomial ℂ →+* ℂ := Polynomial.eval₂RingHom (RingHom.id ℂ) z
      change φ P = _
      simp [P, φ, Polynomial.eval₂_monomial, mul_comm]
    have hfinite' :
        k z = ∑ m ∈ Finset.range (n + 1), z ^ m * ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hfinite
    simpa [hEval] using hfinite'
  refine ⟨P, hPdeg, ?_⟩
  intro z
  have : H z = Complex.exp (k z) := by simp [hk_exp z]
  simp [this, hk_poly z]

end Hadamard
end Complex
end
end HadamardSourceScope31

section HadamardSourceScope32

noncomputable section

namespace Complex

open _root_.Complex
namespace Hadamard

open _root_.Complex _root_.Erdos970.Complex _root_.Real _root_.Erdos970.Real
  BigOperators _root_.Finset Set Filter Topology Metric

open scoped Topology

open Polynomial

private lemma exists_pow_eq_complex {n : ℕ} (hn : 0 < n) (w : ℂ) : ∃ z : ℂ, z ^ n = w := by
  classical
  by_cases hw : w = 0
  · subst hw
    refine ⟨0, ?_⟩
    have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    simp [hn0]
  · refine ⟨Complex.exp (Complex.log w / n), ?_⟩
    have hn0 : (n : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn)
    calc
      (Complex.exp (Complex.log w / n)) ^ n
          = Complex.exp ((n : ℂ) * (Complex.log w / n)) := by
              simpa using (Complex.exp_nat_mul (Complex.log w / n) n).symm
      _ = Complex.exp (Complex.log w) := by
            have : (n : ℂ) * (Complex.log w / n) = Complex.log w := by
              field_simp [hn0]
            simp [this]
      _ = w := by simpa using (Complex.exp_log hw)

private lemma mul_conj_div_norm (a : ℂ) (ha : a ≠ 0) :
    a * ((starRingEnd ℂ) a / (‖a‖ : ℂ)) = (‖a‖ : ℂ) := by
  have hnorm_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hnorm_ne : (‖a‖ : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hnorm_pos)
  have hmul : a * (starRingEnd ℂ) a = (Complex.normSq a : ℂ) :=
    Complex.mul_conj a
  have hcast : (Complex.normSq a : ℂ) = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    exact_mod_cast (Complex.normSq_eq_norm_sq a)
  have hdiv : ((‖a‖ ^ 2 : ℝ) : ℂ) / (‖a‖ : ℂ) = (‖a‖ : ℂ) := by
    have : ((‖a‖ ^ 2 : ℝ) : ℂ) = (‖a‖ : ℂ) * (‖a‖ : ℂ) := by
      simp [pow_two]
    calc
      ((‖a‖ ^ 2 : ℝ) : ℂ) / (‖a‖ : ℂ)
          = ((‖a‖ : ℂ) * (‖a‖ : ℂ)) / (‖a‖ : ℂ) := by simp [this]
      _ = (‖a‖ : ℂ) := by
            field_simp [hnorm_ne]
  calc
    a * ((starRingEnd ℂ) a / (‖a‖ : ℂ))
        = (a * (starRingEnd ℂ) a) / (‖a‖ : ℂ) := by
            simp [div_eq_mul_inv, mul_assoc]
    _ = (Complex.normSq a : ℂ) / (‖a‖ : ℂ) := by simp [hmul]
    _ = ((‖a‖ ^ 2 : ℝ) : ℂ) / (‖a‖ : ℂ) := by simp [hcast]
    _ = (‖a‖ : ℂ) := hdiv

private lemma exists_z_norm_eq_re_eval_ge
    (P : Polynomial ℂ) (hn : 0 < P.natDegree) :
    ∃ R0 : ℝ, 0 < R0 ∧
      ∀ R : ℝ, R0 ≤ R →
        ∃ z : ℂ, ‖z‖ = R ∧
          (‖P.leadingCoeff‖ / 2) * R ^ P.natDegree ≤ (P.eval z).re := by
  classical
  set n : ℕ := P.natDegree
  have hn0 : 0 < n := hn
  have hP0 : P ≠ 0 := by
    intro h0
    simp [n, h0] at hn0
  have hLC : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP0
  set a : ℂ := P.leadingCoeff
  have ha : a ≠ 0 := hLC
  have hnorm_a_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  set wtarget : ℂ := (starRingEnd ℂ) a / (‖a‖ : ℂ)
  have hwtarget_norm : ‖wtarget‖ = (1 : ℝ) := by
    calc
      ‖wtarget‖ = ‖(starRingEnd ℂ) a‖ / ‖(‖a‖ : ℂ)‖ := by
        simp [wtarget]
      _ = ‖a‖ / ‖a‖ := by simp
      _ = (1 : ℝ) := by
        field_simp [hnorm_a_pos.ne']
  rcases exists_pow_eq_complex (n := n) hn0 (w := wtarget) with ⟨w, hw⟩
  have hw_norm : ‖w‖ = (1 : ℝ) := by
    have hpow : (‖w‖ : ℝ) ^ n = 1 := by
      have := congrArg (fun z : ℂ => ‖z‖) hw
      simpa [norm_pow, hwtarget_norm] using this
    have hn0' : n ≠ 0 := Nat.ne_of_gt hn0
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg w) hn0').1 hpow
  set S : ℝ := ∑ i ∈ Finset.range n, ‖P.coeff i‖
  set R0 : ℝ := max 1 (2 * S / ‖a‖)
  refine ⟨R0, ?_, ?_⟩
  · have : (0 : ℝ) < (1 : ℝ) := by norm_num
    exact lt_of_lt_of_le this (le_max_left _ _)
  · intro R hR
    have hR_ge1 : (1 : ℝ) ≤ R := by
      exact le_trans (le_max_left _ _) hR
    have hR_nonneg : 0 ≤ R := le_trans (by norm_num) hR_ge1
    set z : ℂ := (R : ℂ) * w
    have hz_norm : ‖z‖ = R := by
      have : ‖z‖ = |R| * ‖w‖ := by
        simp [z]
      simp [this, hw_norm, abs_of_nonneg hR_nonneg]
    have h_eval : P.eval z =
        (∑ i ∈ Finset.range n, P.coeff i * z ^ i) + P.coeff n * z ^ n := by
      have hsum : P.eval z = ∑ i ∈ Finset.range (n + 1), P.coeff i * z ^ i := by
        have : P.natDegree + 1 = n + 1 := by simp [n]
        simpa [this] using (Polynomial.eval_eq_sum_range (p := P) z)
      have hsplit :
          (∑ i ∈ Finset.range (n + 1), P.coeff i * z ^ i)
            = (∑ i ∈ Finset.range n, P.coeff i * z ^ i) + P.coeff n * z ^ n := by
        simpa using (Finset.sum_range_succ (f := fun i => P.coeff i * z ^ i) n)
      exact hsum.trans hsplit
    have h_lower_norm :
        ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ ≤ S * R ^ (n - 1) := by
      have h1 :
          ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖
            ≤ ∑ i ∈ Finset.range n, ‖P.coeff i * z ^ i‖ := by
        simpa using (norm_sum_le (Finset.range n) (fun i => P.coeff i * z ^ i))
      have hterm : ∀ i ∈ Finset.range n, ‖P.coeff i * z ^ i‖ ≤ ‖P.coeff i‖ * R ^ (n - 1) := by
        intro i hi
        have hi_lt : i < n := Finset.mem_range.mp hi
        have hi_le : i ≤ n - 1 := Nat.le_pred_of_lt hi_lt
        have hzpow : ‖z‖ ^ i ≤ R ^ (n - 1) := by
          have hmono : ‖z‖ ^ i ≤ ‖z‖ ^ (n - 1) :=
            pow_le_pow_right₀ (by simpa [hz_norm] using hR_ge1) hi_le
          simpa [hz_norm] using hmono
        calc
          ‖P.coeff i * z ^ i‖ = ‖P.coeff i‖ * ‖z‖ ^ i := by
            simp [norm_pow]
          _ ≤ ‖P.coeff i‖ * R ^ (n - 1) := by
            exact mul_le_mul_of_nonneg_left hzpow (norm_nonneg _)
      have h2 :
          ∑ i ∈ Finset.range n, ‖P.coeff i * z ^ i‖
            ≤ ∑ i ∈ Finset.range n, ‖P.coeff i‖ * R ^ (n - 1) := by
        exact Finset.sum_le_sum (fun i hi => hterm i hi)
      have h3 :
          (∑ i ∈ Finset.range n, ‖P.coeff i‖ * R ^ (n - 1))
            = (∑ i ∈ Finset.range n, ‖P.coeff i‖) * R ^ (n - 1) := by
        simp [Finset.sum_mul]
      have hsum_le : (∑ i ∈ Finset.range n, ‖P.coeff i‖) ≤ S := by
        simp [S]
      calc
        ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖
            ≤ ∑ i ∈ Finset.range n, ‖P.coeff i * z ^ i‖ := h1
        _ ≤ ∑ i ∈ Finset.range n, ‖P.coeff i‖ * R ^ (n - 1) := h2
        _ = (∑ i ∈ Finset.range n, ‖P.coeff i‖) * R ^ (n - 1) := h3
        _ ≤ S * R ^ (n - 1) := by
              exact mul_le_mul_of_nonneg_right hsum_le (pow_nonneg hR_nonneg _)
    have h_lead_re : (P.coeff n * z ^ n).re = ‖a‖ * R ^ n := by
      have hw_pow : w ^ n = wtarget := hw
      have ha_mul : a * w ^ n = (‖a‖ : ℂ) := by
        have : a * w ^ n = a * wtarget := by simp [hw_pow]
        simpa [wtarget, a] using (this.trans (mul_conj_div_norm a ha))
      have hz_pow : z ^ n = ((R : ℂ) ^ n) * (w ^ n) := by
        simp [z, mul_pow, mul_comm]
      have hcoeffn : P.coeff n = a := by simp [a, n, Polynomial.coeff_natDegree]
      have hreR : ∀ m : ℕ, (((R : ℂ) ^ m).re) = R ^ m := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
            simp [pow_succ, ih, mul_re]
      calc
        (P.coeff n * z ^ n).re
            = (a * z ^ n).re := by simp [hcoeffn]
        _ = (a * (((R : ℂ) ^ n) * (w ^ n))).re := by simp [hz_pow]
        _ = (((R : ℂ) ^ n) * (a * (w ^ n))).re := by
              ring_nf
        _ = (((R : ℂ) ^ n) * (‖a‖ : ℂ)).re := by simp [ha_mul]
        _ = (((R : ℂ) ^ n).re) * ‖a‖ := by
              simp [mul_re]
        _ = (R ^ n) * ‖a‖ := by simp [hreR n]
        _ = ‖a‖ * R ^ n := by ring
    refine ⟨z, hz_norm, ?_⟩
    have hre_lower : (∑ i ∈ Finset.range n, P.coeff i * z ^ i).re
        ≥ -‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ := by
      have habs : |(∑ i ∈ Finset.range n, P.coeff i * z ^ i).re|
          ≤ ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ :=
        Complex.abs_re_le_norm _
      have := neg_le_of_abs_le habs
      simpa using this
    have hre_main :
        (P.eval z).re ≥ (P.coeff n * z ^ n).re - ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ := by
      have : (P.eval z).re =
          (∑ i ∈ Finset.range n, P.coeff i * z ^ i).re + (P.coeff n * z ^ n).re := by
        simp [h_eval, add_comm]
      linarith [this, hre_lower]
    have hR_ge_R0 : R0 ≤ R := hR
    have hR_ge : 2 * S / ‖a‖ ≤ R := le_trans (le_max_right _ _) hR_ge_R0
    have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR_ge1
    have hR_nonneg' : 0 ≤ R := le_of_lt hRpos
    have hn_ge1 : 1 ≤ n := Nat.succ_le_of_lt hn0
    have hlower_le : S * R ^ (n - 1) ≤ (‖a‖ / 2) * R ^ n := by
      have ha_pos : 0 < ‖a‖ := hnorm_a_pos
      have hS_le : S ≤ (‖a‖ / 2) * R := by
        have : 2 * S ≤ ‖a‖ * R := by
          have := (mul_le_mul_of_nonneg_left hR_ge (by linarith [ha_pos.le] : (0 : ℝ) ≤ ‖a‖))
          have hne : (‖a‖ : ℝ) ≠ 0 := ne_of_gt ha_pos
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hne] using this
        have : S ≤ (‖a‖ * R) / 2 := by linarith
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
      have : S * R ^ (n - 1) ≤ (‖a‖ / 2) * R * R ^ (n - 1) := by
        have hpow_nonneg : 0 ≤ R ^ (n - 1) := pow_nonneg hR_nonneg' _
        exact mul_le_mul_of_nonneg_right hS_le hpow_nonneg
      have hRR : R * R ^ (n - 1) = R ^ n := by
        have : n = (n - 1) + 1 := by
          exact (Nat.sub_add_cancel hn_ge1).symm
        rw [this, pow_succ]
        ring_nf; grind
      simpa [mul_assoc, hRR] using this
    have hfinal_re :
        (‖a‖ / 2) * R ^ n ≤ (P.eval z).re := by
      have hlower' : ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ ≤ (‖a‖ / 2) * R ^ n := by
        exact h_lower_norm.trans hlower_le
      have hlead : (P.coeff n * z ^ n).re = ‖a‖ * R ^ n := by simpa [a] using h_lead_re
      have hre_main' :
          (‖a‖ * R ^ n) - ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ ≤ (P.eval z).re := by
        simpa [hlead] using hre_main
      have hsub :
          (‖a‖ * R ^ n) - (‖a‖ / 2) * R ^ n ≤
            (‖a‖ * R ^ n) - ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ :=
        sub_le_sub_left hlower' (‖a‖ * R ^ n)
      have hsim : (‖a‖ * R ^ n) - (‖a‖ / 2) * R ^ n = (‖a‖ / 2) * R ^ n := by ring
      have : (‖a‖ * R ^ n) - (‖a‖ / 2) * R ^ n ≤ (P.eval z).re :=
        hsub.trans hre_main'
      simpa [hsim] using this
    simpa [a, n] using hfinal_re

theorem natDegree_le_floor_of_growth_exp_eval
    {ρ : ℝ} (hρ : 0 ≤ ρ) (P : Polynomial ℂ)
    (hgrowth :
      ∃ C > 0, ∀ z : ℂ,
        Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) ≤ C * (1 + ‖z‖) ^ ρ) :
    P.natDegree ≤ Nat.floor ρ := by
  classical
  by_cases hdeg : P.natDegree = 0
  · simp [hdeg]
  · have hnpos : 0 < P.natDegree := Nat.pos_of_ne_zero hdeg
    rcases exists_z_norm_eq_re_eval_ge (P := P) hnpos with ⟨R0, hR0pos, hray⟩
    rcases hgrowth with ⟨C, hCpos, hC⟩
    have hLCpos : 0 < ‖P.leadingCoeff‖ := by
      have hP0 : P ≠ 0 := by
        intro h0
        simp [h0] at hdeg
      have : P.leadingCoeff ≠ 0 := (Polynomial.leadingCoeff_ne_zero).2 hP0
      exact norm_pos_iff.2 this
    let c : ℝ := ‖P.leadingCoeff‖ / 2
    have hcpos : 0 < c := by
      have : (0 : ℝ) < (2 : ℝ) := by norm_num
      exact (div_pos hLCpos this)
    have hn_le_real : (P.natDegree : ℝ) ≤ ρ := by
      by_contra hnlt
      have hnlt' : ρ < (P.natDegree : ℝ) := lt_of_not_ge hnlt
      let δ : ℝ := (P.natDegree : ℝ) - ρ
      have hδ : 0 < δ := sub_pos.2 hnlt'
      let K0 : ℝ := (C * (2 : ℝ) ^ ρ) / c
      have hK0 : ∃ R1, ∀ R ≥ R1, K0 + 1 ≤ R ^ δ := by
        have h : ∀ᶠ R in (atTop : Filter ℝ), K0 + 1 ≤ R ^ δ :=
          (tendsto_atTop.mp (tendsto_rpow_atTop hδ)) (K0 + 1)
        rcases (eventually_atTop.1 h) with ⟨R1, hR1⟩
        exact ⟨R1, hR1⟩
      rcases hK0 with ⟨R1, hR1⟩
      set R : ℝ := max (max R0 1) R1
      have hR_ge_R0 : R0 ≤ R := le_trans (le_max_left _ _) (le_max_left _ _)
      have hR_ge1 : (1 : ℝ) ≤ R := le_trans (le_max_right _ _) (le_max_left _ _)
      have hR_ge_R1 : R1 ≤ R := le_max_right _ _
      have hR_pos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR_ge1
      have hRδ : K0 + 1 ≤ R ^ δ := hR1 R hR_ge_R1
      rcases hray R hR_ge_R0 with ⟨z, hz_norm, hz_re⟩
      have hlog_lower :
          (P.eval z).re ≤ Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) := by
        have hpos : 0 < ‖Complex.exp (Polynomial.eval z P)‖ := by
          simp
        have hle :
            ‖Complex.exp (Polynomial.eval z P)‖ ≤
              1 + ‖Complex.exp (Polynomial.eval z P)‖ := by
          linarith [norm_nonneg (Complex.exp (Polynomial.eval z P))]
        have hlog_le : Real.log ‖Complex.exp (Polynomial.eval z P)‖
            ≤ Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) :=
          Real.log_le_log hpos hle
        have hlog_eq : Real.log ‖Complex.exp (Polynomial.eval z P)‖ = (P.eval z).re := by
          simp [Complex.norm_exp]
        simpa [hlog_eq] using hlog_le
      have hlog_upper :
          Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) ≤ C * (1 + ‖z‖) ^ ρ :=
        hC z
      have hmain : c * R ^ (P.natDegree : ℝ) ≤ C * (1 + R) ^ ρ := by
        have hz_re' : c * R ^ P.natDegree ≤ (P.eval z).re := by
          simpa [c] using hz_re
        have hz_re'' : c * R ^ (P.natDegree : ℝ) ≤ (P.eval z).re := by
          simpa [Real.rpow_natCast, c] using hz_re'
        have : c * R ^ (P.natDegree : ℝ) ≤ Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) :=
          hz_re''.trans hlog_lower
        have : c * R ^ (P.natDegree : ℝ) ≤ C * (1 + ‖z‖) ^ ρ :=
          this.trans hlog_upper
        simpa [hz_norm] using this
      have h1R_le : (1 + R : ℝ) ≤ R * 2 := by linarith
      have hpow1 : (1 + R : ℝ) ^ ρ ≤ (R * 2) ^ ρ :=
        Real.rpow_le_rpow (by linarith [hR_pos.le]) h1R_le hρ
      have hR2 : (R * 2) ^ ρ = R ^ ρ * (2 : ℝ) ^ ρ := by
        have hRnonneg : 0 ≤ R := le_of_lt hR_pos
        have h2nonneg : 0 ≤ (2 : ℝ) := by norm_num
        simpa [mul_assoc] using (Real.mul_rpow hRnonneg h2nonneg (z := ρ))
      have hmain' : c * R ^ (P.natDegree : ℝ) ≤ C * (R ^ ρ * (2 : ℝ) ^ ρ) := by
        have := le_trans hmain (mul_le_mul_of_nonneg_left hpow1 (le_of_lt hCpos))
        simpa [hR2, mul_assoc, mul_left_comm, mul_comm] using this
      have hRρ_pos : 0 < R ^ ρ := Real.rpow_pos_of_pos hR_pos _
      have hRρ_ne : (R ^ ρ : ℝ) ≠ 0 := ne_of_gt hRρ_pos
      have hdiv :
          (c * R ^ (P.natDegree : ℝ)) / (R ^ ρ) ≤ C * (2 : ℝ) ^ ρ := by
        have h :=
            div_le_div_of_nonneg_right hmain' (le_of_lt hRρ_pos)
        have hRhs : (C * (R ^ ρ * (2 : ℝ) ^ ρ)) / (R ^ ρ) = C * (2 : ℝ) ^ ρ := by
          field_simp [hRρ_ne]
        simpa [hRhs, mul_assoc, mul_left_comm, mul_comm] using h
      have hRsub : R ^ δ = R ^ (P.natDegree : ℝ) / R ^ ρ := by
        simpa [δ] using (Real.rpow_sub hR_pos (P.natDegree : ℝ) ρ)
      have hRδ_le : c * (R ^ δ) ≤ C * (2 : ℝ) ^ ρ := by
        have hLhs : c * (R ^ δ) = (c * R ^ (P.natDegree : ℝ)) / (R ^ ρ) := by
          simp [hRsub, div_eq_mul_inv, mul_left_comm, mul_comm]
        simpa [hLhs] using hdiv
      have hRδ_le' : R ^ δ ≤ K0 := by
        have : R ^ δ ≤ (C * (2 : ℝ) ^ ρ) / c := by
          refine (le_div_iff₀ hcpos).2 ?_
          simpa [mul_assoc, mul_left_comm, mul_comm] using hRδ_le
        simpa [K0] using this
      have : K0 + 1 ≤ K0 := le_trans hRδ (le_trans hRδ_le' (le_rfl))
      exact (not_lt_of_ge this) (lt_add_of_pos_right _ (by norm_num : (0 : ℝ) < 1))
    exact (Nat.le_floor_iff hρ).2 hn_le_real

theorem natDegree_le_floor_of_exp_eval_norm_bound {τ : ℝ} (hτ : 0 ≤ τ) (P : Polynomial ℂ)
    (hbound :
      ∃ C > 0, ∀ z : ℂ,
        ‖Complex.exp (Polynomial.eval z P)‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ)) :
    P.natDegree ≤ Nat.floor τ := by
  rcases hbound with ⟨C, hCpos, hC⟩
  have hlog_growth :
      ∃ C > 0, ∀ z : ℂ,
        Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) ≤ C * (1 + ‖z‖) ^ τ :=
    Real.log_growth_of_norm_le_exp_mul_rpow
      (f := fun z : ℂ => Complex.exp (Polynomial.eval z P))
      (r := fun z : ℂ => 1 + ‖z‖) hCpos hτ
      (fun z => by linarith [norm_nonneg z]) hC
  exact natDegree_le_floor_of_growth_exp_eval (ρ := τ) hτ P hlog_growth

end Hadamard
end Complex
end
end HadamardSourceScope32

section HadamardSourceScope33

noncomputable section

open Set Filter Asymptotics
open scoped Topology BigOperators

namespace Complex.Hadamard

open _root_.Complex

lemma no_zero_on_sphere_of_norm_image_avoid
    {f : ℂ → ℂ} (hentire : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    {B r : ℝ} (hrpos : 0 < r) (hr_le_B : r ≤ B)
    (smallSet : Set (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (hsmall_fin : smallSet.Finite)
    (hsmallSet :
      smallSet = {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀Val p‖ ≤ B})
    (hr_not_bad :
      let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
      let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀Val p‖
      r ∉ small.image a) :
    ∀ u : ℂ, ‖u‖ = r → f u ≠ 0 := by
  classical
  let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
  let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀Val p‖
  let bad : Finset ℝ := small.image a
  have hr_not_bad' : r ∉ bad := by
    simpa [bad, small, a] using hr_not_bad
  have hr_not :
      ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
        ‖divisorZeroIndex₀Val p‖ ≤ B → r ≠ ‖divisorZeroIndex₀Val p‖ := by
    intro p hpB hEq
    have hp_small : p ∈ small := by
      have hp_mem : p ∈ smallSet := by
        simpa [hsmallSet] using hpB
      simpa [small] using (hsmall_fin.mem_toFinset.2 hp_mem)
    have : r ∈ bad := Finset.mem_image.2 ⟨p, hp_small, by simpa [a] using hEq.symm⟩
    exact (hr_not_bad' this).elim
  exact no_zero_on_sphere_of_forall_val_norm_ne (f := f) hentire hnot
    (B := B) (r := r) hrpos hr_le_B hr_not

theorem norm_inv_hadamardDenominator_le_exp_on_cartan_circle
    {f : ℂ → ℂ} {ρ τ : ℝ} {m : ℕ}
    (hmρ : (m : ℝ) ≤ ρ) (hτ : ρ < τ) (hτ_lt : τ < (m + 1 : ℝ))
    (hτ_nonneg : 0 ≤ τ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1)))
    (hsumτ : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ τ)) :
    let Sτ : ℝ :=
      ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), ‖divisorZeroIndex₀Val p‖⁻¹ ^ τ
    let Cprod : ℝ := cartanProductConstant m τ Sτ
    ∀ {R r : ℝ}, 0 < R → 1 ≤ R → R ≤ r → r ≤ 2 * R →
      ∀ (smallSet : Set (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
        (hsmall_fin : smallSet.Finite),
        smallSet =
            {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) |
              ‖divisorZeroIndex₀Val p‖ ≤ 4 * R} →
        (let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
         let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
          fun p => ‖divisorZeroIndex₀Val p‖
         r ∉ small.image a) →
        (let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
         let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
          fun p => ‖divisorZeroIndex₀Val p‖
         (∑ p ∈ small, (1 : ℝ) * CartanBound.φ (r / a p)) ≤
          CartanBound.Cφ * (small.card : ℝ)) →
        ∀ u : ℂ, ‖u‖ = r →
          ‖(u ^ analyticOrderNatAt f 0 *
              divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖
            ≤ Real.exp (Cprod * (1 + r) ^ τ) := by
  classical
  intro Sτ Cprod R r hRpos hRle hR_le_r hr_le_2R smallSet hsmall_fin
    hsmallSet hr_not_bad hr_phi u hur
  let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
  let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀Val p‖
  let bad : Finset ℝ := small.image a
  have hr_not_bad' : r ∉ bad := by
    simpa [bad, small, a] using hr_not_bad
  have hr1 : (1 : ℝ) ≤ r := le_trans hRle hR_le_r
  have hpow_inv_le1 : ‖(u ^ analyticOrderNatAt f 0)⁻¹‖ ≤ 1 :=
    Complex.norm_inv_pow_le_one_of_one_le_norm u (analyticOrderNatAt f 0) (by simpa [hur] using hr1)
  let fac : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ :=
    fun p => weierstrassFactor m (u / divisorZeroIndex₀Val p)
  have hloc :
      HasProdLocallyUniformlyOn
        (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (w : ℂ) =>
          weierstrassFactor m (w / divisorZeroIndex₀Val p))
        (divisorCanonicalProduct m f (Set.univ : Set ℂ))
        (Set.univ : Set ℂ) :=
    hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
  have hprod :
      HasProd fac (divisorCanonicalProduct m f (Set.univ : Set ℂ) u) :=
    hloc.hasProd (by simp : u ∈ (Set.univ : Set ℂ))
  let ap : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀Val p‖
  have : DecidablePred (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) => p ∈ small) :=
    Classical.decPred _
  let b : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
    fun p =>
      if hp : p ∈ small then
        CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
      else
        (2 : ℝ) * (r / ap p) ^ τ
  have hterm : ∀ p, ‖(fac p)⁻¹‖ ≤ Real.exp (b p) := by
    intro p
    by_cases hp : p ∈ small
    · have hval_ne : r ≠ ap p := by
        intro hEq
        have : r ∈ bad := by
          refine Finset.mem_image.2 ⟨p, hp, ?_⟩
          simp [ap, a, hEq]
        exact (hr_not_bad' this).elim
      have hval0 : divisorZeroIndex₀Val p ≠ 0 := divisorZeroIndex₀Val_ne_zero p
      have hmτ : (m : ℝ) ≤ τ := le_trans hmρ (le_of_lt hτ)
      have hnear :
          ‖(weierstrassFactor m (u / divisorZeroIndex₀Val p))⁻¹‖
            ≤ Real.exp (CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)) := by
        simpa [ap] using
          (norm_inv_weierstrassFactor_le_exp_near (m := m) (τ := τ) (r := r)
              (u := u) (a := divisorZeroIndex₀Val p)
              (hur := hur) (ha := hval0) (hr := by simpa [ap] using hval_ne) hmτ)
      simpa [fac, b, hp] using hnear
    · have hlarge : (4 * R : ℝ) < ap p := by
        have : ¬ap p ≤ 4 * R := by
          intro hle
          have : p ∈ small := by
            have hp_mem : p ∈ smallSet := by
              simpa [hsmallSet, ap] using hle
            simpa [small] using (hsmall_fin.mem_toFinset.2 hp_mem)
          exact hp this
        exact lt_of_not_ge this
      have hz' : ‖u / divisorZeroIndex₀Val p‖ ≤ (1 / 2 : ℝ) :=
        norm_div_le_half_of_norm_le_of_two_mul_lt (z := u) (a := divisorZeroIndex₀Val p)
          (R := 2 * R) (by nlinarith [hRpos]) (by rw [hur]; exact hr_le_2R)
          (by nlinarith [hlarge])
      have hτ_le : τ ≤ (m + 1 : ℝ) := le_of_lt hτ_lt
      have hfar :
          ‖(weierstrassFactor m (u / divisorZeroIndex₀Val p))⁻¹‖ ≤
            Real.exp ((2 : ℝ) * (r / ap p) ^ τ) := by
        simpa [ap] using
          (norm_inv_weierstrassFactor_le_exp_far (m := m) (τ := τ) (r := r)
              (u := u) (a := divisorZeroIndex₀Val p)
              (hur := hur) (ha := divisorZeroIndex₀Val_ne_zero p) (hz := hz') hτ_le)
      simpa [fac, b, hp] using hfar
  have hb_le :
      ∀ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)),
        (∑ p ∈ s, b p) ≤ Cprod * (1 + r) ^ τ := by
    intro s
    simpa [small, ap, b, Sτ, Cprod, a, hsmallSet] using
      (Complex.Hadamard.cartan_sum_majorant_le (f := f) (m := m) (τ := τ) (R := R) (r := r)
        (hRpos := hRpos) (hrpos := lt_of_lt_of_le hRpos hR_le_r)
        (hR_le_r := hR_le_r) (hτ_nonneg := hτ_nonneg)
        (smallSet := smallSet) (hsmall_fin := hsmall_fin) (hsmallSet := hsmallSet)
        (hsumτ := hsumτ)
        (hr_phi := by
          simpa [small, a, one_mul] using hr_phi)
        s)
  have hcprod_inv :
      ‖(divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖ ≤
        Real.exp (Cprod * (1 + r) ^ τ) := by
    refine hasProd_norm_inv_le_exp_of_pointwise_le_exp
      (α := divisorZeroIndex₀ f (Set.univ : Set ℂ)) (fac := fac)
      (F := divisorCanonicalProduct m f (Set.univ : Set ℂ) u)
      hprod (b := b) (B := Cprod * (1 + r) ^ τ) ?_ ?_
    · exact hterm
    · intro s
      exact hb_le s
  have hmul :
      ‖(u ^ analyticOrderNatAt f 0 *
          divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖
        =
      ‖(u ^ analyticOrderNatAt f 0)⁻¹‖ *
        ‖(divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖ := by
    simp [mul_inv_rev, mul_comm]
  rw [hmul]
  have :
      ‖(u ^ analyticOrderNatAt f 0)⁻¹‖ *
          ‖(divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖
        ≤ 1 * Real.exp (Cprod * (1 + r) ^ τ) :=
    mul_le_mul hpow_inv_le1 hcprod_inv (by positivity) (by positivity)
  simpa using this

theorem hadamardQuotient_norm_le_exp_on_cartan_circle
    {f H : ℂ → ℂ} {ρ τ : ℝ} {m : ℕ} {Cf : ℝ}
    (hmρ : (m : ℝ) ≤ ρ) (hτ : ρ < τ) (hτ_lt : τ < (m + 1 : ℝ))
    (hτ_nonneg : 0 ≤ τ) (hentire : Differentiable ℂ f)
    (hnot : ∃ z : ℂ, f z ≠ 0)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1)))
    (hsumτ : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ τ))
    (hf_boundτ : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (Cf * (1 + ‖z‖) ^ τ))
    (hfactor : ∀ z : ℂ,
      f z =
        H z * z ^ analyticOrderNatAt f 0 *
          divisorCanonicalProduct m f (Set.univ : Set ℂ) z) :
    let Sτ : ℝ :=
      ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), ‖divisorZeroIndex₀Val p‖⁻¹ ^ τ
    let Cprod : ℝ := cartanProductConstant m τ Sτ
    ∀ {R r : ℝ}, 0 < R → 1 ≤ R → R ≤ r → r ≤ 2 * R → 0 < r →
      ∀ (smallSet : Set (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
        (hsmall_fin : smallSet.Finite),
        smallSet =
            {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) |
              ‖divisorZeroIndex₀Val p‖ ≤ 4 * R} →
        (let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
         let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
          fun p => ‖divisorZeroIndex₀Val p‖
         r ∉ small.image a) →
        (let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
         let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
          fun p => ‖divisorZeroIndex₀Val p‖
         (∑ p ∈ small, (1 : ℝ) * CartanBound.φ (r / a p)) ≤
          CartanBound.Cφ * (small.card : ℝ)) →
        ∀ u : ℂ, ‖u‖ = r → ‖H u‖ ≤ Real.exp ((Cf + Cprod + 10) * (1 + r) ^ τ) := by
  classical
  intro Sτ Cprod R r hRpos hRle hR_le_r hr_le_2R hrpos smallSet hsmall_fin
    hsmallSet hr_not_bad hr_phi u hur
  let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
  let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀Val p‖
  let bad : Finset ℝ := small.image a
  have hr_not_bad' : r ∉ bad := by
    simpa [bad, small, a] using hr_not_bad
  have hden_eq :
      f u =
        H u * (u ^ analyticOrderNatAt f 0 *
          divisorCanonicalProduct m f (Set.univ : Set ℂ) u) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using (hfactor u)
  have hfu_ne : f u ≠ 0 := by
    have hr_le_4R : r ≤ 4 * R := by nlinarith [hr_le_2R, hRpos]
    exact no_zero_on_sphere_of_norm_image_avoid (f := f) hentire hnot
      (B := 4 * R) (r := r) hrpos hr_le_4R smallSet hsmall_fin hsmallSet
      (by simpa [small, a] using hr_not_bad) u hur
  have hden_ne :
      (u ^ analyticOrderNatAt f 0 *
        divisorCanonicalProduct m f (Set.univ : Set ℂ) u) ≠ 0 := by
    intro hden0
    have : f u = 0 := by simpa [hden0] using hden_eq
    exact hfu_ne this
  have hHu :
      H u =
        f u / (u ^ analyticOrderNatAt f 0 *
          divisorCanonicalProduct m f (Set.univ : Set ℂ) u) := by
    exact eq_div_of_mul_eq hden_ne (Eq.symm hden_eq)
  have hf_u : ‖f u‖ ≤ Real.exp (Cf * (1 + r) ^ τ) := by
    simpa [hur] using hf_boundτ u
  have hden_inv :
      ‖(u ^ analyticOrderNatAt f 0 *
          divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖
        ≤ Real.exp (Cprod * (1 + r) ^ τ) := by
    simpa [Sτ, Cprod] using
      (norm_inv_hadamardDenominator_le_exp_on_cartan_circle
        (f := f) (ρ := ρ) (τ := τ) (m := m)
        hmρ hτ hτ_lt hτ_nonneg h_sum hsumτ
        (R := R) (r := r) hRpos hRle hR_le_r hr_le_2R
        smallSet hsmall_fin hsmallSet
        (by simpa [small, a] using hr_not_bad)
        (by simpa [small, a, one_mul] using hr_phi)
        u hur)
  have :
      ‖H u‖ ≤
        ‖f u‖ *
          ‖(u ^ analyticOrderNatAt f 0 *
            divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖ := by
    have :
        ‖H u‖ =
          ‖f u /
            (u ^ analyticOrderNatAt f 0 *
              divisorCanonicalProduct m f (Set.univ : Set ℂ) u)‖ := by
      simp [hHu]
    simp [div_eq_mul_inv, norm_inv, this]
  have hmul :
      ‖f u‖ *
          ‖(u ^ analyticOrderNatAt f 0 *
            divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖
        ≤ Real.exp (Cf * (1 + r) ^ τ) * Real.exp (Cprod * (1 + r) ^ τ) :=
    mul_le_mul hf_u hden_inv (by positivity) (by positivity)
  have hexp :
      Real.exp (Cf * (1 + r) ^ τ) * Real.exp (Cprod * (1 + r) ^ τ)
        = Real.exp ((Cf + Cprod) * (1 + r) ^ τ) := by
    simp [Real.exp_add, add_mul, add_comm]
  have : ‖H u‖ ≤ Real.exp ((Cf + Cprod) * (1 + r) ^ τ) :=
    (this.trans hmul).trans_eq hexp
  have hslack :
      Real.exp ((Cf + Cprod) * (1 + r) ^ τ) ≤
        Real.exp ((Cf + Cprod + 10) * (1 + r) ^ τ) := by
    refine Real.exp_le_exp.2 ?_
    have hnn : 0 ≤ (1 + r) ^ τ := by positivity
    nlinarith
  exact this.trans hslack

theorem hadamardQuotient_norm_le_exp_rpow_of_growth {f H : ℂ → ℂ} {ρ τ : ℝ} {m : ℕ}
    (hρ : 0 ≤ ρ) (hmρ : (m : ℝ) ≤ ρ) (hτ : ρ < τ) (hτ_lt : τ < (m + 1 : ℝ))
    (hτ_nonneg : 0 ≤ τ) (hentire : Differentiable ℂ f) (hH_entire : Differentiable ℂ H)
    (hnot : ∃ z : ℂ, f z ≠ 0)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1)))
    (hgrowth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ)
    (hfactor : ∀ z : ℂ,
      f z =
        H z * z ^ analyticOrderNatAt f 0 *
          divisorCanonicalProduct m f (Set.univ : Set ℂ) z) :
    ∃ C > 0, ∀ z : ℂ, ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ) := by
  rcases hgrowth with ⟨Cf, hCfpos, hCf⟩
  have hsumτ :
      Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
        ‖divisorZeroIndex₀Val p‖⁻¹ ^ τ) :=
    summable_norm_inv_rpow_divisorZeroIndex₀_of_growth (f := f) (ρ := ρ) (τ := τ)
      hρ hτ hentire hnot ⟨Cf, hCfpos, hCf⟩
  let Sτ : ℝ := ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), ‖divisorZeroIndex₀Val p‖⁻¹ ^ τ
  have hSτ_nonneg : 0 ≤ Sτ := tsum_nonneg fun _ =>
    Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _
  let Cprod : ℝ := cartanProductConstant m τ Sτ
  have hCprod_nonneg : 0 ≤ Cprod := by
    simpa [Cprod] using cartanProductConstant_nonneg (m := m) (τ := τ) hSτ_nonneg
  have hf_boundτ : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (Cf * (1 + ‖z‖) ^ τ) :=
    Real.norm_le_exp_mul_rpow_of_log_growth
      (f := f) (r := fun z : ℂ => 1 + ‖z‖) (C := Cf) (ρ := ρ) (τ := τ)
      hCfpos.le (fun z => by linarith [norm_nonneg z]) (le_of_lt hτ) hCf
  refine ⟨(Cf + Cprod + 10) * (3 : ℝ) ^ τ, by
    have h3τ : 0 < (3 : ℝ) ^ τ := by positivity
    nlinarith [hCfpos, hCprod_nonneg, h3τ], ?_⟩
  intro z
  let R : ℝ := max ‖z‖ 1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hRle : (1 : ℝ) ≤ R := le_max_right _ _
  let smallSet : Set (divisorZeroIndex₀ f (Set.univ : Set ℂ)) :=
    {p | ‖divisorZeroIndex₀Val p‖ ≤ 4 * R}
  have hsmall_fin : smallSet.Finite := by
    have : Metric.closedBall (0 : ℂ) (4 * R) ⊆ (Set.univ : Set ℂ) := by simp
    simpa [smallSet] using
      (divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ))
        (B := 4 * R) this)
  let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
  let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀Val p‖
  have ha_pos : ∀ p ∈ small, 0 < a p := by
    intro p hp
    exact norm_pos_iff.2 (divisorZeroIndex₀Val_ne_zero p)
  let bad : Finset ℝ := small.image a
  rcases CartanBound.exists_radius_Ioc_sum_mul_phi_div_le_Cφ_mul_sum_avoid
      (s := small) (w := fun _ => (1 : ℝ)) (a := a)
      (hw := by intro _ _; norm_num) (ha := ha_pos) (bad := bad) (R := R) hRpos with
    ⟨r, hr_mem, hr_not_bad, hr_phi⟩
  have hR_le_r : R ≤ r := le_of_lt hr_mem.1
  have hr_le_2R : r ≤ 2 * R := hr_mem.2
  have hrpos : 0 < r := lt_of_lt_of_le hRpos hR_le_r
  have hcircle :
      ∀ u : ℂ, ‖u‖ = r → ‖H u‖ ≤ Real.exp ((Cf + Cprod + 10) * (1 + r) ^ τ) := by
    simpa [Sτ, Cprod] using
      (hadamardQuotient_norm_le_exp_on_cartan_circle
        (f := f) (H := H) (ρ := ρ) (τ := τ) (m := m) (Cf := Cf)
        hmρ hτ hτ_lt hτ_nonneg hentire hnot h_sum hsumτ hf_boundτ hfactor
        (R := R) (r := r) hRpos hRle hR_le_r hr_le_2R hrpos
        smallSet hsmall_fin (by rfl)
        (by simpa [small, a, bad] using hr_not_bad)
        (by simpa [small, a, one_mul, Finset.sum_const, nsmul_eq_mul] using hr_phi))
  have hz_ball : z ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (le_max_left _ _) hr_mem.1
  have hball :
      ‖H z‖ ≤ Real.exp ((Cf + Cprod + 10) * (1 + r) ^ τ) := by
    exact Complex.norm_le_of_mem_ball_of_forall_sphere_norm_le hH_entire hrpos hz_ball hcircle
  have hr_le_3 : 1 + r ≤ 3 * (1 + ‖z‖) := by
    exact Real.one_add_le_three_mul_one_add_of_le_two_mul_max (norm_nonneg z)
      (by simpa [R] using hr_le_2R)
  have hmain :
      Real.exp ((Cf + Cprod + 10) * (1 + r) ^ τ)
        ≤ Real.exp (((Cf + Cprod + 10) * (3 : ℝ) ^ τ) * (1 + ‖z‖) ^ τ) := by
    have hnn : 0 ≤ (Cf + Cprod + 10) := by nlinarith [le_of_lt hCfpos, hCprod_nonneg]
    exact Real.exp_mul_rpow_le_exp_mul_rpow_of_le_mul hnn (by norm_num)
      (by linarith [le_of_lt hrpos]) (by positivity) hτ_nonneg hr_le_3
  simpa [mul_assoc] using hball.trans hmain

theorem hadamard_factorization_of_growth {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hentire : Differentiable ℂ f)
    (hnot : ∃ z : ℂ, f z ≠ 0)
    (hgrowth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) :
    ∃ (P : Polynomial ℂ),
      P.degree ≤ Nat.floor ρ ∧
      ∀ z : ℂ,
        f z =
          Complex.exp (Polynomial.eval z P) *
            z ^ (analyticOrderNatAt f 0) *
            divisorCanonicalProduct (Nat.floor ρ) f (Set.univ : Set ℂ) z := by
  set m : ℕ := Nat.floor ρ
  have h_sum :
      Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
        ‖divisorZeroIndex₀Val p‖⁻¹ ^ (m + 1)) := by
    simpa [m] using
      (summable_norm_inv_pow_divisorZeroIndex₀_of_growth (f := f) (ρ := ρ)
        hρ hentire hnot hgrowth)
  rcases exists_entire_nonzero_hadamardQuotient (m := m) (f := f) hentire hnot h_sum with
    ⟨H, hH_entire, hH_ne, hfactor⟩
  rcases Real.exists_between_self_and_floor_add_one_same_floor hρ with
    ⟨τ, hτ, hτ_lt, hτ_nonneg, hfloorτ'⟩
  have hfloorτ : Nat.floor τ = m := by
    simpa [m] using hfloorτ'
  have hτ_lt_m : τ < (m + 1 : ℝ) := by
    simpa [m] using hτ_lt
  have hτ_lt_nat : τ < ((m + 1 : ℕ) : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using hτ_lt_m
  have hmρ : (m : ℝ) ≤ ρ := by
    have := Nat.floor_le hρ
    simpa [m] using this
  have hH_bound_rpow :
      ∃ C > 0, ∀ z : ℂ, ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ) :=
    hadamardQuotient_norm_le_exp_rpow_of_growth (f := f) (H := H) (ρ := ρ) (τ := τ)
      (m := m) hρ hmρ hτ hτ_lt hτ_nonneg hentire hH_entire hnot h_sum hgrowth hfactor
  have hH_growth_nat :
      ∃ C > 0, ∀ z : ℂ, ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (m + 1)) := by
    exact Real.exists_norm_le_exp_mul_pow_of_rpow_bound
      (f := H) (r := fun z : ℂ => 1 + ‖z‖)
      (fun z => by linarith [norm_nonneg z]) hτ_lt_nat hH_bound_rpow
  rcases zero_free_polynomial_growth_is_exp_poly (H := H) (n := m + 1)
      hH_entire hH_ne hH_growth_nat with
    ⟨P, hPn, hHP⟩
  have hPnat : P.natDegree ≤ m := by
    have hbound :
        ∃ C > 0, ∀ z : ℂ,
          ‖Complex.exp (Polynomial.eval z P)‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ) := by
      rcases hH_bound_rpow with ⟨C, hCpos, hC⟩
      exact ⟨C, hCpos, fun z => by simpa [hHP z] using (hC z)⟩
    have := natDegree_le_floor_of_exp_eval_norm_bound hτ_nonneg P hbound
    simpa [hfloorτ] using this
  refine ⟨P, ?_, ?_⟩
  · have : P.degree ≤ m := Polynomial.degree_le_of_natDegree_le hPnat
    simpa [m] using this
  · intro z
    have hH' : H z = Complex.exp (Polynomial.eval z P) := by simpa using (hHP z)
    simpa [hH', mul_assoc, mul_left_comm, mul_comm, m] using (hfactor z)

end Complex.Hadamard
end
end HadamardSourceScope33

end HadamardAssemblyScope

end Erdos970
