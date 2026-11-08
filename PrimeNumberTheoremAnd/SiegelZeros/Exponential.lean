import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.ProductBounds

namespace SiegelZeros

section
noncomputable section

namespace Complex
namespace Hadamard

open _root_.SiegelZeros.Complex _root_.SiegelZeros.Real BigOperators
  _root_.SiegelZeros.Finset Set Filter Topology Metric

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
end
section
noncomputable section

namespace Complex
namespace Hadamard

open _root_.SiegelZeros.Complex _root_.SiegelZeros.Real BigOperators
  _root_.SiegelZeros.Finset Set Filter Topology Metric

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
            simp [pow_succ, ih, Complex.mul_re]
      calc
        (P.coeff n * z ^ n).re
            = (a * z ^ n).re := by simp [hcoeffn]
        _ = (a * (((R : ℂ) ^ n) * (w ^ n))).re := by simp [hz_pow]
        _ = (((R : ℂ) ^ n) * (a * (w ^ n))).re := by
              ring_nf
        _ = (((R : ℂ) ^ n) * (‖a‖ : ℂ)).re := by simp [ha_mul]
        _ = (((R : ℂ) ^ n).re) * ‖a‖ := by
              simp [Complex.mul_re]
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
end

end SiegelZeros
