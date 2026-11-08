import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import PrimeNumberTheoremAnd.Catalan.Wiener

namespace CatalanPNT

open ZetaFivePNT

open ArithmeticFunction hiding log
open Nat hiding log
open _root_.Finset
open BigOperators _root_.Filter _root_.Real _root_.Asymptotics
open scoped Chebyshev

theorem WeakPNT' : Tendsto (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) atTop (nhds 1) := by
  have : (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) =
      (fun N ↦ (∑ n ∈ range N, Λ n)/N + Λ N / N) := by
    ext N
    have : N ∈ Iic N := mem_Iic.mpr (le_refl _)
    rw [← Finset.sum_erase_add _ _ this, ← Nat.Iio_eq_range, Iic_erase]
    exact add_div _ _ _
  rw [this, ← add_zero 1]
  apply Tendsto.add WeakPNT
  convert squeeze_zero (f := fun N ↦ Λ N / N) (g := fun N ↦ log N / N) (t₀ := atTop) ?_ ?_ ?_
  · intro N
    exact div_nonneg vonMangoldt_nonneg (cast_nonneg N)
  · intro N
    exact div_le_div_of_nonneg_right vonMangoldt_le_log (cast_nonneg N)
  simpa only [Function.comp_def, pow_one, one_mul, add_zero] using
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop

theorem WeakPNT'' : ψ ~[atTop] (fun x ↦ x) := by
    rw [(by rfl : ψ = (fun x ↦ ψ x))]
    simp_rw [Chebyshev.psi_eq_sum_Icc]
    apply IsEquivalent.trans (v := fun x ↦ (⌊x⌋₊:ℝ))
    · rw [isEquivalent_iff_tendsto_one]
      · convert Tendsto.comp WeakPNT' (tendsto_nat_floor_atTop (α := ℝ)) using 1
        ext x
        rfl
      rw [eventually_iff]
      simp only [ne_eq, cast_eq_zero, floor_eq_zero, not_lt, mem_atTop_sets,
        Set.mem_ofPred_eq]
      use 1
      simp only [imp_self, implies_true]
    exact Asymptotics.isEquivalent_nat_floor

theorem isLittleO_sqrt_mul_log : (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] _root_.id := by
  have : (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] fun x ↦ x := by
    refine (isLittleO_mul_iff_isLittleO_div ?_).mpr ?_
    · filter_upwards [eventually_gt_atTop 0] with x hx; exact (sqrt_ne_zero hx.le).mpr hx.ne'
    · convert isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2) using 2 with x
      rw [div_sqrt, sqrt_eq_rpow]
  exact this

theorem chebyshev_asymptotic : θ ~[atTop] id := by
  rw [← sub_sub_self ψ θ]
  refine WeakPNT''.sub_isLittleO
    (IsBigO.trans_isLittleO (g := fun x ↦ 2 * x.sqrt * x.log) ?_ ?_)
  · rw [isBigO_iff']; refine ⟨1, one_pos, ?_⟩
    simp only [one_mul, eventually_atTop]
    exact ⟨2, fun x hx ↦ by
      rw [Pi.sub_apply, norm_eq_abs, norm_eq_abs, abs_of_nonneg (by bound : 0 ≤ 2 * √x * log x)]
      exact (abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x))).symm ▸
        Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith : 1 ≤ x)⟩
  · convert isLittleO_sqrt_mul_log.const_mul_left 2 using 1 <;> first | rfl | (funext x; ring)

end CatalanPNT
