import PrimeNumberTheoremAnd.Catalan.OrdinaryZetaZeroFree
import Mathlib.Analysis.Complex.RemovableSingularity

namespace CatalanPNT

noncomputable section

open Complex Filter Set
open scoped Topology

namespace CatalanOrdinaryZeta

noncomputable def regularizedZeta : ℂ → ℂ :=
  Function.update (fun s ↦ (s - 1) * riemannZeta s) 1 1

@[simp] theorem regularizedZeta_one : regularizedZeta 1 = 1 := by
  simp only [regularizedZeta, Function.update_self]

theorem regularizedZeta_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    regularizedZeta s = (s - 1) * riemannZeta s := by
  exact Function.update_of_ne hs ..

theorem regularizedZeta_ne_zero_at_one : regularizedZeta 1 ≠ 0 := by
  rw [regularizedZeta_one]
  exact one_ne_zero

theorem differentiable_regularizedZeta : Differentiable ℂ regularizedZeta := by
  rw [← differentiableOn_univ,
    ← differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) Filter.univ_mem]
  constructor
  · refine DifferentiableOn.congr (f := fun s ↦ (s - 1) * riemannZeta s) ?_ ?_
    · intro s hs
      exact ((differentiableAt_id.sub_const 1).mul
        (differentiableAt_riemannZeta (Set.mem_sdiff_singleton.mp hs).2)).differentiableWithinAt
    · intro s hs
      exact regularizedZeta_of_ne_one (Set.mem_sdiff_singleton.mp hs).2
  · simpa only [regularizedZeta, continuousAt_update_same] using riemannZeta_residue_one

theorem deriv_regularizedZeta_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    deriv regularizedZeta s =
      (s - 1) * deriv riemannZeta s + riemannZeta s := by
  have hderiv : deriv regularizedZeta s =
      deriv (fun w ↦ (w - 1) * riemannZeta w) s := by
    refine eventuallyEq_iff_exists_mem.mpr ?_ |>.deriv_eq
    exact ⟨_, isOpen_ne.mem_nhds hs,
      fun _ hw ↦ regularizedZeta_of_ne_one (Set.mem_ofPred.mp hw)⟩
  rw [hderiv, deriv_fun_mul (by fun_prop) (differentiableAt_riemannZeta hs),
    deriv_sub_const, deriv_id'', one_mul, add_comm]

theorem regularizedZeta_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    regularizedZeta s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hs₁
  · exact regularizedZeta_ne_zero_at_one
  · rw [regularizedZeta_of_ne_one hs₁]
    exact mul_ne_zero (sub_ne_zero.mpr hs₁)
      (riemannZeta_ne_zero_of_one_le_re_of_ne_one hs hs₁)

noncomputable def vonMangoldtAux (s : ℂ) : ℂ :=
  -deriv regularizedZeta s / regularizedZeta s

theorem continuousOn_vonMangoldtAux :
    ContinuousOn vonMangoldtAux {s | 1 ≤ s.re} := by
  change ContinuousOn (fun s ↦ -deriv regularizedZeta s / regularizedZeta s)
    {s | 1 ≤ s.re}
  simp_rw [neg_div]
  have h := differentiable_regularizedZeta
  exact ((h.contDiff.continuous_deriv le_rfl).continuousOn.div
    h.continuous.continuousOn fun s hs ↦ regularizedZeta_ne_zero_of_one_le_re hs).neg

theorem eqOn_vonMangoldtAux :
    Set.EqOn vonMangoldtAux
      (fun s ↦ LSeries (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) s - 1 / (s - 1))
      {s | 1 < s.re} := by
  intro s hs
  change vonMangoldtAux s =
    LSeries (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) s - 1 / (s - 1)
  have hs' : 1 < s.re := hs
  have hs₁ : s ≠ 1 := by
    rintro rfl
    norm_num at hs'
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs'
  unfold vonMangoldtAux
  rw [deriv_regularizedZeta_of_ne_one hs₁, regularizedZeta_of_ne_one hs₁,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs']
  field_simp [sub_ne_zero.mpr hs₁, hz]
  ring

end CatalanOrdinaryZeta

end

end CatalanPNT
