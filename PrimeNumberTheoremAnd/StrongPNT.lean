module

public import Architect
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Data.Rat.Cast.OfScientific
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Analysis.Complex.BorelCaratheodory
public import PrimeNumberTheoremAnd.MediumPNT

@[expose] public section

open Nat Filter Set Function Complex Real ComplexConjugate MeasureTheory

open ArithmeticFunction (vonMangoldt)

local notation (name := mellintransform2) "𝓜" => mellin

local notation "Λ" => vonMangoldt

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

local notation "ψ" => ChebyshevPsi

--open scoped ArithmeticFunction

@[blueprint "AnalyticOn.norm_le_of_norm_le_on_sphere"
  (title := "AnalyticOn.norm-le-of-norm-le-on-sphere")
  (statement := /--
    An application of the Maximum modulus principle.
  -/)
  (proof := /--
    This is standard in the literature.
  -/)
  (latexEnv := "lemma")]
lemma AnalyticOn.norm_le_of_norm_le_on_sphere {C r R : ℝ} {f : ℂ → ℂ} {w : ℂ}
    (hyp_r : r ≤ R)
    (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (cond : ∀ z ∈ Metric.sphere 0 r, ‖f z‖ ≤ C)
    (wInS : w ∈ Metric.closedBall 0 r) :
    ‖f w‖ ≤ C := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    (U := Metric.closedBall 0 r) Metric.isBounded_closedBall
  · apply DifferentiableOn.diffContOnCl
    rw [Metric.closure_closedBall]
    exact AnalyticOn.differentiableOn
      (AnalyticOn.mono analytic
        (Metric.closedBall_subset_closedBall hyp_r))
  · rw [frontier_closedBall']
    exact cond
  · rw [Metric.closure_closedBall]
    exact wInS

@[blueprint "borelCaratheodory'"
  (title := "borelCaratheodory'")
  (statement := /--
    An application of
    \begin{verbatim}
      Complex.borelCaratheodory_zero.
    \end{verbatim}
  -/)
  (proof := /--
    This is standard in the literature.
  -/)
  (latexEnv := "theorem")]
theorem borelCaratheodory' {M r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (Mpos : 0 < M) (Rpos : 0 < R) (hyp_r : r < R)
    (analytic : AnalyticOn ℂ f (Metric.ball 0 R))
    (zeroAtZero : f 0 = 0)
    (realPartBounded : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ M)
    (hyp_z : z ∈ Metric.closedBall 0 r) :
    ‖f z‖ ≤ (2 * M * r) / (R - r) := by
  have h_borelCaratheodory : ∀ ε > 0, ‖f z‖ ≤ (2 * (M + ε) * ‖z‖) / (R - ‖z‖) := by
    intro ε εpos;
    apply Complex.borelCaratheodory_zero;
    exacts [by linarith, analytic.differentiableOn, fun z hz => by rw [Set.mem_ofPred_eq]; linarith [realPartBounded z hz], Rpos, by exact Metric.mem_ball.mpr ( lt_of_le_of_lt ( Metric.mem_closedBall.mp hyp_z ) hyp_r ), zeroAtZero]
  have h_limit : ‖f z‖ ≤ (2 * M * ‖z‖) / (R - ‖z‖) := by
    have h_limit : Filter.Tendsto (fun ε => (2 * (M + ε) * ‖z‖) / (R - ‖z‖)) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((2 * M * ‖z‖) / (R - ‖z‖))) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto' ?_ _ _ (by ring_nf))
      exact ((continuous_const.mul (continuous_const.add continuous_id)).mul continuous_const).div_const _
    exact le_of_tendsto_of_tendsto tendsto_const_nhds h_limit ( Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => h_borelCaratheodory ε hε );
  rw [mem_closedBall_iff_norm, sub_zero] at hyp_z
  refine le_trans h_limit ?_;
  gcongr
  · exact mul_nonneg (mul_nonneg (zero_le_two) (le_of_lt Mpos)) (le_trans (norm_nonneg z) hyp_z)

blueprint_comment /--
    This upstreamed from https://github.com/math-inc/strongpnt/tree/main
-/

@[blueprint "cauchy_formula_deriv"
  (title := "cauchy-formula-deriv")
  (statement := /--
    Let $f$ be analytic on $|z|\leq R$. For any $z$ with $|z|\leq r$ and any $r'$
    with $0 < r < r' < R$ we have
    $$f'(z)=\frac{1}{2\pi i}\oint_{|w|=r'}\frac{f(w)}{(w-z)^2}\,dw=\frac{1}{2\pi}
    \int_0^{2\pi}\frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}\,dt.$$
  -/)
  (proof := /--
    This is just Cauchy's integral formula for derivatives.
  -/)
  (latexEnv := "lemma")]
lemma cauchy_formula_deriv {r r' R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (r_lt_r' : r < r') (r'_lt_R : r' < R)
    (hf_on_ball : DifferentiableOn ℂ f (Metric.ball 0 R))
    (hz : z ∈ Metric.closedBall 0 r) :
    deriv f z = (1 / (2 * Real.pi * I)) • ∮ w in C(0, r'), (w - z)⁻¹ ^ 2 • f w := by
  have hz_in_ball : z ∈ Metric.ball 0 r' :=
    Metric.mem_ball.mpr <| (Metric.mem_closedBall.mp hz).trans_lt r_lt_r'
  simp [← Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
      Metric.isOpen_ball (Metric.closedBall_subset_ball r'_lt_R) hf_on_ball hz_in_ball]

@[blueprint "DerivativeBound"
  (title := "DerivativeBound")
  (statement := /--
    Let $R,\,M>0$ and $0 < r < r' < R$. Let $f$ be analytic on $|z|\leq R$ such that
    $f(0)=0$ and suppose $\Re f(z)\leq M$ for all $|z|\leq R$. Then we have that
    $$|f'(z)|\leq\frac{2M(r')^2}{(R-r')(r'-r)^2}$$
    for all $|z|\leq r$.
  -/)
  (proof := /--
    By Lemma \ref{cauchy_formula_deriv} we know that
    $$f'(z)=\frac{1}{2\pi i}\oint_{|w|=r'}\frac{f(w)}{(w-z)^2}\,dw
      =\frac{1}{2\pi }\int_0^{2\pi}\frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}\,dt.$$
    Thus,
    \begin{equation}\label{pickupPoint1}
        |f'(z)|=\left|\frac{1}{2\pi}\int_0^{2\pi}
          \frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}\,dt\right|
          \leq\frac{1}{2\pi}\int_0^{2\pi}
          \left|\frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}\right|\,dt.
    \end{equation}
    Now applying Theorem \ref{borelCaratheodory'}, and noting that
    $r'-r\leq|r'e^{it}-z|$, we have that
    $$\left|\frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}\right|
      \leq\frac{2M(r')^2}{(R-r')(r'-r)^2}.$$
    Substituting this into Equation (\ref{pickupPoint1}) and evaluating the integral
    completes the proof.
  -/)
  (latexEnv := "lemma")]
lemma DerivativeBound {M r r' R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (Mpos : 0 < M) (pos_r : 0 < r) (r_lt_r' : r < r') (r'_lt_R : r' < R)
    (analytic_f : AnalyticOn ℂ f (Metric.ball 0 R))
    (f_zero_at_zero : f 0 = 0)
    (re_f_le_M : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ M)
    (z_in_r : z ∈ Metric.closedBall 0 r) :
    ‖(deriv f) z‖ ≤ 2 * M * (r') ^ 2 / ((R - r') * (r' - r) ^ 2) := by
  rw [cauchy_formula_deriv r_lt_r' r'_lt_R analytic_f.differentiableOn  z_in_r, one_div]
  grw [circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const (by linarith) (C := 2 * M * r' / ((R - r') * (r' - r) ^ 2))]
  · exact le_of_eq (by ring)
  · intro z' hz'
    rw [smul_eq_mul, norm_mul]
    grw[borelCaratheodory' Mpos (by grind) r'_lt_R analytic_f f_zero_at_zero  re_f_le_M
      (Metric.sphere_subset_closedBall hz')]
    suffices ‖(z' - z)⁻¹ ^ 2‖ ≤ 1 / (r' - r) ^ 2 by
      grw [this]
      · exact le_of_eq (by field)
      · refine mul_nonneg (mul_nonneg ?_ ?_) (inv_nonneg.mpr ?_) <;> linarith
    have hdist : r' - r ≤ ‖z' - z‖ := by
      simp only [mem_sphere_iff_norm, sub_zero, Metric.mem_closedBall,
        dist_zero_right] at hz' z_in_r
      rw [← hz']
      exact le_trans (by linarith) (norm_sub_norm_le z' z)
    rw [norm_pow, norm_inv, one_div, inv_pow]
    gcongr

@[blueprint "BorelCaratheodoryDeriv"
  (title := "BorelCaratheodoryDeriv")
  (statement := /--
    Let $R,\,M>0$. Let $f$ be analytic on $|z|\leq R$ such that $f(0)=0$ and suppose
    $\Re f(z)\leq M$ for all $|z|\leq R$. Then for any $0 < r < R$,
    $$|f'(z)|\leq\frac{16MR^2}{(R-r)^3}$$
    for all $|z|\leq r$.
  -/)
  (proof := /--
    Using Lemma \ref{DerivativeBound} with $r'=(R+r)/2$, and noting that $r < R$,
    we have that
    $$|f'(z)|\leq\frac{4M(R+r)^2}{(R-r)^3}\leq\frac{16MR^2}{(R-r)^3}.$$
  -/)
  (latexEnv := "theorem")]
theorem BorelCaratheodoryDeriv {M r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (Mpos : 0 < M) (rpos : 0 < r) (hyp_r : r < R)
    (analytic_f : AnalyticOn ℂ f (Metric.ball 0 R))
    (zeroAtZero : f 0 = 0)
    (realPartBounded : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ M)
    (hyp_z : z ∈ Metric.closedBall 0 r) :
    ‖deriv f z‖ ≤ 16 * M * R ^ 2 / (R - r) ^ 3 := by
  have hr' : 2 * M * ((R + r) / 2) ^ 2 / ((R - (R + r) / 2) * ((R + r) / 2 - r) ^ 2) =
      4 * M * (R + r) ^ 2 / (R - r) ^ 3 := by field_simp; ring
  calc ‖deriv f z‖
      _ ≤ 4 * M * (R + r) ^ 2 / (R - r) ^ 3 := hr' ▸
          DerivativeBound Mpos rpos (by linarith) (by linarith) analytic_f zeroAtZero realPartBounded hyp_z
      _ ≤ 16 * M * R ^ 2 / (R - r) ^ 3 := by
          have : 16 * M * R ^ 2 = 4 * M * (2 * R) ^ 2 := by ring_nf
          rw [this]; bound

blueprint_comment /--
\begin{definition}[TaxicabIntegral]\label{TaxicabIntegral}
  Let $0 < R$. Let $f:\overline{\mathbb{D}_R}\to\mathbb{C}$ be analytic on neighborhoods of points
  in $\overline{\mathbb{D}_R}$. Define the functon $I_f:\mathbb{D}_R\to\mathbb{C}$ by
    $$I_f(z)=z\int_0^1f(tz)\,dt.$$
\end{definition}
-/

@[blueprint "LogOfAnalyticFunction"
  (title := "LogOfAnalyticFunction")
  (statement := /--
    Let $0<r<R$. Let $B:\overline{\mathbb{D}_{R}}\to\mathbb{C}$ be analytic on neighborhoods of
    points in $\overline{\mathbb{D}_{R}}$ with $B(z)\neq 0$ for all
    $z\in\overline{\mathbb{D}_{R}}$.Then there exists $J_B:\mathbb{D}_R\to\mathbb{C}$ that is
    analytic on neighborhoods of points in $\mathbb{D}_R$ such that
    \begin{itemize}
        \item $J_B(0)=0$
        \item $J_B'(z)=B'(z)/B(z)$ for all $z\in\overline{\mathbb{D}_r}$
        \item $\log|B(z)|-\log|B(0)|=\mathfrak{R}J_B(z)$ for all $z\in\mathbb{D}_R$.
    \end{itemize}
  -/)
  (proof := /--
    We let $J_B(z)=I_{B'/B}(z)$. Then clearly, $J_B(0)=0$. Now note that
    \begin{align*}
        I_{B'/B}(z)=z\int_0^1(B'/B)(tz)\,dt=\int_0^z(B'/B)(u)\,du.
    \end{align*}
    Thus by the fundamental theorem of calculus we have that $J_B'(z)=B'(z)/B(z)$. Now let
    $H(z)=\exp(J_B(z))/B(z)$ and note that
    $$H'(z)=(B(z)\,J_B'(z)-B'(z))\left(\frac{\exp(J_B(z))}{(B(z))^2}\right).$$
    Thus, $H$ is constant since we know that $B(z)\,J_B'(z)-B(z)=0$ from $J_B'(z)=B'(z)/B(z)$. So
    since $H(0)=\exp(J_B(0))/B(0)=1/B(0)$ we know $H(z)=1/B(0)$ for all $z$. So we have,
    $$\frac{1}{B(0)}=\frac{\exp(J_B(z))}{B(z)}\implies\left|\frac{B(z)}{B(0)}\right|
      =\exp(\mathfrak{R}J_B(z)).$$
    Taking the logarithm of both sides completes the proof.
  -/)
  (latexEnv := "theorem")]
theorem LogOfAnalyticFunction {r R : ℝ} {B : ℂ → ℂ}
    (zero_lt_r : 0 < r) (r_lt_R : r < R)
    (BanalyticOnNhdOfDR : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (Bnonzero : ∀ z ∈ Metric.closedBall (0 : ℂ) R, B z ≠ 0) :
    ∃ (J_B : ℂ → ℂ), (AnalyticOnNhd ℂ J_B (Metric.ball 0 R)) ∧
      (J_B 0 = 0) ∧
      (∀ z ∈ Metric.closedBall 0 r, (deriv J_B) z = (deriv B) z / (B z)) ∧
      (∀ z ∈ Metric.ball 0 R, Real.log ‖B z‖ - Real.log ‖B 0‖ = (J_B z).re) := by
  obtain ⟨J_B, hJB⟩ : ∃ J_B : ℂ → ℂ, (∀ z ∈ Metric.ball 0 R, (HasDerivAt J_B (deriv B z / B z) z)) ∧ J_B 0 = 0 ∧ (∀ z ∈ Metric.ball 0 R, Real.log ‖B z‖ - Real.log ‖B 0‖ = (J_B z).re) := by
    set f : ℂ → ℂ := fun z => deriv B z / B z;
    have hf : AnalyticOnNhd ℂ f (Metric.ball 0 R) :=
      (BanalyticOnNhdOfDR.deriv.mono Metric.ball_subset_closedBall).div
        (BanalyticOnNhdOfDR.mono Metric.ball_subset_closedBall)
        (fun z hz => Bnonzero z <| Metric.ball_subset_closedBall hz)
    obtain ⟨J, hJ⟩ := DifferentiableOn.isExactOn_ball hf.differentiableOn
    refine ⟨fun z ↦ J z - J 0, fun z hz ↦ (hJ z hz).sub_const _, by simp, ?_⟩
    set H : ℂ → ℂ := fun z => Complex.exp (J z - J 0) / B z
    have hJB_deriv : ∀ z ∈ Metric.ball 0 R, HasDerivAt (fun z ↦ J z - J 0) (f z) z :=
      fun z hz ↦ (hJ z hz).sub_const _
    have hH_deriv : ∀ z ∈ Metric.ball 0 R, HasDerivAt H 0 z := by
      intro z hz
      have := (Complex.hasDerivAt_exp _).comp z (hJB_deriv z hz)
      convert! this.div (BanalyticOnNhdOfDR.differentiableOn.differentiableAt
        (Metric.closedBall_mem_nhds_of_mem hz) |>.hasDerivAt)
        (Bnonzero z <| Metric.ball_subset_closedBall hz) using 1
      ring_nf!; grind
    have hH_const : ∀ z ∈ Metric.ball 0 R, H z = H 0 := by
      intro z hz
      have h_diffOn : DifferentiableOn ℂ H (Metric.ball 0 R) :=
        fun z hz ↦ (hH_deriv z hz).differentiableAt.differentiableWithinAt
      refine Convex.is_const_of_fderivWithin_eq_zero (convex_ball 0 R) h_diffOn ?_ hz
        (Metric.mem_ball_self (Metric.pos_of_mem_ball hz))
      intro x hx
      rw [fderivWithin_of_isOpen Metric.isOpen_ball hx,
        ← ContinuousLinearMap.toSpanSingleton_zero]
      exact (hH_deriv x hx).hasFDerivAt.fderiv
    have h_exp_re : ∀ z ∈ Metric.ball 0 R, Real.exp (J z - J 0).re = ‖B z‖ / ‖B 0‖ := by
      intro z hz
      have hc := hH_const z hz
      simp only [H, sub_self, Complex.exp_zero, one_div] at hc
      rw [div_eq_iff (Bnonzero z (Metric.ball_subset_closedBall hz)), mul_comm] at hc
      rw [← Complex.norm_exp, ← norm_div, div_eq_mul_inv]
      exact enorm_eq_iff_norm_eq.mp (congrArg enorm hc)
    intro z hz
    have hBz := Bnonzero z (Metric.ball_subset_closedBall hz)
    have hB0 := Bnonzero 0 (by norm_num; linarith)
    rw [← Real.log_div (norm_ne_zero_iff.mpr hBz) (norm_ne_zero_iff.mpr hB0),
      ← h_exp_re z hz, Real.log_exp]
  have hmem : ∀ z, z ∈ Metric.ball (0 : ℂ) r → z ∈ Metric.closedBall (0 : ℂ) R := by
    intro z hz
    apply Metric.mem_closedBall.mpr
    rw [Metric.mem_ball] at hz
    linarith
  refine ⟨J_B, ?_, hJB.2.1, ?_, hJB.2.2⟩
  · intro z hz
    exact DifferentiableOn.analyticAt (fun w hw ↦ (hJB.1 w hw).differentiableAt.differentiableWithinAt) (IsOpen.mem_nhds Metric.isOpen_ball hz)
  · intro z hz
    exact (hJB.1 z (Metric.closedBall_subset_ball r_lt_R hz)).deriv

@[blueprint "LogOfAnalyticFunction'"
  (title := "LogOfAnalyticFunction'")
  (statement := /--
    A wrapper of the above theorem that will be useful later on.
  -/)
  (proof := /--
    See above.
  -/)
  (latexEnv := "theorem")]
theorem LogOfAnalyticFunction' {r' r R : ℝ} {B : ℂ → ℂ}
    (r'_pos : 0 < r') (r'_lt_r : r' < r) (r_lt_R : r < R)
    (BanalyticOnNhdOfDR : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (Bnonzero : ∀ z ∈ Metric.closedBall (0 : ℂ) r, B z ≠ 0) :
    ∃ (J_B : ℂ → ℂ), (AnalyticOnNhd ℂ J_B (Metric.ball 0 r)) ∧
      (J_B 0 = 0) ∧
      (∀ z ∈ Metric.closedBall 0 r', (deriv J_B) z = (deriv B) z / (B z)) ∧
      (∀ z ∈ Metric.ball 0 r, Real.log ‖B z‖ - Real.log ‖B 0‖ = (J_B z).re) := by
  have BanalyticOnNhdOfDr : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) r) := BanalyticOnNhdOfDR.mono (Metric.closedBall_subset_closedBall r_lt_R.le)
  exact LogOfAnalyticFunction r'_pos r'_lt_r BanalyticOnNhdOfDr Bnonzero

@[blueprint "SetOfZeros"
  (title := "SetOfZeros")
  (statement := /--
    Let $R>0$ and $f:\mathbb{C}\to\mathbb{C}$. Define the set of zeros
    $\mathcal{K}_f(R)=\{\rho\in\mathbb{C}:|\rho|\leq R,\,f(\rho)=0\}$.
  -/)]
def SetOfZeros (R : ℝ) (f : ℂ → ℂ) : Set ℂ := {ρ : ℂ | ‖ρ‖ ≤ R ∧ f ρ = 0}

lemma finiteSetOfZeros_mono {r : ℝ} {f : ℂ → ℂ}
    (r_lt_one : r < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite) :
    (SetOfZeros r f).Finite := by
  apply Set.Finite.subset finiteZeros
  unfold SetOfZeros
  refine ofPred_subset_ofPred.mpr ?_
  intro z hz
  exact ⟨by linarith, hz.2⟩

blueprint_comment /--
\begin{definition}[ZeroOrder]\label{ZeroOrder}
  Let $f:\mathbb{C}\to\mathbb{C}$.
  We define $m_f(\rho)$ as the order of the zero $\rho$ w.r.t $f$.
\end{definition}
  In LEAN, this corresponds exactly with analyticOrderAt/analyticOrderNatAt.
-/

open Classical
@[blueprint "ZeroFactor"
  (title := "ZeroFactor")
  (statement := /--
    Let $f:\mathbb{C}\to\mathbb{C}$ and $\rho\in\mathbb{C}$. Then there exists $h_\rho$ such that
    $$f(z)=(z-\rho)^{m_f(\rho)}\,h_\rho(z).$$
    In LEAN, this corresponds exactly with (-.analyticOrderAt-ne-top.mp -).choose,
    but this serves as a wrapper of that with the necessary conditions.
  -/)]
noncomputable def ZeroFactor (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if h1 : AnalyticAt ℂ f z then
    if h2 : analyticOrderAt f z ≠ ⊤ then
      (h1.analyticOrderAt_ne_top.mp h2).choose z
    else 0
  else 0

@[blueprint "ZeroFactorization"
  (title := "ZeroFactorization")
  (statement := /--
    Let $f:\mathbb{C}\to\mathbb{C}$ be analytic on $\overline{\mathbb{D}_1}$ with $f(0)\neq 0$.
    For all $\rho\in\mathcal{K}_f(R)$ with $R<1$ there exists $h_\rho(z)$ such that
    $h_\rho(z)$ is analytic at $\rho$, $h_\rho(\rho)\neq 0$, and
    $f(z)=(z-\rho)^{m_f(\rho)}\,h_\rho(z)$.
  -/)
  (proof := /--
    Since $f$ is analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ we know
    that there exists a series expansion about $\rho$:
    $$f(z)=\sum_{0\leq n}a_n\,(z-\rho)^n.$$
    Now if we let $m$ be the smallest number such that $a_m\neq 0$, then
    $$f(z)=\sum_{0\leq n}a_n\,(z-\rho)^n=\sum_{m\leq n}a_n\,(z-\rho)^n
      =(z-\rho)^m\sum_{m\leq n}a_n\,(z-\rho)^{n-m}=(z-\rho)^m\,h_\rho(z).$$
    Trivially, $h_\rho(z)$ is analytic at $\rho$ (we have written down the series
    expansion); now note that
    $$h_\rho(\rho)=\sum_{m\leq n}a_n(\rho-\rho)^{n-m}=\sum_{m\leq n}a_n0^{n-m}=a_m\neq 0.$$
  -/)
  (latexEnv := "lemma")]
lemma ZeroFactorization {R : ℝ} {f : ℂ → ℂ} {ρ : ℂ}
    (RleOne : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0)
    (hρ : ρ ∈ SetOfZeros R f) :
    ∃ h_ρ : ℂ → ℂ, AnalyticAt ℂ h_ρ ρ ∧ h_ρ ρ ≠ 0 ∧ ZeroFactor f ρ = h_ρ ρ ∧
      f =ᶠ[nhds ρ] fun z ↦ (z - ρ) ^ analyticOrderNatAt f ρ * h_ρ z := by
  have zero_mem_closedBall : 0 ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw[mem_closedBall_iff_norm, sub_zero, norm_zero]
    exact zero_le_one
  have ρ_mem_closedBall : ρ ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw[mem_closedBall_iff_norm, sub_zero]
    linarith[hρ.1]
  have orderAtZeroIsZero : analyticOrderAt f 0 = 0 := by
    rw[analyticOrderAt_eq_zero]
    exact Or.symm (Decidable.not_or_of_imp fun a a_1 ↦ hf_neq_zero_at_zero a)
  have finiteOrder : analyticOrderAt f ρ ≠ ⊤ := by
    refine AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected hfAnalytic (Metric.isPreconnected_closedBall) zero_mem_closedBall ρ_mem_closedBall (lt_top_iff_ne_top.mp ?_)
    rw[orderAtZeroIsZero]
    exact ENat.top_pos
  have AnalyticAt_ρ : AnalyticAt ℂ f ρ := by exact (hfAnalytic ρ ρ_mem_closedBall)
  obtain ⟨h_ρ, h_ρ_neq_zero_at_zero, f_eq⟩ := (AnalyticAt_ρ.analyticOrderAt_ne_top.mp finiteOrder).choose_spec
  set g := (AnalyticAt_ρ.analyticOrderAt_ne_top.mp finiteOrder).choose
  refine ⟨g, h_ρ, h_ρ_neq_zero_at_zero, ?_, f_eq⟩
  simp only [ZeroFactor, AnalyticAt_ρ, ↓reduceDIte, ne_eq, finiteOrder, not_false_eq_true,
    smul_eq_mul, g]

@[blueprint "CFunction"
  (title := "CFunction")
  (statement := /--
    Let $0 < r < 1$, and $f:\mathbb{C}\to\mathbb{C}$ be analytic on $\overline{\mathbb{D}_1}$ with
    $f(0)\neq 0$. We define a function $C_f:\mathbb{C}\to\mathbb{C}$ as follows. This function is
    constructed by dividing $f(z)$ by a polynomial whose roots are the zeros of $f$ inside
    $\overline{\mathbb{D}_r}$.
    $$C_f(z)=\begin{cases}
        \displaystyle\frac{f(z)}{\prod_{\rho\in\mathcal{K}_f(r)}(z-\rho)^{m_f(\rho)}}
          \qquad\text{for }z\not\in\mathcal{K}_f(r) \\
        \displaystyle\frac{h_z(z)}{\prod_{\rho\in\mathcal{K}_f(r)\setminus\{z\}}
          (z-\rho)^{m_f(\rho)}}\qquad\text{for }z\in\mathcal{K}_f(r)
    \end{cases}$$
    where $h_z(z)$ comes from Lemma \ref{ZeroFactorization}.
  -/)]
noncomputable def Cf (r : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if finite_zeros_mono : (SetOfZeros r f).Finite then
    if _ : z ∈ SetOfZeros r f then
      ZeroFactor f z / ∏ ρ ∈ (finite_zeros_mono.toFinset \ {z}), (z - ρ) ^ (analyticOrderNatAt f ρ)
    else
      f z / ∏ ρ ∈ (finite_zeros_mono.toFinset), (z - ρ) ^ (analyticOrderNatAt f ρ)
  else 1

lemma analyticAt_finset_prod_sub_pow (s : Finset ℂ) (g : ℂ → ℕ) (w : ℂ) :
    AnalyticAt ℂ (fun z => ∏ ρ ∈ s, (z - ρ) ^ g ρ) w := by
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty]
    exact analyticAt_const
  | @insert a s' hne ih =>
    have : (fun z => ∏ ρ ∈ insert a s', (z - ρ) ^ g ρ) = fun z => (z - a) ^ g a * ∏ ρ ∈ s', (z - ρ) ^ g ρ :=
      funext fun z => Finset.prod_insert hne
    rw [this]
    exact ((analyticAt_id.sub analyticAt_const).pow _).mul ih

@[blueprint "CfAnalytic"
  (title := "CfAnalytic")
  (statement := /--
    If $f:\mathbb{C}\to\mathbb{C}$ is analytic on $\overline{\mathbb{D}_1}$ then so too is $C_f$.
  -/)
  (proof := /--
    Look at the definition of $C_f$ and apply ZeroFactorization.
  -/)
  (latexEnv := "lemma")]
lemma CfAnalytic {r R : ℝ} {f : ℂ → ℂ}
    (r_lt_R : r < R) (R_lt_one : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    AnalyticOnNhd ℂ (Cf r f) (Metric.closedBall (0 : ℂ) R) := by
  intro w hw
  unfold Cf
  by_cases finite_zeros_mono : (SetOfZeros r f).Finite
  · simp only [finite_zeros_mono, ↓reduceDIte]
    by_cases w_in_zeros : w ∈ SetOfZeros r f
    · obtain ⟨h_w, hh_w_analytic, hh_w_w_ne_zero, hh_w_eq⟩ := ZeroFactorization (by linarith) (hfAnalytic.mono (Metric.closedBall_subset_closedBall (by linarith))) hf_neq_zero_at_zero w_in_zeros;
      have h_eq : ∀ᶠ z in nhds w, (if h : z ∈ SetOfZeros r f then ZeroFactor f z / ∏ ρ ∈ finite_zeros_mono.toFinset \ {z}, (z - ρ) ^ analyticOrderNatAt f ρ else f z / ∏ ρ ∈ finite_zeros_mono.toFinset, (z - ρ) ^ analyticOrderNatAt f ρ) = h_w z / ∏ ρ ∈ finite_zeros_mono.toFinset \ {w}, (z - ρ) ^ analyticOrderNatAt f ρ := by
        filter_upwards [ hh_w_eq.2, hh_w_analytic.continuousAt.eventually_ne hh_w_w_ne_zero ] with z hz hz';
        by_cases h : z = w
        · subst h
          rw [dif_pos w_in_zeros]
          congr 1
          exact hh_w_eq.1
        · have z_not_in : z ∉ SetOfZeros r f := by
            intro hmem
            have hfz : f z = 0 := hmem.2
            rw [hz] at hfz
            exact absurd hfz (mul_ne_zero (pow_ne_zero _ (sub_ne_zero_of_ne h)) hz')
          rw [dif_neg z_not_in, hz]
          have hw_mem : w ∈ finite_zeros_mono.toFinset := finite_zeros_mono.mem_toFinset.mpr w_in_zeros
          rw [Finset.prod_eq_prod_sdiff_singleton_mul hw_mem (fun ρ => (z - ρ) ^ analyticOrderNatAt f ρ)]
          rw [mul_comm ((z - w) ^ analyticOrderNatAt f w) (h_w z)]
          rw [mul_div_mul_right _ _ (pow_ne_zero _ (sub_ne_zero_of_ne h))]
      apply hh_w_analytic.div _ _ |> fun h => h.congr _;
      · use fun z => ∏ ρ ∈ finite_zeros_mono.toFinset \ { w }, ( z - ρ ) ^ analyticOrderNatAt f ρ;
      · exact analyticAt_finset_prod_sub_pow _ _ _
      · simp only [Finset.prod_eq_zero_iff, ne_eq, pow_eq_zero_iff', Finset.mem_sdiff, Finite.mem_toFinset, Finset.mem_singleton, not_exists, not_and,
          Decidable.not_not, and_imp]
        intro x _ h_ne_w
        exact fun h_eq_w => absurd (sub_eq_zero.mp h_eq_w).symm h_ne_w
      · filter_upwards [ h_eq ] with z hz using hz.symm
    · apply AnalyticAt.congr _ _
      · exact fun z => f z / ∏ ρ ∈ finite_zeros_mono.toFinset, ( z - ρ ) ^ analyticOrderNatAt f ρ
      · refine AnalyticAt.div ?_ ?_ ?_
        · exact hfAnalytic w ( Metric.mem_closedBall.mpr <| le_trans hw.out <| by linarith )
        · exact analyticAt_finset_prod_sub_pow _ _ _
        · simp only [ ne_eq, Finset.prod_eq_zero_iff, Finite.mem_toFinset, pow_eq_zero_iff',
          sub_eq_zero, ↓existsAndEq, true_and, not_and, Decidable.not_not]
          exact fun h => absurd h w_in_zeros
      · filter_upwards [ IsOpen.mem_nhds ( isOpen_compl_iff.mpr finite_zeros_mono.isClosed ) w_in_zeros ] with z hz
        split_ifs with h
        · exact absurd h hz
        · rfl
  · simp only [finite_zeros_mono, ↓reduceDIte]
    exact analyticAt_const

@[blueprint "BlaschkeB"
  (title := "BlaschkeB")
  (statement := /--
    Let $0 < r < R < 1$, and $f:\mathbb{C}\to\mathbb{C}$ be analytic $\overline{\mathbb{D}_1}$ with
    $f(0)\neq 0$. We define a function $B_f:\mathbb{C}\to\mathbb{C}$ as follows.
    $$B_f(z)=C_f(z)\prod_{\rho\in\mathcal{K}_f(r)}
      \left(R-\frac{z\overline{\rho}}{R}\right)^{m_f(\rho)}$$
  -/)]
noncomputable def BlaschkeB (r R : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if finite_zeros_mono : (SetOfZeros r f).Finite then
    (Cf r f) z * (∏ ρ ∈ finite_zeros_mono.toFinset, (R - z * (conj ρ) / R) ^ (analyticOrderNatAt f ρ))
  else 1

@[blueprint "BlaschkeAnalytic"
  (title := "BlaschkeAnalytic")
  (statement := /--
    If $f:\mathbb{C}\to\mathbb{C}$ is analytic on $\overline{\mathbb{D}_R}$ then so too is $B_f$.
  -/)
  (proof := /--
    Expand out $B_f$ as a product, and observe that each part is analytic on $\overline{\mathbb{D}_R}$.
  -/)
  (latexEnv := "lemma")]
lemma BlaschkeAnalytic {r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_R : r < R) (R_lt_one : R < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    AnalyticOnNhd ℂ (BlaschkeB r R f) (Metric.closedBall (0 : ℂ) R) := by
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  have r_lt_one : r < 1 := lt_trans r_lt_R R_lt_one
  unfold BlaschkeB
  by_cases finite_zeros_mono : (SetOfZeros r f).Finite
  · simp only [finite_zeros_mono, ↓reduceDIte]
    refine AnalyticOnNhd.mul (CfAnalytic r_lt_R R_lt_one hfAnalytic hf_neq_zero_at_zero) (Finset.analyticOnNhd_fun_prod (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset ?_)
    intro w hw
    refine AnalyticOnNhd.fun_pow (AnalyticOnNhd.sub (analyticOnNhd_const) (AnalyticOnNhd.div (AnalyticOnNhd.mul (analyticOnNhd_id) (analyticOnNhd_const)) (analyticOnNhd_const) ?_)) (analyticOrderAt f w).toNat
    intro w' hw'
    exact_mod_cast ne_of_gt R_pos
  · simp only [finite_zeros_mono, ↓reduceDIte]
    exact analyticOnNhd_const

@[blueprint "BlaschkeOfZero"
  (title := "BlaschkeOfZero")
  (statement := /--
    Let $0 < r < R<1$, and $f:\mathbb{C}\to\mathbb{C}$ be analytic on $\overline{\mathbb{D}_1}$ with
    $f(0)\neq 0$. Then
    $$|B_f(0)|=|f(0)|\prod_{\rho\in\mathcal{K}_f(r)}
      \left(\frac{R}{|\rho|}\right)^{m_f(\rho)}.$$
  -/)
  (proof := /--
    Since $f(0)\neq 0$, we know that $0\not\in\mathcal{K}_f(r)$. Thus,
    $$C_f(0)=\frac{f(0)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)}(-\rho)^{m_f(\rho)}}.$$
    Thus, substituting this into Definition \ref{BlaschkeB},
    $$|B_f(0)|=|C_f(0)|\prod_{\rho\in\mathcal{K}_f(r)}R^{m_f(\rho)}
      =|f(0)|\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{|\rho|}\right)^{m_f(\rho)}.$$
  -/)
  (latexEnv := "lemma")]
lemma BlaschkeOfZero {r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_one : r < 1) (r_lt_R : r < R)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    ‖BlaschkeB r R f 0‖ =
      ‖f 0‖ * (∏ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, (R / ‖ρ‖) ^ (analyticOrderNatAt f ρ)) := by
  have zero_not_zero : ¬(0 ∈ SetOfZeros r f) := by
    apply notMem_ofPred_iff.mpr
    simp only [norm_zero, not_and]
    intro r
    exact mem_support.mp hf_neq_zero_at_zero
  unfold BlaschkeB Cf
  simp only [finiteSetOfZeros_mono r_lt_one finiteZeros, zero_not_zero, ↓reduceDIte, zero_sub, zero_mul, zero_div, sub_zero,
    Complex.norm_mul, Complex.norm_div, norm_prod, norm_pow, norm_neg, norm_real, norm_eq_abs]
  rw[div_eq_mul_inv, mul_assoc, abs_of_pos (by linarith)]
  refine (mul_right_inj' (norm_ne_zero_iff.mpr hf_neq_zero_at_zero)).mpr ?_
  rw[← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  simp only [div_eq_inv_mul, mul_pow, inv_pow]

@[blueprint "norm_fOfZero_le_norm_BlaschkeOfZero"
  (title := "norm-fOfZero-le-norm-BlaschkeOfZero")
  (statement := /--
    Let $0 < r < R<1$, and $f:\mathbb{C}\to\mathbb{C}$ be analytic on $\overline{\mathbb{D}_1}$ with
    $f(0)\neq 0$. Then
    $$|f(0)|\leq|B_f(0)|.$$
  -/)
  (proof := /--
    Applying lemma \ref{BlaschkeOfZero} we know that
    $$|B_f(0)|=|f(0)|\prod_{\rho\in\mathcal{K}_f(r)}
      \left(\frac{R}{|\rho|}\right)^{m_f(\rho)}.$$
    Note that for all $\rho\in\mathcal{K}_f(r)$ that $1<R/|\rho|$ since $r<R$.
    Thus, the result follows.
  -/)
  (latexEnv := "lemma")]
lemma norm_fOfZero_le_norm_BlaschkeOfZero {r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_R : r < R) (R_lt_one : R < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    ‖f 0‖ ≤ ‖BlaschkeB r R f 0‖ := by
  have r_lt_one : r < 1 := lt_trans r_lt_R R_lt_one
  rw [BlaschkeOfZero r_pos r_lt_one r_lt_R finiteZeros hf_neq_zero_at_zero, ← mul_one ‖f 0‖]
  refine mul_le_mul (by rw[mul_one]) ?_ (zero_le_one) (mul_nonneg (norm_nonneg (f 0)) zero_le_one)
  rw [← Finset.prod_const_one (s := (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset)]
  apply Finset.prod_le_prod
  · intro ρ hρ
    exact zero_le_one
  · intro ρ hρ
    simp only [SetOfZeros, Finite.mem_toFinset, mem_ofPred_eq] at hρ
    apply one_le_pow₀
    rw[one_le_div]
    · linarith
    · rw [norm_pos_iff]
      by_contra h
      rw [h] at hρ
      exact hf_neq_zero_at_zero hρ.2

@[blueprint "DiskBound"
  (title := "DiskBound")
  (statement := /--
    Let $0 < r < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic on
    $\overline{\mathbb{D}_1}$ with $f(0)\neq0$ such that $|f(z)|\leq B$ for $|z|\leq R$,
    then $|B_f(z)|\leq B$ for $|z|\leq R$ also.
  -/)
  (proof := /--
    For $|z|=R$, we know that $z\not\in\mathcal{K}_f(r)$. Thus,
    $$C_f(z)=\frac{f(z)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)}(z-\rho)^{m_f(\rho)}}.$$
    Thus, substituting this into Definition \ref{BlaschkeB},
    $$|B_f(z)|=|f(z)|\prod_{\rho\in\mathcal{K}_f(r)}
      \left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|^{m_f(\rho)}.$$
    But note that
    $$\left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|
      =\frac{|R^2-z\overline{\rho}|/R}{|z-\rho|}
      =\frac{|z|\cdot|\overline{z-\rho}|/R}{|z-\rho|}=1.$$
    So we have that $|B_f(z)|=|f(z)|\leq B$ when $|z|=R$. Now by the maximum modulus
    principle, we know that the maximum of $|B_f|$ must occur on the boundary where
    $|z|=R$. Thus $|B_f(z)|\leq B$ for all $|z|\leq R$.
  -/)
  (latexEnv := "lemma")]
lemma DiskBound {B r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (r_pos : 0 < r) (r_lt_R : r < R) (R_lt_one : R < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0) (fz_bound : ∀ (z : ℂ), ‖z‖ ≤ R → ‖f z‖ ≤ B)
    (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
    ‖BlaschkeB r R f z‖ ≤ B := by
  have r_lt_one : r < 1 := lt_trans r_lt_R R_lt_one
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  refine AnalyticOn.norm_le_of_norm_le_on_sphere (Std.IsPreorder.le_refl R) (AnalyticOnNhd.analyticOn (BlaschkeAnalytic r_pos r_lt_R R_lt_one finiteZeros hfAnalytic hf_neq_zero_at_zero)) ?_ hz
  intro w hw
  rw[mem_sphere_iff_norm, sub_zero] at hw
  have hw_not_in : ¬(w ∈ SetOfZeros r f) := by
    apply notMem_ofPred_iff.mpr
    intro le_r
    linarith
  have Bf_eq_f_at_w : ‖BlaschkeB r R f w‖ = ‖f w‖ := by
    unfold BlaschkeB Cf
    simp only [finiteSetOfZeros_mono r_lt_one finiteZeros, hw_not_in, ↓reduceDIte, Complex.norm_mul, Complex.norm_div, norm_prod, norm_pow]
    rw[div_eq_mul_inv, mul_assoc, mul_right_eq_self₀]
    by_cases fw_normZero : ‖f w‖ = 0
    · exact Or.inr fw_normZero
    · apply Or.inl
      rw[← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_eq_one
      intro w' hw'_in
      have hfact : (R : ℂ) - w * starRingEnd ℂ w' / R = (conj w - conj w') * w / R := by
        rw[sub_mul, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hw, ofReal_pow]
        field_simp
      rw [hfact, norm_div, norm_mul, ← map_sub, norm_conj, Complex.norm_real, hw, Real.norm_of_nonneg (le_of_lt R_pos)]
      field_simp
      rw[← div_pow, div_self, one_pow]
      rw[Set.Finite.mem_toFinset] at hw'_in
      exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (fun h => hw_not_in (h ▸ hw'_in)))
  rw[Bf_eq_f_at_w]
  exact fz_bound w (le_of_eq hw)

@[blueprint "BlaschkeNonZero"
  (title := "BlaschkeNonZero")
  (statement := /--
    Let $0 < r < R<1$ and $f:\overline{\mathbb{D}_1}\to\mathbb{C}$ be analytic on
    neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)\neq 0$. Then $B_f(z)\neq 0$
    for all $z\in\overline{\mathbb{D}_r}$.
  -/)
  (proof := /--
    Suppose that $z\in\mathcal{K}_f(r)$. Then we have that
    $$C_f(z)=\frac{h_z(z)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)\setminus\{z\}}
      (z-\rho)^{m_f(\rho)}}.$$
    where $h_z(z)\neq 0$ according to Lemma \ref{ZeroFactorization}. Thus, substituting
    this into Definition \ref{BlaschkeB},
    \begin{equation}\label{pickupPoint2}
        |B_f(z)|=|h_z(z)|\cdot\left|R-\frac{|z|^2}{R}\right|^{m_f(z)}
          \prod_{\rho\in\mathcal{K}_f(r)\setminus\{z\}}
          \left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|^{m_f(\rho)}.
    \end{equation}
    Trivially, $|h_z(z)|\neq 0$. Now note that
    $$\left|R-\frac{|z|^2}{R}\right|=0\implies|z|=R.$$
    However, this is a contradiction because $z\in\overline{\mathbb{D}_r}$ tells us that
    $|z|\leq r < R$. Similarly, note that
    $$\left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|=0\implies|z|=\frac{R^2}{|\overline{\rho}|}.$$
    However, this is also a contradiction because $\rho\in\mathcal{K}_f(r)$ tells us that
    $R < R^2/|\overline{\rho}|=|z|$, but $z\in\overline{\mathbb{D}_r}$ tells us that
    $|z|\leq r < R$. So, we know that
    $$\left|R-\frac{|z|^2}{R}\right|\neq 0\qquad\text{and}\qquad
      \left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|\neq 0
      \quad\text{for all}\quad\rho\in\mathcal{K}_f(r)\setminus\{z\}.$$
    Applying this to Equation (\ref{pickupPoint2}) we have that $|B_f(z)|\neq 0$.
    So, $B_f(z)\neq 0$.

    Now suppose that $z\not\in\mathcal{K}_f(r)$. Then we have that
    $$C_f(z)=\frac{f(z)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)}(z-\rho)^{m_f(\rho)}}.$$
    Thus, substituting this into Definition \ref{BlaschkeB},
    \begin{equation}\label{pickupPoint3}
        |B_f(z)|=|f(z)|\prod_{\rho\in\mathcal{K}_f(r)}
          \left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|^{m_f(\rho)}.
    \end{equation}
    We know that $|f(z)|\neq 0$ since $z\not\in\mathcal{K}_f(r)$. Now note that
    $$\left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|=0\implies|z|=\frac{R^2}{|\overline{\rho}|}.$$
    However, this is a contradiction because $\rho\in\mathcal{K}_f(r)$ tells us that
    $R < R^2/|\overline{\rho}|=|z|$, but $z\in\overline{\mathbb{D}_r}$ tells us that
    $|z|\leq r < R$. So, we know that
    $$\left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|\neq 0
      \quad\text{for all}\quad\rho\in\mathcal{K}_f(r).$$
    Applying this to Equation (\ref{pickupPoint3}) we have that $|B_f(z)|\neq 0$.
    So, $B_f(z)\neq 0$.

    We have shown that $B_f(z)\neq 0$ for both $z\in\mathcal{K}_f(r)$ and
    $z\not\in\mathcal{K}_f(r)$, so the result follows.
  -/)
  (latexEnv := "lemma")]
lemma BlaschkeNonzero {r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_R : r < R) (R_lt_one : R < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r, BlaschkeB r R f z ≠ 0 := by
  have r_lt_one : r < 1 := lt_trans r_lt_R R_lt_one
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  intro z hz
  have hz_norm_le_r : ‖z‖ ≤ r := by rwa [mem_closedBall_iff_norm, sub_zero] at hz
  have hz_norm_lt_R : ‖z‖ < R := by linarith
  let hFin := finiteSetOfZeros_mono r_lt_one finiteZeros
  have hBProd : ∏ ρ ∈ hFin.toFinset,
      (↑R - z * (starRingEnd ℂ) ρ / ↑R) ^ analyticOrderNatAt f ρ ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro ρ hρ
    apply pow_ne_zero
    norm_num [ sub_eq_zero, Complex.ext_iff ];
    simp only [SetOfZeros, Finite.mem_toFinset, mem_ofPred_eq] at hρ
    rw [ eq_div_iff ] <;> norm_num [ Complex.normSq, Complex.norm_def ] at *;
    · rw [Real.sqrt_lt' (by linarith)] at hz_norm_lt_R
      rw [ Real.sqrt_le_iff ] at hρ
      exact fun h => absurd h ( by nlinarith [ sq_nonneg ( z.re - ρ.re ), sq_nonneg ( z.im - ρ.im ), mul_lt_mul_of_pos_left r_lt_R R_pos ] )
    · linarith
  unfold BlaschkeB Cf
  by_cases z_in_zeros : z ∈ SetOfZeros r f
  · simp only [hFin, z_in_zeros, ↓reduceDIte]
    obtain ⟨_, _, hne, heq⟩ :=
      ZeroFactorization (by linarith) (hfAnalytic.mono (Metric.closedBall_subset_closedBall (by linarith)))
        hf_neq_zero_at_zero z_in_zeros
    rw [heq.1]
    refine mul_ne_zero (div_ne_zero hne (Finset.prod_ne_zero_iff.mpr fun ρ hρ =>
      pow_ne_zero _ (sub_ne_zero.mpr fun h =>
        (Finset.mem_sdiff.mp hρ).2 (Finset.mem_singleton.mpr h.symm)))) hBProd
  · simp only [hFin, z_in_zeros, ↓reduceDIte]
    refine mul_ne_zero (div_ne_zero (fun hfz => z_in_zeros ⟨hz_norm_le_r, hfz⟩)
      (Finset.prod_ne_zero_iff.mpr fun ρ hρ =>
        pow_ne_zero _ (sub_ne_zero.mpr fun h => z_in_zeros (h ▸ hFin.mem_toFinset.mp hρ)))) hBProd

@[blueprint "ZerosBound"
  (title := "ZerosBound")
  (statement := /--
    Let $0< r < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic on
    neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)=1$ and $|f(z)|\leq B$
    for $|z|\leq R$, then
    $$\sum_{\rho\in\mathcal{K}_f(r)}m_f(\rho)\leq\frac{\log B}{\log(R/r)}.$$
  -/)
   (proof := /--
    Since $f(0)=1$, by Lemma \ref{BlaschkeOfZero} we know that
    $$|B_f(0)|
      =|f(0)|\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{|\rho|}\right)^{m_f(\rho)}
      =\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{|\rho|}\right)^{m_f(\rho)}.$$
    Thus, substituting this into Definition \ref{BlaschkeB},
    $$(R/r)^{\sum_{\rho\in\mathcal{K}_f(r)}m_f(\rho)}
      =\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{r}\right)^{m_f(\rho)}
      \leq\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{|\rho|}\right)^{m_f(\rho)}
      =|B_f(0)|\leq B$$
    whereby Lemma \ref{DiskBound} we know that $|B_f(z)|\leq B$ for all $|z|\leq R$.
    Taking the logarithm of both sides and rearranging gives the desired result.
  -/)
  (latexEnv := "theorem")]
theorem ZerosBound {B r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_one : r < 1) (r_lt_R : r < R) (R_lt_one : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0_eq_one : f 0 = 1)
    (finiteZeros : (SetOfZeros 1 f).Finite) (fz_bound : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, analyticOrderNatAt f ρ ≤
      1 / Real.log (R / r) * Real.log B := by
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  have hf0_ne_zero : f 0 ≠ 0 := by rw [hf0_eq_one]; exact one_ne_zero
  have blaschke_eq := BlaschkeOfZero r_pos r_lt_one r_lt_R finiteZeros hf0_ne_zero
  rw[hf0_eq_one, norm_one, one_mul] at blaschke_eq
  rw [one_div, inv_mul_eq_div, le_div_iff₀ (Real.log_pos (by simp only [lt_div_iff₀ r_pos, one_mul, r_lt_R])), ← Real.log_pow]
  refine Real.log_le_log (pow_pos (div_pos R_pos r_pos) _) ?_
  calc (R / r) ^ ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, analyticOrderNatAt f ρ
      = ∏ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, (R / r) ^ analyticOrderNatAt f ρ := by
        rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ ∏ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, (R / ‖ρ‖) ^ analyticOrderNatAt f ρ := by
      apply Finset.prod_le_prod
      · intro ρ _
        exact pow_nonneg (div_nonneg (le_of_lt R_pos) (le_of_lt r_pos)) _
      · intro ρ hρ
        have hρ_mem := (finiteSetOfZeros_mono r_lt_one finiteZeros).mem_toFinset.mp hρ
        refine pow_le_pow_left₀ (div_nonneg (le_of_lt R_pos) (le_of_lt r_pos)) ?_ _
        refine div_le_div_of_nonneg_left (le_of_lt R_pos) (norm_pos_iff.mpr ?_) (hρ_mem.1)
        rintro rfl
        exact hf0_ne_zero hρ_mem.2
    _ ≤ B := by
      rw[← blaschke_eq]
      exact DiskBound r_pos r_lt_R R_lt_one finiteZeros hfAnalytic
        hf0_ne_zero fz_bound (Metric.mem_closedBall_self (le_of_lt R_pos))

@[blueprint "JBlaschke"
  (title := "JBlaschke")
  (statement := /--
    Let $0 < r < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic on
    neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)=1$, define
    $L_f(z)=J_{B_f}(z)$ where $J$ is from Theorem \ref{LogOfAnalyticFunction} and $B_f$
    is from Definition \ref{BlaschkeB}.
  -/)]
noncomputable def JBlaschke {r' r R : ℝ} {f : ℂ → ℂ}
  (r'_pos : 0 < r') (r'_lt_r : r' < r) (r_pos : 0 < r) (r_lt_R : r < R) (R_lt_one : R < 1)
  (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0_eq_one : f 0 = 1)
  (finiteZeros : (SetOfZeros 1 f).Finite)
  (z : ℂ) : ℂ :=
  (LogOfAnalyticFunction' r'_pos r'_lt_r r_lt_R
    (BlaschkeAnalytic r_pos r_lt_R R_lt_one finiteZeros hfAnalytic (hf0_eq_one ▸ one_ne_zero))
    (BlaschkeNonzero r_pos r_lt_R R_lt_one finiteZeros hfAnalytic (hf0_eq_one ▸ one_ne_zero))).choose z

@[blueprint "JBlaschkeDerivBound"
  (title := "JBlaschkeDerivBound")
  (statement := /--
    Let $B>1$ and $0 < r' < r < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic
    on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)=1$ and $|f(z)|\leq B$
    for all $|z|\leq R$, then for all $|z|\leq r'$
    $$|L_f'(z)|\leq\frac{16\log(B)\,r^2}{(r-r')^3}.$$
  -/)
  (proof := /--
    By Lemma \ref{DiskBound} we immediately know that $|B_f(z)|\leq B$ for all $|z|\leq R$.
    Now since $L_f=J_{B_f}$ by Definition \ref{JBlaschke}, by Theorem
    \ref{LogOfAnalyticFunction} we know that
    $$L_f(0)=0\qquad\text{and}\qquad
      \Re L_f(z)=\log|B_f(z)|-\log|B_f(0)|\leq\log|B_f(z)|\leq\log B$$
    for all $|z|\leq r$. Note that in the above
    $$0=\log|f(0)|\leq\log|B_f(0)|$$
    because of Lemma \ref{norm_fOfZero_le_norm_BlaschkeOfZero}. So by Theorem \ref{BorelCaratheodoryDeriv}, it follows that
    $$|L_f'(z)|\leq\frac{16\log(B)\,r^2}{(r-r')^3}$$
    for all $|z|\leq r'$.
  -/)
  (latexEnv := "theorem")]
theorem JBlaschkeDerivBound {B r' r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (one_lt_B : 1 < B) (r'_pos : 0 < r') (r'_lt_r : r' < r) (r_pos : 0 < r) (r_lt_R : r < R) (R_lt_one : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0_eq_one : f 0 = 1)
    (finiteZeros : (SetOfZeros 1 f).Finite) (fz_bound : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B)
    (hz : z ∈ Metric.closedBall (0 : ℂ) r') :
    ‖deriv (JBlaschke r'_pos r'_lt_r r_pos r_lt_R R_lt_one hfAnalytic hf0_eq_one finiteZeros) z‖
      ≤ 16 * Real.log (B) * r ^ 2 / (r - r') ^ 3 := by
  have r_pos : 0 < r := lt_trans r'_pos r'_lt_r
  let blaschkeAnalytic := BlaschkeAnalytic r_pos r_lt_R R_lt_one finiteZeros hfAnalytic (hf0_eq_one ▸ one_ne_zero)
  let blaschkeNonzero := BlaschkeNonzero r_pos r_lt_R R_lt_one finiteZeros hfAnalytic (hf0_eq_one ▸ one_ne_zero)
  let logOfAnalytic := LogOfAnalyticFunction' r'_pos r'_lt_r r_lt_R blaschkeAnalytic blaschkeNonzero
  set JB := logOfAnalytic.choose with JB_def
  obtain ⟨JB_Analytic, JB_0_eq_0, deriv_JB_eq, JB_re⟩ := logOfAnalytic.choose_spec
  rw [← JB_def] at JB_Analytic JB_0_eq_0 deriv_JB_eq JB_re
  have JB_def' : JB = (JBlaschke r'_pos r'_lt_r r_pos r_lt_R R_lt_one hfAnalytic hf0_eq_one finiteZeros) := by
    unfold JBlaschke
    rw [← JB_def]
  rw[← JB_def']
  refine BorelCaratheodoryDeriv (Real.log_pos one_lt_B) r'_pos r'_lt_r (JB_Analytic.analyticOn) JB_0_eq_0 ?_ hz
  intro w hw
  rw[← JB_re w hw]
  have hwr : w ∈ Metric.closedBall (0 : ℂ) r := by exact Metric.ball_subset_closedBall hw
  have hlog : 0 ≤ Real.log ‖BlaschkeB r R f 0‖ := by
    rw [← Real.log_one]
    apply Real.log_le_log zero_lt_one
    rw [← norm_one (α := ℂ), ← hf0_eq_one]
    exact norm_fOfZero_le_norm_BlaschkeOfZero r_pos r_lt_R R_lt_one finiteZeros (hf0_eq_one ▸ one_ne_zero)
  suffices h : Real.log ‖BlaschkeB r R f w‖ ≤ Real.log B by linarith
  exact Real.log_le_log (norm_pos_iff.mpr (blaschkeNonzero w hwr))
    (DiskBound r_pos r_lt_R R_lt_one finiteZeros hfAnalytic (hf0_eq_one ▸ one_ne_zero) fz_bound (Metric.closedBall_subset_closedBall r_lt_R.le hwr))

@[blueprint "FinalBound"
  (title := "FinalBound")
  (statement := /--
    Let $B>1$ and $0 < r' < r < R' < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function
    analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)=1$ and
    $|f(z)|\leq B$ for all $|z|\leq R$, then for all
    $z\in\overline{\mathbb{D}_{r'}}\setminus\mathcal{K}_f(R')$ we have
    $$\left|\frac{f'}{f}(z)-\sum_{\rho\in\mathcal{K}_f(r)}\frac{m_f(\rho)}{z-\rho}\right|
      \leq\left(\frac{16r^2}{(r-r')^3}+\frac{1}{(R^2/R'-R')\,\log(R/R')}\right)\log B.$$
  -/)
  (proof := /--
    Since $z\in\overline{\mathbb{D}_{r'}}\setminus\mathcal{K}_f(R')$ we know that
    $z\not\in\mathcal{K}_f(R')$; thus, by Definition \ref{CFunction} we know that
    $$C_f(z)=\frac{f(z)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)}(z-\rho)^{m_f(\rho)}}.$$
    Substituting this into Definition \ref{BlaschkeB} we have that
    $$B_f(z)=f(z)\prod_{\rho\in\mathcal{K}_f(r)}
      \left(\frac{R-z\overline{\rho}/R}{z-\rho}\right)^{m_f(\rho)}.$$
    Taking the complex logarithm of both sides we have that
    $$\mathrm{Log}\,B_f(z)=\mathrm{Log}\,f(z)
      +\sum_{\rho\in\mathcal{K}_f(r)}m_f(\rho)\,\mathrm{Log}(R-z\overline{\rho}/R)
      -\sum_{\rho\in\mathcal{K}_f(r)}m_f(\rho)\,\mathrm{Log}(z-\rho).$$
    Taking the derivative of both sides we have that
    $$\frac{B_f'}{B_f}(z)=\frac{f'}{f}(z)
      +\sum_{\rho\in\mathcal{K}_f(r)}\frac{m_f(\rho)}{z-R^2/\overline{\rho}}
      -\sum_{\rho\in\mathcal{K}_f(r)}\frac{m_f(\rho)}{z-\rho}.$$
    By Definition \ref{JBlaschke} and Theorem \ref{LogOfAnalyticFunction},
    since $L_f(z)=J_{B_f}(z)$ we have $L_f'(z)=J'_{B_f}(z)=(B_f'/B_f)(z)$. Thus,
    $$\frac{f'}{f}(z)-\sum_{\rho\in\mathcal{K}_f(r)}\frac{m_f(\rho)}{z-\rho}
      =L_f'(z)-\sum_{\rho\in\mathcal{K}_f(r)}\frac{m_f(\rho)}{z-R^2/\overline{\rho}}.$$
    Now since $z\in\overline{\mathbb{D}_{r'}}\subseteq\overline{\mathbb{D}_{R'}}$ and $\rho\in\mathcal{K}_f(r)\subseteq\mathcal{K}_f(R')$, we know that
    $R^2/R'-R'\leq|z-R^2/\overline{\rho}|$. Thus by the triangle inequality we have
    $$\left|\frac{f'}{f}(z)-\sum_{\rho\in\mathcal{K}_f(r)}\frac{m_f(\rho)}{z-\rho}\right|
      \leq|L_f'(z)|+\left(\frac{1}{R^2/R'-R'}\right)\sum_{\rho\in\mathcal{K}_f(r)}m_f(\rho).$$
    Now by Theorem \ref{ZerosBound} and \ref{JBlaschkeDerivBound} we get our desired result
    with a little algebraic manipulation.
  -/)
  (latexEnv := "theorem")]
theorem FinalBound {B r' r R' R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (one_lt_B : 1 < B) (r'_pos : 0 < r') (r'_lt_r : r' < r) (r_lt_one : r < 1) (r_lt_R' : r < R') (R'_lt_R : R' < R) (R_lt_one : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0_eq_one : f 0 = 1)
    (finiteZeros : (SetOfZeros 1 f).Finite) (fz_bound : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B)
    (hz : z ∈ Metric.closedBall (0 : ℂ) r' \ SetOfZeros R' f) :
    ‖(deriv f z / f z) - ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, analyticOrderNatAt f ρ / (z - ρ)‖ ≤
      (16 * r ^ 2 / (r - r') ^ 3 + 1 / ((R ^ 2 / R' - R') * Real.log (R / R'))) * Real.log B := by
  have r'_lt_one : r' < 1 := lt_trans r'_lt_r r_lt_one
  have r_pos : 0 < r := lt_trans r'_pos r'_lt_r
  have R'_pos : 0 < R' := lt_trans r_pos r_lt_R'
  have R_pos : 0 < R := lt_trans R'_pos R'_lt_R
  have r_lt_R : r < R := lt_trans r_lt_R' R'_lt_R
  have r'_lt_R : r' < R := lt_trans r'_lt_r r_lt_R
  have rFiniteZeros: (SetOfZeros r f).Finite := finiteSetOfZeros_mono r_lt_one finiteZeros
  have zNotInZeros : ¬(z ∈ SetOfZeros r f) := (fun hmem => hz.2 ⟨hmem.1.trans r_lt_R'.le, hmem.2⟩)
  have z_norm : ‖z‖ ≤ r' := by simpa [Metric.mem_closedBall, dist_zero_right] using hz.1
  have ρ_mem : ∀ ρ ∈ rFiniteZeros.toFinset, ‖ρ‖ ≤ r ∧ f ρ = 0 := fun ρ hρ => rFiniteZeros.mem_toFinset.mp hρ
  have ρ_ne_zero : ∀ ρ ∈ rFiniteZeros.toFinset, ρ ≠ 0 := fun ρ hρ h => one_ne_zero (hf0_eq_one ▸ h ▸ (ρ_mem ρ hρ).2)
  have blaschke_sub_ne : ∀ ρ ∈ rFiniteZeros.toFinset, (↑R : ℂ) - z * (starRingEnd ℂ) ρ / ↑R ≠ 0 := by
    intro ρ hρ h
    have : ‖z * (starRingEnd ℂ) ρ / (↑R : ℂ)‖ < R := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos R_pos, div_lt_iff₀ R_pos, norm_mul, norm_conj]
      exact mul_lt_mul (z_norm.trans_lt r'_lt_R) ((ρ_mem ρ hρ).1.trans_lt r_lt_R).le
        (norm_pos_iff.mpr (ρ_ne_zero ρ hρ)) R_pos.le
    rw [← sub_eq_zero.mp h] at this
    simp [Complex.norm_real, abs_of_pos R_pos] at this
  have fz_ne : f z ≠ 0 := fun h => zNotInZeros ⟨z_norm.trans r'_lt_r.le, h⟩
  have blaschke_prod_ne : ∀ ρ ∈ rFiniteZeros.toFinset, ((↑R : ℂ) - z * (starRingEnd ℂ) ρ / ↑R) ^ analyticOrderNatAt f ρ ≠ 0 := fun ρ hρ => pow_ne_zero _ (blaschke_sub_ne ρ hρ)
  have hDiff_blaschke : ∀ ρ ∈ rFiniteZeros.toFinset, DifferentiableAt ℂ (fun w => ((↑R : ℂ) - w * (starRingEnd ℂ) ρ / ↑R) ^ analyticOrderNatAt f ρ) z := fun ρ _ => ((differentiableAt_const _).sub ((differentiableAt_id.mul_const _).div_const _)).pow _
  have hDiff_sub : ∀ ρ ∈ rFiniteZeros.toFinset, DifferentiableAt ℂ (fun w => (w - (ρ : ℂ)) ^ analyticOrderNatAt f ρ) z := fun ρ _ => (differentiableAt_id.sub (differentiableAt_const _)).pow _
  have hpos : 0 < R ^ 2 / R' - R' := by
    rw [sub_pos, lt_div_iff₀ R'_pos, ← sq]
    apply pow_lt_pow_left₀ R'_lt_R R'_pos.le two_ne_zero
  have LfBound := JBlaschkeDerivBound one_lt_B r'_pos r'_lt_r r_pos r_lt_R R_lt_one hfAnalytic hf0_eq_one finiteZeros fz_bound hz.1
  have zerosBound : ↑(∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, analyticOrderNatAt f ρ) ≤ 1 / Real.log (R / R') * Real.log B := by
    apply (ZerosBound r_pos r_lt_one r_lt_R R_lt_one hfAnalytic hf0_eq_one finiteZeros fz_bound).trans
    refine mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le ?_ ?_) (Real.log_nonneg (le_of_lt one_lt_B))
    · rw [← Real.log_one, Real.log_lt_log_iff zero_lt_one (div_pos R_pos R'_pos), one_lt_div R'_pos]
      exact R'_lt_R
    · rw [Real.log_le_log_iff (div_pos R_pos R'_pos) (div_pos R_pos r_pos)]
      exact div_le_div_of_nonneg_left (le_of_lt R_pos) r_pos (le_of_lt r_lt_R')
  suffices h1 : ‖deriv f z / f z - ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, ↑(analyticOrderNatAt f ρ) / (z - ρ)‖ ≤ ‖deriv (JBlaschke r'_pos r'_lt_r r_pos r_lt_R R_lt_one hfAnalytic hf0_eq_one finiteZeros) z‖ + 1 / (R ^ 2 / R' - R') * ↑(∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, analyticOrderNatAt f ρ) by
    calc ‖deriv f z / f z - ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, ↑(analyticOrderNatAt f ρ) / (z - ρ)‖
      ≤ ‖deriv (JBlaschke r'_pos r'_lt_r r_pos r_lt_R R_lt_one hfAnalytic hf0_eq_one finiteZeros) z‖ + 1 / (R ^ 2 / R' - R') * ↑(∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, analyticOrderNatAt f ρ) := h1
    _ ≤ 16 * Real.log B * r ^ 2 / (r - r') ^ 3 + 1 / (R ^ 2 / R' - R') * (1 / Real.log (R / R') * Real.log B) := by
      linarith [mul_le_mul_of_nonneg_left zerosBound (div_nonneg zero_le_one (le_of_lt hpos))]
    _ = (16 * r ^ 2 / (r - r') ^ 3 + 1 / ((R ^ 2 / R' - R') * Real.log (R / R'))) * Real.log B := by
      field_simp
  suffices h2 : deriv f z / f z - ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, ↑(analyticOrderNatAt f ρ) / (z - ρ) =
    deriv (JBlaschke r'_pos r'_lt_r r_pos r_lt_R R_lt_one hfAnalytic hf0_eq_one finiteZeros) z - ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, ↑(analyticOrderNatAt f ρ) / (z - R ^ 2 / conj ρ) by
    rw [h2, sub_eq_add_neg]
    apply norm_add_le_of_le (le_rfl)
    simp only [norm_neg, cast_sum, Finset.mul_sum, one_div_mul_eq_div]
    apply (norm_sum_le _ _).trans (Finset.sum_le_sum (fun ρ hρ => ?_))
    rw [norm_div, RCLike.norm_natCast]
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) hpos
    simp only [Set.mem_sdiff, Metric.mem_closedBall, dist_zero_right, SetOfZeros, Finite.mem_toFinset, mem_ofPred_eq] at hρ hz
    rw [norm_sub_rev]
    calc R ^ 2 / R' - R'
        ≤ ‖↑R ^ 2 / conj ρ‖ - ‖z‖ := by
          refine sub_le_sub ?_ (hz.1.trans (r'_lt_r.le.trans r_lt_R'.le))
          rw [norm_div, norm_pow, norm_real, norm_eq_abs, abs_of_nonneg (le_of_lt R_pos)]
          apply div_le_div_of_nonneg_left (sq_nonneg R) (norm_pos_iff.mpr (star_ne_zero.mpr (fun h => one_ne_zero (hf0_eq_one ▸ h ▸ hρ.2))))
          rw [norm_star]
          linarith [hρ.1]
      _ ≤ ‖↑R ^ 2 / conj ρ - z‖ := norm_sub_norm_le _ _
  suffices h3 : deriv (BlaschkeB r R f) z / BlaschkeB r R f z = deriv f z / f z
    + ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, ↑(analyticOrderNatAt f ρ) / (z - R ^ 2 / conj ρ)
    - ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, ↑(analyticOrderNatAt f ρ) / (z - ρ) by
    let blaschkeAnalytic := BlaschkeAnalytic r_pos r_lt_R R_lt_one finiteZeros hfAnalytic (hf0_eq_one ▸ one_ne_zero)
    let blaschkeNonzero := BlaschkeNonzero r_pos r_lt_R R_lt_one finiteZeros hfAnalytic (hf0_eq_one ▸ one_ne_zero)
    let logOfAnalytic := LogOfAnalyticFunction' r'_pos r'_lt_r r_lt_R blaschkeAnalytic blaschkeNonzero
    set JB := logOfAnalytic.choose with JB_def
    obtain ⟨JB_Analytic, JB_0_eq_0, deriv_JB_eq, JB_re⟩ := logOfAnalytic.choose_spec
    rw [← JB_def] at JB_Analytic JB_0_eq_0 deriv_JB_eq JB_re
    have JB_def' : JB = (JBlaschke r'_pos r'_lt_r r_pos r_lt_R R_lt_one hfAnalytic hf0_eq_one finiteZeros) := by
      unfold JBlaschke
      rw [JB_def]
    rw [eq_sub_iff_add_eq, sub_add_eq_add_sub, ← h3, ← JB_def', eq_comm]
    exact deriv_JB_eq z hz.1
  suffices h4 : BlaschkeB r R f z = f z * ∏ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, ((R - z * conj ρ / R) / (z - ρ)) ^ (analyticOrderNatAt f ρ) by
    have sum1LD : ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, logDeriv (fun z ↦ (R - z * conj ρ / R) ^ ↑(analyticOrderNatAt f ρ)) z = ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, ↑(analyticOrderNatAt f ρ) / (z - R ^ 2 / conj ρ) := by
      refine Finset.sum_congr rfl (fun ρ hρ => ?_)
      rw [← logDeriv_pow, logDeriv_fun_pow, logDeriv_fun_pow, logDeriv_id', mul_eq_mul_left_iff]
      · left
        simp only [logDeriv, Pi.div_apply]
        rw [deriv_fun_sub (differentiableAt_const _) ?_, deriv_div_const, deriv_mul_const (differentiableAt_fun_id)]
        · simp only [deriv_const', deriv_id'', one_mul, zero_sub]
          rw [div_eq_div_iff (blaschke_sub_ne ρ hρ), one_mul, neg_mul, mul_sub, mul_div, neg_sub, mul_comm _ z, ← mul_div_assoc, sub_left_inj]
          · field_simp
            exact mul_div_cancel_left₀ _ (star_ne_zero.mpr (ρ_ne_zero ρ hρ))
          · intro h; apply blaschke_sub_ne ρ hρ
            have hconj : (starRingEnd ℂ) ρ ≠ 0 := star_ne_zero.mpr (ρ_ne_zero ρ hρ)
            have hR : (↑R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt R_pos)
            rw [sub_eq_zero.mp h, div_mul_cancel₀ _ hconj, sq, mul_div_cancel_right₀ _ hR, sub_self]
        · simp only [differentiableAt_fun_id, differentiableAt_const, DifferentiableAt.fun_mul,
          DifferentiableAt.div_const]
      · simp only [differentiableAt_fun_id]
      · simp only [differentiableAt_const, DifferentiableAt.fun_sub_iff_right,
          differentiableAt_fun_id, DifferentiableAt.fun_mul, DifferentiableAt.div_const]
    have sum2LD : ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, logDeriv (fun z ↦ (z - ρ) ^ ↑(analyticOrderNatAt f ρ)) z =  ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, ↑(analyticOrderNatAt f ρ) / (z - ρ) := by
      refine Finset.sum_congr rfl (fun ρ _ => ?_)
      have : (fun z ↦ (z - ρ) ^ analyticOrderNatAt f ρ) =
        (fun x ↦ x ^ analyticOrderNatAt f ρ) ∘ (fun z ↦ z - ρ) := by rfl
      rw[← logDeriv_pow, this, logDeriv_comp]
      · simp only [logDeriv_pow, differentiableAt_fun_id, differentiableAt_const, deriv_fun_sub,
          deriv_id'', deriv_const', sub_zero, mul_one]
      · simp only [differentiableAt_fun_id, DifferentiableAt.fun_pow]
      · simp only [differentiableAt_fun_id, differentiableAt_const, DifferentiableAt.fun_sub]
    unfold BlaschkeB Cf
    simp only [rFiniteZeros, ↓reduceDIte, dite_eq_ite, ite_mul, ← logDeriv_apply, ← sum1LD, ← sum2LD]
    rw [← logDeriv_fun_prod blaschke_prod_ne hDiff_blaschke,
      ← logDeriv_fun_prod ?_ hDiff_sub,
      ← logDeriv_fun_mul _ fz_ne (Finset.prod_ne_zero_iff.mpr blaschke_prod_ne) ((hfAnalytic z (Metric.closedBall_subset_closedBall r'_lt_one.le hz.1)).differentiableAt) (DifferentiableAt.fun_finsetProd hDiff_blaschke),
      ← logDeriv_fun_div _ ?_ ?_ ?_ (DifferentiableAt.fun_finsetProd hDiff_sub)]
    · have h_eq : ∀ᶠ w in nhds z, (if w ∈ SetOfZeros r f then (ZeroFactor f w / ∏ ρ ∈ rFiniteZeros.toFinset \ {w}, (w - ρ) ^ analyticOrderNatAt f ρ) * ∏ ρ ∈ rFiniteZeros.toFinset, (R - w * (starRingEnd ℂ) ρ / R) ^ analyticOrderNatAt f ρ else (f w / ∏ ρ ∈ rFiniteZeros.toFinset, (w - ρ) ^ analyticOrderNatAt f ρ) * ∏ ρ ∈ rFiniteZeros.toFinset, (R - w * (starRingEnd ℂ) ρ / R) ^ analyticOrderNatAt f ρ) = (f w * ∏ ρ ∈ rFiniteZeros.toFinset, (R - w * (starRingEnd ℂ) ρ / R) ^ analyticOrderNatAt f ρ) / ∏ ρ ∈ rFiniteZeros.toFinset, (w - ρ) ^ analyticOrderNatAt f ρ := by
        filter_upwards [(isOpen_compl_iff.mpr rFiniteZeros.isClosed).mem_nhds zNotInZeros] with w hw using by rw [if_neg hw]; ring
      simp only [logDeriv, Pi.div_apply]
      congr 1
      · apply Filter.EventuallyEq.deriv_eq h_eq
      · convert h_eq.self_of_nhds using 1
    · exact mul_ne_zero fz_ne (Finset.prod_ne_zero_iff.mpr blaschke_prod_ne)
    · simp only [ne_eq, Finset.prod_eq_zero_iff, Finite.mem_toFinset, pow_eq_zero_iff',
        sub_eq_zero, ↓existsAndEq, zNotInZeros, true_and, false_and, not_false_eq_true]
    · exact ((hfAnalytic z (Metric.closedBall_subset_closedBall r'_lt_one.le hz.1)).differentiableAt).mul (DifferentiableAt.fun_finsetProd hDiff_blaschke)
    · exact (fun ρ hρ => pow_ne_zero _ (sub_ne_zero.mpr fun h => zNotInZeros (h ▸ rFiniteZeros.mem_toFinset.mp hρ)))
  simp only [BlaschkeB, Cf, rFiniteZeros, ↓reduceDIte, zNotInZeros, div_mul_eq_mul_div, mul_div_assoc, ← Finset.prod_div_distrib, div_pow]

blueprint_comment /--
  API analogous to HasProd.norm, Multipliable.norm, Multipliable.norm-tprod
-/

variable {α R : Type*} [SeminormedCommRing R] [NormMulClass R] [NormOneClass R]
 {f : α → R} {x : R}

lemma HasProd.nnnorm (hfx : HasProd f x) : HasProd (‖f ·‖₊) ‖x‖₊ := by
  simp only [HasProd, ← nnnorm_prod, SummationFilter.unconditional_filter] at ⊢ hfx
  exact hfx.nnnorm

theorem Multipliable.nnnorm (hf : Multipliable f) : Multipliable (‖f ·‖₊) :=
  let ⟨x, hx⟩ := hf; ⟨‖x‖₊, hx.nnnorm⟩

lemma Multipliable.nnnorm_tprod (hf : Multipliable f) : ‖∏' i, f i‖₊ = ∏' i, ‖f i‖₊ :=
  hf.hasProd.nnnorm.tprod_eq.symm

@[blueprint "ZetaFixedLowerBound"
  (title := "ZetaFixedLowerBound")
  (statement := /--
    For all $t\in\mathbb{R}$ one has
    $$|\zeta(3/2+it)|\geq\frac{\zeta(3)}{\zeta(3/2)}.$$
  -/)
  (proof := /--
    From the Euler product expansion of $\zeta$, we have that for $\Re s>1$
    $$\zeta(s)=\prod_p\frac{1}{1-p^{-s}}.$$
    Thus, we have that
    $$\frac{\zeta(2s)}{\zeta(s)}=\prod_p\frac{1-p^{-s}}{1-p^{-2s}}=\prod_p\frac{1}{1+p^{-s}}.$$
    Now note that $|1-p^{-(3/2+it)}|\leq 1+|p^{-(3/2+it)}|=1+p^{-3/2}$. Thus,
    $$|\zeta(3/2+it)|=\prod_p\frac{1}{|1-p^{-(3/2+it)}|}
      \geq\prod_p\frac{1}{1+p^{-3/2}}=\frac{\zeta(3)}{\zeta(3/2)}$$
    for all $t\in\mathbb{R}$ as desired.
  -/)
  (latexEnv := "theorem")]
lemma ZetaFixedLowerBound (t : ℝ) :
    ‖ζ (3/2 + I * t)‖₊ ≥ ‖ζ 3 / ζ (3 / 2)‖₊ := by
  have mp : ∀ {s : ℂ}, 1 < s.re → Multipliable fun p : Primes ↦ (1 - (p : ℂ) ^ (-s))⁻¹ := by
    intro s hs
    exact ⟨ζ s, riemannZeta_eulerProduct_hasProd hs⟩
  have h₁ : 1 < ((3 : ℂ) / 2).re := by norm_num
  have h₂ : 1 < (3 : ℂ).re := by norm_num
  have h₃ : 1 < (3 / 2 + I * (t : ℂ)).re := by norm_num
  rw [nnnorm_div, ge_iff_le,
    div_le_iff₀ (nnnorm_pos.mpr (riemannZeta_ne_zero_of_one_le_re (by norm_num))),
    ← riemannZeta_eulerProduct_tprod h₁, ← riemannZeta_eulerProduct_tprod h₂,
    ← riemannZeta_eulerProduct_tprod h₃, (mp h₁).nnnorm_tprod, (mp h₂).nnnorm_tprod,
    (mp h₃).nnnorm_tprod, ← (mp h₃).nnnorm.tprod_mul (mp h₁).nnnorm]
  refine (mp h₂).nnnorm.tprod_le_tprod (fun p ↦ ?_) ((mp h₃).nnnorm.mul (mp h₁).nnnorm)
  simp only [nnnorm_inv, ← mul_inv]
  have hfact : ‖1 - (p : ℂ) ^ (-3 : ℂ)‖₊ =
      ‖1 + (p : ℂ) ^ ((-3 : ℂ) / 2)‖₊ * ‖1 - (p : ℂ) ^ (-((3 : ℂ) / 2))‖₊ := by
    rw [← nnnorm_mul]; congr 1; ring_nf; rw [← Complex.cpow_nat_mul]; ring_nf
  have hne : ∀ {s : ℂ}, 1 < s.re → (1 - (p : ℂ) ^ (-s)) ≠ 0 := fun hs ↦ Complex.one_sub_prime_cpow_ne_zero p.2 hs
  rw [inv_le_inv₀, hfact]
  · apply _root_.mul_le_mul_left
    rw [← norm_toNNReal, ← norm_toNNReal]
    apply Real.toNNReal_le_toNNReal
    calc ‖1 - (p : ℂ) ^ (-(3 / 2 + I * ↑t))‖
        ≤ 1 + ‖(p : ℂ) ^ (-(3 / 2 + I * ↑t))‖ := by
          rw [← Complex.norm_of_nonneg zero_le_one]; exact norm_sub_le _ _
      _ = ‖1 + (p : ℂ) ^ (-(3 : ℂ) / 2)‖ := by
          have : 0 ≤ 1 + (p : ℝ) ^ (-(3 : ℝ) / 2) := by linarith [Real.rpow_nonneg (cast_nonneg' ↑p) (-3 / 2)]
          simp only [Complex.norm_natCast_cpow_of_pos (Nat.Prime.pos p.2), add_re, neg_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero,
            sub_self, div_ofNat_re, re_ofNat, neg_div', add_zero]
          rw [← Real.norm_of_nonneg this, ← Complex.norm_real, Complex.ofReal_add, Complex.ofReal_cpow (cast_nonneg' ↑p)]
          push_cast; rfl
  · exact norm_pos_iff.mpr (hne h₂)
  · exact mul_pos (norm_pos_iff.mpr (hne h₃)) (norm_pos_iff.mpr (hne h₁))

@[blueprint "riemannZeta1"
  (title := "riemannZeta1")
  (statement := /--
    Let
    $$\zeta_1(s)=1+\frac{1}{s-1}-s\int_1^\infty\{x\}\,x^{-s}\,\frac{dx}{x}.$$
  -/)]
noncomputable def riemannZeta1 (s : ℂ) := 1 + 1 / (s - 1) - s * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)

local notation "ζ₁" => riemannZeta1

@[blueprint "Zeta1AltFormula"
  (title := "Zeta1AltFormula")
  (statement := /--
    We have that
    $$\zeta_1(s)=\zeta_0(1,s)$$
    where $\zeta_0(1,s)$ comes from Definition \ref{riemannZeta0}.
  -/)
  (proof := /--
    Note that
    $$\zeta_0(1,s)=1+\frac{-1}{1-s}+\frac{-1}{2}+s\int_1^\infty\frac{\lfloor x\rfloor+1/2-x}{x^{s+1}}\,dx.$$
    With minor simplifications we have
    $$\zeta_0(1,s)=1+\frac{1}{s-1}-\frac{1}{2}+\frac{s}{2}\int_1^\infty x^{-s-1}\,dx-s\int_1^\infty\{x\}\,x^{-s-1}\,dx.$$
    The first integral evaluates to $1/s$ (when $0<\mathfrak{R}s$), so this term when multiplied by the $s/2$ cancels with the $-1/2$. This exactly gives $\zeta_1$.
  -/)]
lemma Zeta1AltFormula {s : ℂ} (hs : 0 < s.re) :
    ζ₁ s = riemannZeta0 1 s := by
  have := Int.self_sub_floor (R := ℝ)
  have s_ne_zero : s ≠ 0 := by
    intro h; have : s.re = 0 := by simp only [h, zero_re]
    linarith
  simp only [riemannZeta1, riemannZeta0, Finset.sum_range_succ, Finset.sum_range_zero, div_zero,
    CharP.cast_eq_zero, zero_add, cast_one, one_cpow, ne_eq, one_ne_zero, not_false_eq_true,
    div_self, Complex.zero_cpow s_ne_zero, zero_add, ← div_neg_eq_neg_div', neg_sub, Int.fract]
  rw [sub_eq_add_neg, ← mul_neg, ← MeasureTheory.integral_neg]
  nth_rewrite 2 [add_assoc]
  rw [add_left_cancel_iff, neg_sub_left, add_comm 1 s]
  simp only [← neg_mul, ← Complex.ofReal_neg, neg_sub, div_eq_mul_inv, one_mul, add_sub_right_comm, add_mul, ← Complex.cpow_neg, neg_add, ← sub_eq_add_neg]
  rw [MeasureTheory.integral_add, MeasureTheory.integral_const_mul, integral_Ioi_cpow_of_lt _ zero_lt_one]
  · push_cast; simp only [inv_neg, sub_add_cancel, one_cpow,
      neg_div_neg_eq, one_div, mul_add, ← mul_assoc, mul_right_comm, mul_inv_cancel₀ s_ne_zero]
    norm_num
  · simp only [neg_re, one_re, sub_re]
    linarith
  · refine MeasureTheory.Integrable.mono' (integrableOn_Ioi_rpow_of_lt (by linarith) (by linarith)) ?_ ?_ (g := fun u => u ^ ( -s.re - 1 ))
    · apply Measurable.aestronglyMeasurable
      refine Measurable.mul ?_ (Complex.measurable_ofReal.pow_const _)
      exact (Measurable.of_discrete.comp Int.measurable_floor).sub Complex.measurable_ofReal
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      norm_num [Complex.norm_cpow_eq_rpow_re_of_pos ( zero_lt_one.trans hx )]
      apply mul_le_of_le_one_left (Real.rpow_nonneg (by linarith [hx.out]) _)
      norm_cast; rw [← norm_neg, neg_sub, ← Int.fract, Real.norm_of_nonneg (Int.fract_nonneg _)]
      exact (Int.fract_lt_one _).le
  · refine MeasureTheory.Integrable.mono' (integrableOn_Ioi_rpow_of_lt (by linarith) (by linarith)) ?_ ?_ (g := fun u => u ^ ( -s.re - 1 ))
    · apply Measurable.aestronglyMeasurable
      exact measurable_const.mul (Complex.measurable_ofReal.pow_const _)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      norm_num [Complex.norm_cpow_eq_rpow_re_of_pos ( zero_lt_one.trans hx )]
      exact mul_le_of_le_one_left (Real.rpow_nonneg (by linarith [hx.out]) _) (one_half_lt_one).le

@[blueprint "ZetaAltFormula"
  (title := "ZetaAltFormula")
  (statement := /--
    We have that
    $$\zeta(s)=\zeta_1(s)$$
    for all $s\in S$ with $S=\{s\in\mathbb{C}:0<\mathfrak{R}s,\,s\neq 1\}$.
  -/)
  (proof := /--
    This immediately follows from Lemmas \ref{Zeta1AltFormula} and \ref{Zeta0EqZeta}.
  -/)]
lemma ZetaAltFormula {s : ℂ} (hs : 0 < s.re) (hs' : s ≠ 1) :
    ζ s = ζ₁ s:= by
  rw [Zeta1AltFormula hs, ← Zeta0EqZeta zero_lt_one hs hs']

@[blueprint "GlobalBound"
  (title := "GlobalBound")
  (statement := /--
    For all $s\in\mathbb{C}$ with $|s|\leq 1$ and $t\in\mathbb{R}$ with $|t|\geq 2$, we have that
    $$|\zeta(s+3/2+it)|\leq 7+2\,|t|.$$
  -/)
  (proof := /--
    For the sake of clearer proof writing let $z=s+3/2+it$. Since $|s|\leq 1$ we know that
    $1/2\leq\mathfrak{R}z$; additionally, as $|t|\geq 2$, we know $1\leq|\mathfrak{I}z|$.
    So, $z\in S$. Thus, from Lemma \ref{ZetaAltFormula} we know that
    $$|\zeta(z)|\leq 1+\frac{1}{|z-1|}
      +|z|\cdot\left|\int_1^\infty\{x\}\,x^{-z}\,\frac{dx}{x}\right|$$
    by applying the triangle inequality. Now note that $|z-1|\geq 1$. Likewise,
    $$|z|\cdot\left|\int_1^\infty\{x\}\,x^{-z}\,\frac{dx}{x}\right|
      \leq|z|\int_1^\infty|\{x\}\,x^{-z-1}|\,dx
      \leq|z|\int_1^\infty x^{-\Re z-1}\,dx=\frac{|z|}{\Re z}\leq 2\,|z|.$$
    Thus we have that,
    $$|\zeta(s+3/2+it)|=|\zeta(z)|\leq 1+1+2\,|z|=2+2\,|s+3/2+it|
      \leq2+2\,|s|+3+2\,|it|\leq 7+2\,|t|.$$
  -/)]
theorem GlobalBound
    {s : ℂ} (hs : ‖s‖ ≤ 1) {t : ℝ} (ht : |t| ≥ 2) :
    ‖ζ (s + 3 / 2 + I * t)‖ ≤ 7 + 2 * |t| := by
  have sReLB : -1 ≤ s.re := by linarith [abs_le.mp ((Complex.abs_re_le_norm s).trans hs)]
  have hz : s + 3 / 2 + I * ↑t ∈ {s | 0 < s.re ∧ s ≠ 1} := by
    simp only [ne_eq, Complex.ext_iff, one_re, one_im, not_and, mem_ofPred_eq, add_re, div_ofNat_re,
      re_ofNat, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero, sub_self, add_zero,
      add_im, div_ofNat_im, im_ofNat, zero_div, mul_im, one_mul, zero_add]
    refine ⟨by linarith, fun hs => ?_⟩
    cases abs_cases t <;>  linarith [abs_le.mp (Complex.abs_re_le_norm s), abs_le.mp (Complex.abs_im_le_norm s)]
  have leadingTerms : ‖1 + 1 / (s + 3 / 2 + I * ↑t - 1)‖ ≤ 2 := by
    rw [← one_add_one_eq_two (R := ℝ)]
    apply norm_add_le_of_le (norm_one.le)
    rw [norm_div, norm_one, div_le_one (norm_pos_iff.mpr (sub_ne_zero.mpr hz.2))]
    simp only [norm_def, normSq, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, sqrt_le_one, sub_re,
      add_re, div_ofNat_re, re_ofNat, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero,
      sub_self, add_zero, one_re, sub_im, add_im, div_ofNat_im, im_ofNat, zero_div, mul_im, one_mul,
      zero_add, one_im, sub_zero, one_le_sqrt] at ⊢ hs
    cases abs_cases t <;> nlinarith [sq_nonneg (s.re + 1 / 2), sq_nonneg (s.im + t - 1), sq_nonneg (s.im + t + 1)]
  have domBound {x : ℝ} (hu : x ∈ Ioi 1) : |Int.fract x| * ‖(x : ℂ) ^ (-(s + 3 / 2 + I * ↑t) - 1)‖ ≤ x ^ (-(s.re + 3 / 2) - 1) := by
    rw [mem_Ioi] at hu
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    simp only [neg_add_rev, sub_re, add_re, neg_re, mul_re, I_re, ofReal_re, zero_mul, I_im,
      ofReal_im, mul_zero, sub_self, neg_zero, div_ofNat_re, re_ofNat, zero_add, one_re, Int.abs_fract]
    refine mul_le_of_le_one_left (by apply Real.rpow_nonneg (by linarith)) ((Int.fract_lt_one x).le)
  have domIntegral : Integrable (fun x : ℝ => x ^ (-(s.re + 3 / 2) - 1)) (volume.restrict (Set.Ioi 1)) := integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hint : ‖∫ (u : ℝ) in Ioi 1, (↑(Int.fract u) : ℂ) * (u : ℂ) ^ (-(s + 3 / 2 + I * ↑t) - 1)‖ ≤ 1 / (s.re + 3 / 2) := by
    refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
    have hI := integral_Ioi_rpow_of_lt (a := -(s.re + 3 / 2) - 1) (by linarith) one_pos
    simp only [sub_add_cancel, one_rpow, neg_div_neg_eq] at hI
    simp only [Complex.norm_mul, norm_real, norm_eq_abs, ← hI]
    refine integral_mono_ae (domIntegral.mono' (((measurable_fract.abs).mul ((Complex.measurable_ofReal.pow_const _).norm)).aestronglyMeasurable) ?_) domIntegral (by filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx using domBound hx)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_mul, norm_eq_abs, abs_abs, norm_norm]
    exact domBound hx
  have z_norm : ‖s + 3 / 2 + I * ↑t‖ ≤ 5 / 2 + |t| := by
    have It_norm : ‖I * (↑t : ℂ)‖ = |t| := by rw [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have threeHalves_norm : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by rw [norm_div, Complex.norm_ofNat, Complex.norm_ofNat]
    refine (norm_add_le_of_le (norm_add_le_of_le hs (le_of_eq threeHalves_norm)) (le_of_eq It_norm)).trans (by linarith)
  have hmul : ‖(s + 3 / 2 + I * ↑t) * ∫ (u : ℝ) in Ioi 1, (↑(Int.fract u) : ℂ) * (u : ℂ) ^ (-(s + 3 / 2 + I * ↑t) - 1)‖ ≤ 5 + 2 * |t| := by
    rw [norm_mul]
    have hinv : (1 : ℝ) / (s.re + 3 / 2) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    exact (mul_le_mul z_norm (hint.trans hinv) (norm_nonneg _) (by linarith [abs_nonneg t])).trans (by linarith)
  rw [ZetaAltFormula hz.1 hz.2]
  exact (norm_sub_le_of_le leadingTerms hmul).trans (by linarith)

blueprint_comment /--
\begin{theorem}[LogDerivZetaFinalBound]\label{LogDerivZetaFinalBound}
    Let $t\in\mathbb{R}$ with $|t|\geq 2$ and $0 < r' < r < R' < R<1$. If
    $f(z)=\zeta(z+3/2+it)$, then for all
    $z\in\overline{\mathbb{D}_{r'}}\setminus\mathcal{K}_f(R')$ we have that
    $$\left|\frac{f'}{f}(z)-\sum_{\rho\in\mathcal{K}_f(r)}\frac{m_f(\rho)}{z-\rho}\right|
      \ll\left(\frac{16r^2}{(r-r')^3}+\frac{1}{(R^2/R'-R')\,\log(R/R')}\right)\log|t|.$$
\end{theorem}
-/

blueprint_comment /--
\begin{proof}
\uses{ZetaFixedLowerBound, GlobalBound, FinalBound}
    Let $g(z)=\zeta(z+3/2+it)/\zeta(3/2+it)$. Note that $g(0)=1$ and for $|z|\leq R$
    $$|g(z)|=\frac{|\zeta(z+3/2+it)|}{|\zeta(3/2+it)|}
      \leq\frac{\zeta(3/2)}{\zeta(3)}\cdot(7+2\,|t|)\leq\frac{13\,\zeta(3/2)}{3\,\zeta(3)}\,|t|$$
    by Theorems \ref{ZetaFixedLowerBound} and \ref{GlobalBound}. Thus by Theorem
    \ref{FinalBound} we have that
    $$\left|\frac{g'}{g}(z)-\sum_{\rho\in\mathcal{K}_g(r)}\frac{m_g(\rho)}{z-\rho}\right|
      \leq\left(\frac{16r^2}{(r-r')^3}+\frac{1}{(R^2/R'-R')\,\log(R/R')}\right)
      \left(\log|t|+\log\left(\frac{13\,\zeta(3/2)}{3\,\zeta(3)}\right)\right).$$
    Now note that $f'/f=g'/g$, $\mathcal{K}_f(r)=\mathcal{K}_g(r)$, and
    $m_g(\rho)=m_f(\rho)$ for all $\rho\in\mathcal{K}_f(r)$. Thus we have that,
    $$\left|\frac{f'}{f}(z)-\sum_{\rho\in\mathcal{K}_f(r)}\frac{m_f(\rho)}{z-\rho}\right|
      \ll\left(\frac{16r^2}{(r-r')^3}+\frac{1}{(R^2/R'-R')\,\log(R/R')}\right)\log|t|$$
    where the implied constant $C$ is taken to be
    $$C\geq 1+\frac{\log((13\,\zeta(3/2))/(3\,\zeta(3)))}{\log 2}.$$
\end{proof}
-/

blueprint_comment /--
\begin{definition}[ZeroWindows]\label{ZeroWindows}
    Let $\mathcal{Z}_t=\{\rho\in\mathbb{C}:\zeta(\rho)=0,\,|\rho-(3/2+it)|\leq 3/4\}$.
\end{definition}
-/

blueprint_comment /--
\begin{lemma}[SumBoundI]\label{SumBoundI}
    For all $\delta\in (0,1)$ and $t\in\mathbb{R}$ with $|t|\geq 2$ we have
    $$\left|\frac{\zeta'}{\zeta}(1+\delta+it)
      -\sum_{\rho\in\mathcal{Z}_t}\frac{m_\zeta(\rho)}{1+\delta+it-\rho}\right|\ll\log|t|.$$
\end{lemma}
-/

blueprint_comment /--
\begin{proof}
\uses{LogDerivZetaFinalBound}
    We apply Theorem \ref{LogDerivZetaFinalBound} where $r'=2/3$, $r=3/4$, $R'=5/6$, and
    $R=8/9$. Thus, for all $z\in\overline{\mathbb{D}_{2/3}}\setminus\mathcal{K}_f(5/6)$
    we have that
    $$\left|\frac{\zeta'}{\zeta}(z+3/2+it)
      -\sum_{\rho\in\mathcal{K}_f(3/4)}\frac{m_f(\rho)}{z-\rho}\right|\ll\log|t|$$
    where $f(z)=\zeta(z+3/2+it)$ for $t\in\mathbb{R}$ with $|t|\geq 2$. Now if we let
    $z=-1/2+\delta$, then $z\in(-1/2,1/2)\subseteq\overline{\mathbb{D}_{2/3}}$.
    Additionally, $f(z)=\zeta(1+\delta+it)$, where $1+\delta+it$ lies in the zero-free
    region where $\sigma>1$. Thus, $z\not\in\mathcal{K}_f(5/6)$. So,
    $$\left|\frac{\zeta'}{\zeta}(1+\delta+it)
      -\sum_{\rho\in\mathcal{K}_f(3/4)}\frac{m_f(\rho)}{-1/2+\delta-\rho}\right|
      \ll\log|t|.$$
    But now note that if $\rho\in\mathcal{K}_f(3/4)$, then $\zeta(\rho+3/2+it)=0$ and
    $|\rho|\leq 3/4$. Thus, $\rho+3/2+it\in\mathcal{Z}_t$ (the argument works in reverse as well).
    Additionally, note that $m_f(\rho)=m_\zeta(\rho+3/2+it)$. So changing variables using these
    facts gives us that
    $$\left|\frac{\zeta'}{\zeta}(1+\delta+it)
      -\sum_{\rho\in\mathcal{Z}_t}\frac{m_\zeta(\rho)}{1+\delta+it-\rho}\right|
      \ll\log|t|.$$
\end{proof}
-/

blueprint_comment /--
\begin{lemma}[ShiftTwoBound]\label{ShiftTwoBound}
    For all $\delta\in (0,1)$ and $t\in\mathbb{R}$ with $|t|\geq 2$ we have
    $$-\Re \left(\frac{\zeta'}{\zeta}(1+\delta+2it)\right)\ll\log|t|.$$
\end{lemma}
-/

blueprint_comment /--
\begin{proof}
\uses{SumBoundI}
    Note that, for $\rho\in\mathcal{Z}_{2t}$
    \begin{align*}
        \Re \left(\frac{1}{1+\delta+2it-\rho}\right)
          &=\Re \left(\frac{1+\delta-2it-\overline{\rho}}
            {(1+\delta+2it-\rho)(1+\delta-2it-\overline{\rho})}\right) \\
          &=\frac{\Re (1+\delta-2it-\overline{\rho})}{|1+\delta+2it-\rho|^2}
            =\frac{1+\delta-\Re \rho}{(1+\delta-\Re \rho)^2+(2t-\mathfrak{I}\rho)^2}.
    \end{align*}
    Now since $\rho\in\mathcal{Z}_{2t}$, we have that $|\rho-(3/2+2it)|\leq 3/4$. So,
    we have $\Re \rho\in[3/4,9/4]$ and $\mathfrak{I}\rho\in[2t-3/4,2t+3/4]$. Additionally,
    we know that $\zeta(\rho)=0$. This implies the stronger condition that $\Re \rho\in[3/4,1]$.
    Thus,
    $$\delta\leq 1+\delta-\Re \rho\qquad\text{and}\qquad
      (1+\delta-\Re \rho)^2+(2t-\mathfrak{I}\rho)^2\leq 25/16+9/16=17/8.$$
    Which implies that
    \begin{equation}\label{pickupPoint4}
        0<\frac{8}{17}\,\delta
          \leq\frac{1+\delta-\Re \rho}{(1+\delta-\Re \rho)^2+(2t-\mathfrak{I}\rho)^2}
          =\Re \left(\frac{1}{1+\delta+2it-\rho}\right).
    \end{equation}
    Note that, from Lemma \ref{SumBoundI}, we have
    $$\sum_{\rho\in\mathcal{Z}_{2t}}m_\zeta(\rho)\,
      \Re \left(\frac{1}{1+\delta+2it-\rho}\right)
      -\Re \left(\frac{\zeta'}{\zeta}(1+\delta+2it)\right)
      \leq\left|\frac{\zeta'}{\zeta}(1+\delta+2it)
      -\sum_{\rho\in\mathcal{Z}_{2t}}\frac{m_\zeta(\rho)}{1+\delta+2it-\rho}\right|
      \ll\log|2t|.$$
    Since $m_\zeta(\rho)\geq 0$ for all $\rho\in\mathcal{Z}_{2t}$, the inequality from
    Equation (\ref{pickupPoint4}) tells us that by subtracting the sum from both sides
    we have
    $$-\Re \left(\frac{\zeta'}{\zeta}(1+\delta+2it)\right)\ll\log|2t|.$$
    Noting that $\log|2t|=\log(2)+\log|t|\leq2\log|t|$ completes the proof.
\end{proof}
-/

blueprint_comment /--
\begin{lemma}[ShiftOneBound]\label{ShiftOneBound}
    There exists $C>0$ such that for all $\delta\in(0,1)$ and $t\in\mathbb{R}$ with
    $|t|\geq 3$; if $\zeta(\rho)=0$ with $\rho=\sigma+it$, then
    $$-\Re \left(\frac{\zeta'}{\zeta}(1+\delta+it)\right)
      \leq -\frac{1}{1+\delta-\sigma}+C\log|t|.$$
\end{lemma}
-/

blueprint_comment /--
\begin{proof}
\uses{SumBoundI}
    Note that for $\rho'\in\mathcal{Z}_t$
    \begin{align*}
        \Re \left(\frac{1}{1+\delta+it-\rho'}\right)
          &=\Re \left(\frac{1+\delta-it-\overline{\rho'}}
            {(1+\delta+it-\rho')(1+\delta-it-\overline{\rho'})}\right) \\
          &=\frac{\Re (1+\delta-it-\overline{\rho'})}{|1+\delta+it-\rho'|^2}
            =\frac{1+\delta-\Re \rho'}{(1+\delta-\Re \rho')^2+(t-\mathfrak{I}\rho')^2}.
    \end{align*}
    Now since $\rho'\in\mathcal{Z}_t$, we have that $|\rho'-(3/2+it)|\leq 3/4$. So, we
    have $\Re \rho'\in[3/4,9/4]$ and $\mathfrak{I}\rho'\in[t-3/4,t+3/4]$. Additionally, we know
    that $\zeta(\rho')=0$. This implies the stronger condition that $\Re \rho'\in[3/4,1]$. Thus,
    $$\delta\leq 1+\delta-\Re \rho'\qquad\text{and}\qquad
      (1+\delta-\Re \rho')^2+(t-\mathfrak{I}\rho')^2\leq 25/16+9/16=17/8.$$
    Which implies that
    \begin{equation}\label{pickupPoint5}
        0<\frac{8}{17}\,\delta
          \leq\frac{1+\delta-\Re \rho'}{(1+\delta-\Re \rho')^2+(t-\mathfrak{I}\rho')^2}
          =\Re \left(\frac{1}{1+\delta+it-\rho'}\right).
    \end{equation}
    Note that, from Lemma \ref{SumBoundI}, we have
    $$\sum_{\rho'\in\mathcal{Z}_t}m_\zeta(\rho')\,
      \Re \left(\frac{1}{1+\delta+it-\rho'}\right)
      -\Re \left(\frac{\zeta'}{\zeta}(1+\delta+it)\right)
      \leq\left|\frac{\zeta'}{\zeta}(1+\delta+it)
      -\sum_{\rho'\in\mathcal{Z}_t}\frac{m_\zeta(\rho')}{1+\delta+it-\rho'}\right|
      \ll\log|t|.$$
    Since $m_\zeta(\rho')\geq 0$ for all $\rho'\in\mathcal{Z}_t$, the inequality from
    Equation (\ref{pickupPoint5}) tells us that by subtracting the sum over all
    $\rho'\in\mathcal{Z}_t\setminus\{\rho\}$ from both sides we have
    $$\frac{m_\zeta(\rho)}{\Re (1+\delta+it-\rho)}
      -\Re \left(\frac{\zeta'}{\zeta}(1+\delta+it)\right)\ll\log|t|.$$
    But of course we have that $\Re (1+\delta+it-\rho)=1+\delta-\sigma$. So subtracting
    this term from both sides and recalling the implied constant we have
    $$-\Re \left(\frac{\zeta'}{\zeta}(1+\delta+it)\right)
      \leq -\frac{m_\zeta(\rho)}{1+\delta-\sigma}+C\log|t|.$$
    We have that $\sigma\leq 1$ since $\zeta$ is zero free on the right half plane
    $\sigma>1$. Thus $0<1+\delta-\sigma$. Noting this in combination with the fact that
    $1\leq m_\zeta(\rho)$ completes the proof.
\end{proof}
-/

blueprint_comment /--
\begin{lemma}[ShiftZeroBound]\label{ShiftZeroBound}
    For all $\delta\in(0,1)$ we have
    $$-\Re \left(\frac{\zeta'}{\zeta}(1+\delta)\right)\leq\frac{1}{\delta}+O(1).$$
\end{lemma}
-/

blueprint_comment /--
\begin{proof}
\uses{riemannZetaLogDerivResidue}
    From Theorem \ref{riemannZetaLogDerivResidue} we know that
    $$-\frac{\zeta'}{\zeta}(s)=\frac{1}{s-1}+O(1).$$
    Changing variables $s\mapsto 1+\delta$ and applying the triangle inequality we have that
    $$-\Re \left(\frac{\zeta'}{\zeta}(1+\delta)\right)\leq\left|
      -\frac{\zeta'}{\zeta}(1+\delta)\right|\leq\frac{1}{\delta}+O(1).$$
\end{proof}
-/

blueprint_comment /--
\begin{lemma}[SumBoundII]\label{SumBoundII}
    For all $t\in\mathbb{R}$ with $|t|\geq 2$ and $z=\sigma+it$
    where $1-\delta_t/3\leq\sigma\leq 3/2$, we have that
    $$\left|\frac{\zeta'}{\zeta}(z)
      -\sum_{\rho\in\mathcal{Z}_t}\frac{m_\zeta(\rho)}{z-\rho}\right|\ll\log|t|.$$
\end{lemma}
-/

blueprint_comment /--
\begin{proof}
\uses{DeltaRange, LogDerivZetaFinalBound, ZeroInequality}
    By Lemma \ref{DeltaRange} we have that
    $$-11/21<-1/2-\delta_t/3\leq\sigma-3/2\leq0.$$
    We apply Theorem \ref{LogDerivZetaFinalBound} where $r'=2/3$, $r=3/4$, $R'=5/6$, and $R=8/9$.
    Thus for all $z\in\overline{\mathbb{D}_{2/3}}\setminus\mathcal{K}_f(5/6)$ we have that
    $$\left|\frac{\zeta'}{\zeta}(z+3/2+it)
      -\sum_{\rho\in\mathcal{K}_f(3/4)}\frac{m_f(\rho)}{z-\rho}\right|\ll\log|t|$$
    where $f(z)=\zeta(z+3/2+it)$ for $t\in\mathbb{R}$ with $|t|\geq 2$.
    Now if we let $z=\sigma-3/2$, then $z\in(-11/21,0)\subseteq\overline{\mathbb{D}_{2/3}}$.
    Additionally, $f(z)=\zeta(\sigma+it)$, where $\sigma+it$ lies in the zero free region given by
    Lemma \ref{ZeroInequality} since $\sigma\geq 1-\delta_t/3\geq 1-\delta_t$.
    Thus, $z\not\in\mathcal{K}_f(5/6)$. So,
    $$\left|\frac{\zeta'}{\zeta}(\sigma+it)
      -\sum_{\rho\in\mathcal{K}_f(3/4)}\frac{m_f(\rho)}{\sigma-3/2-\rho}\right|\ll\log|t|.$$
    But now note that if $\rho\in\mathcal{K}_f(3/4)$, then $\zeta(\rho+3/2+it)=0$
    and $|\rho|\leq 3/4$ (and the argument works in reverse). Additionally, note that
    $m_f(\rho)=m_\zeta(\rho+3/2+it)$. So changing variables using these facts gives us that
    $$\left|\frac{\zeta'}{\zeta}(\sigma+it)
      -\sum_{\rho\in\mathcal{Z}_t}\frac{m_\zeta(\rho)}{\sigma+it-\rho}\right|\ll\log|t|.$$
\end{proof}
-/

blueprint_comment /--
\begin{lemma}[GapSize]\label{GapSize}
   Let $t\in\mathbb{R}$ with $|t|\geq 3$ and $z=\sigma+it$ where $1-\delta_t/3\leq\sigma\leq 3/2$.
   Additionally, let $\rho\in\mathcal{Z}_t$. Then we have that
   $$|z-\rho|\geq\delta_t/6.$$
\end{lemma}
-/

blueprint_comment /--
\begin{proof}
\uses{ZeroInequality}
    Let $\rho=\sigma'+it'$ and note that since $\rho\in\mathcal{Z}_t$, we have $t'\in(t-3/4,t+3/4)$.
    Thus, if $t>1$ we have
    $$\log|t'|\leq\log|t+3/4|\leq\log|2t|=\log 2+\log|t|\leq 2\log|t|.$$
    And otherwise if $t<-1$ we have
    $$\log|t'|\leq\log|t-3/4|\leq\log|2t|=\log 2+\log|t|\leq 2\log|t|.$$
    So by taking reciprocals and multiplying through by a constant we have
    that $\delta_t\leq2\delta_{t'}$. Now note that since $\rho\in\mathcal{Z}_t$
    we know that $\sigma'\leq 1-\delta_{t'}$ by Theorem \ref{ZeroInequality}
    (here we use the fact that $|t|\geq 3$ to give us that $|t'|\geq 2$). Thus,
    $$\delta_t/6\leq\delta_{t'}-\delta_t/3
      =1-\delta_t/3-(1-\delta_{t'})\leq\sigma-\sigma'\leq|z-\rho|.$$
\end{proof}
-/

/-- The logarithmic derivative of the Riemann zeta function is bounded in the half-plane
`Re(s) >= 3/2`. -/
lemma LogDerivZetaBdd_of_Re_ge_three_halves :
    ∃ C, ∀ (s : ℂ), 3/2 ≤ s.re → ‖deriv riemannZeta s / riemannZeta s‖ ≤ C := by
  have h_sum_converges : Summable (fun n : ℕ ↦ vonMangoldt n / (n : ℝ) ^ (3 / 2 : ℝ)) := by
    have h_summable : Summable (fun n : ℕ ↦ (Real.log n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ)) := by
      obtain ⟨C, hC_pos, hC⟩ : ∃ C > 0, ∀ n : ℕ, n ≥ 2 → Real.log n ≤ C * (n : ℝ) ^ (1/4 : ℝ) := by
        use 4, by grind, fun n hn ↦ by
          have := Real.log_le_sub_one_of_pos (by positivity : 0 < (n : ℝ) ^ (1/4 : ℝ))
          rw [Real.log_rpow (by positivity)] at this
          nlinarith [Real.rpow_pos_of_pos (by positivity : 0 < (n : ℝ)) (1/4 : ℝ)]
      have hBound : ∀ n : ℕ, n ≥ 2 →
          (Real.log n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) ≤ C / (n : ℝ) ^ (5 / 4 : ℝ) := fun n hn ↦ by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        convert mul_le_mul_of_nonneg_right (hC n hn)
          (by positivity : 0 ≤ (n : ℝ) ^ (5 / 4 : ℝ)) using 1
        rw [mul_assoc, ← Real.rpow_add (by positivity)]
        grind
      rw [← summable_nat_add_iff 2]
      exact Summable.of_nonneg_of_le
        (fun n ↦ div_nonneg (Real.log_nonneg (by grind))
          (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (fun n ↦ hBound _ (by grind))
        (Summable.mul_left _ <| by simpa using summable_nat_add_iff 2 |>.2 <|
          Real.summable_one_div_nat_rpow.2 <| by grind)
    refine .of_nonneg_of_le (fun n ↦ ?_) (fun n ↦ ?_) h_summable
    · exact div_nonneg (by exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg)
        (by positivity)
    · rcases eq_or_ne n 0 with (rfl | hn) <;>
        simp_all [ArithmeticFunction.vonMangoldt]
      field_simp
      split_ifs
      · exact Real.log_le_log (Nat.cast_pos.mpr (Nat.minFac_pos _))
          (Nat.cast_le.mpr (Nat.minFac_le (Nat.pos_of_ne_zero hn)))
      · exact Real.log_nonneg (Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn))
  have h_log_deriv_sum : ∀ s : ℂ, 3 / 2 ≤ s.re →
      deriv riemannZeta s / riemannZeta s = -∑' n : ℕ, (vonMangoldt n : ℂ) / (n : ℂ) ^ s := by
    intro s hs; have h := LogDerivativeDirichlet s (by grind); linear_combination -h
  have h_triangle : ∀ s : ℂ,
      ‖∑' n : ℕ, (vonMangoldt n : ℂ) / (n : ℂ) ^ s‖ ≤
        ∑' n : ℕ, ‖(vonMangoldt n : ℂ) / (n : ℂ) ^ s‖ := fun s ↦ by
    by_cases h : Summable fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ s
    · exact norm_tsum_le_tsum_norm h.norm
    · simp only [tsum_eq_zero_of_not_summable h, norm_zero]
      exact tsum_nonneg fun _ ↦ by positivity
  have h_norm_summand : ∀ s : ℂ, 3 / 2 ≤ s.re → ∀ n : ℕ,
      ‖(vonMangoldt n : ℂ) / (n : ℂ) ^ s‖ ≤ (vonMangoldt n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) := by
    intro s hs n
    by_cases hn : n = 0 <;> simp_all [Complex.norm_cpow_of_ne_zero]
    ring_nf; norm_num
    rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity)
      (Real.rpow_le_rpow_of_exponent_le (mod_cast Nat.one_le_iff_ne_zero.mpr hn) hs))
      ArithmeticFunction.vonMangoldt_nonneg
  refine ⟨∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ),
    fun s hs ↦ ?_⟩
  have hSum : Summable fun n ↦ ‖(vonMangoldt n : ℂ) / (n : ℂ) ^ s‖ :=
    Summable.of_nonneg_of_le (fun n ↦ by positivity)
      (fun n ↦ h_norm_summand s hs n) h_sum_converges
  simpa [neg_div, h_log_deriv_sum s hs] using (h_triangle s).trans
    (hSum.tsum_le_tsum (fun n ↦ h_norm_summand s hs n) h_sum_converges)

blueprint_comment /--
From here out we closely follow our previous proof of the Medium PNT and we modify it
using our new estimate in Theorem \ref{LogDerivZetaUniformLogSquaredBound}.
Recall Definition \ref{SmoothedChebyshev}; for fixed $\varepsilon>0$
and a bump function $\nu$ supported on $[1/2,2]$ we have
$$\psi_\varepsilon(X)
  =\frac{1}{2\pi i}\int_{(\sigma)}\left(-\frac{\zeta'}{\zeta}(s)\right)
  \,\mathcal{M}(\tilde{1}_\varepsilon)(s)\,X^s\,ds$$
where $\sigma=1+1/\log X$. Let $T>3$ be a large constant to be chosen later,
and we take $\sigma'=1-\delta_T/3=1-F/\log T$ with $F$ coming from
Theorem \ref{LogDerivZetaUniformLogSquaredBound}. We integrate along the $\sigma$ vertical line,
and we pull contours  accumulating the pole at $s=1$ when we integrate along the curves
\begin{itemize}
    \item $I_1$: $\sigma-i\infty$ to $\sigma-iT$
    \item $I_2$: $\sigma'-iT$ to $\sigma-iT$
    \item $I_3$: $\sigma'-iT$ to $\sigma'+iT$
    \item $I_4$: $\sigma'+iT$ to $\sigma+iT$
    \item $I_5$: $\sigma+iT$ to $\sigma+i\infty$.
\end{itemize}
-/

@[blueprint
  (title := "I1New")
  (statement := /--
    Let
    $$I_1(\nu,\varepsilon,X,T)=
      \frac{1}{2\pi i}\int_{-\infty}^{-T}\left(-\frac{\zeta'}{\zeta}(\sigma+it)\right)
      \,\mathcal{M}(\tilde{1}_\varepsilon)(\sigma+it)\,X^{\sigma+it}\,dt.$$
  -/)]
noncomputable def I1New (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Iic (-T),
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))

@[blueprint
  (title := "I5New")
  (statement := /--
    Let
    $$I_5(\nu,\varepsilon,X,T)=
      \frac{1}{2\pi i}\int_T^\infty\left(-\frac{\zeta'}{\zeta}(\sigma+it)\right)
      \,\mathcal{M}(\tilde{1}_\varepsilon)(\sigma+it)\,X^{\sigma+it}\,dt.$$
  -/)]
noncomputable def I5New (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Ici T,
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))

lemma IntegralLogSqOverTSqBound : ∃ C > 0, ∀ T, 3 < T →
  ∫ t in Set.Ici T, (Real.log t)^2 / t^2 ≤ C / Real.sqrt T := by
    have h_log_sq_le_t_fourth_pow :
        ∃ C > 0, ∀ t : ℝ, 3 ≤ t → (Real.log t)^2 / t^2 ≤ C / t^(3/2 : ℝ) := by
      have h_log_sq_le_sqrt :
          ∃ C > 0, ∀ t : ℝ, 3 ≤ t → Real.log t ^ 2 ≤ C * t ^ (1 / 2 : ℝ) := by
        have h_log_sq_le_sqrt : ∃ C > 0, ∀ t : ℝ, 3 ≤ t → Real.log t ≤ C * t ^ (1 / 4 : ℝ) := by
          use 4, by grind, fun t ht ↦ ?_
          have := Real.log_le_sub_one_of_pos (by positivity : 0 < t ^ (1 / 4 : ℝ))
          rw [Real.log_rpow (by positivity)] at this; linarith
        obtain ⟨C, hC₀, hC⟩ := h_log_sq_le_sqrt; use C^2
        exact ⟨sq_pos_of_pos hC₀, fun t ht ↦
          (pow_le_pow_left₀ (Real.log_nonneg <| by linarith) (hC t ht) 2).trans <| by
            rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
            grind⟩
      obtain ⟨C, hC_pos, hC⟩ := h_log_sq_le_sqrt; use C
      refine ⟨hC_pos, fun t ht ↦ ?_⟩; rw [div_le_div_iff₀] <;> try positivity
      convert mul_le_mul_of_nonneg_right (hC t ht)
        (Real.rpow_nonneg (by linarith : 0 ≤ t) (3 / 2)) using 1
      rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add (by linarith)]; grind
    obtain ⟨C, hC_pos, hC_bound⟩ := h_log_sq_le_t_fourth_pow
    use C * 2
    have h_integral_bound :
        ∀ T : ℝ, 3 < T → ∫ t in Set.Ici T, C / t^(3/2 : ℝ) = C * 2 / Real.sqrt T := by
      have h_integral_eval :
          ∀ T : ℝ, 3 < T → ∫ t in Set.Ici T, t ^ (-3 / 2 : ℝ) = 2 / Real.sqrt T := by
        intro T hT
        rw [MeasureTheory.integral_Ici_eq_integral_Ioi, integral_Ioi_rpow_of_lt] <;> norm_num
        · rw [Real.sqrt_eq_rpow, Real.rpow_neg] <;> ring_nf; linarith
        · linarith
      intro T hT; convert congr_arg (fun x ↦ C * x) (h_integral_eval T hT) using 1 <;> ring_nf
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun x hx ↦ ?_
      rw [← Real.rpow_neg (by linarith [Set.mem_Ici.mp hx])]; ring_nf
    refine ⟨by positivity, fun T hT ↦ (MeasureTheory.setIntegral_mono_on ?_ ?_ measurableSet_Ici
        fun t ht ↦ hC_bound t <| by linarith [ht.out]).trans (h_integral_bound T hT |> le_of_eq)⟩
    · have hInteg : IntegrableOn (fun t ↦ C / t ^ (3 / 2 : ℝ)) (Set.Ici T) := by
        have := h_integral_bound T hT
        contrapose! this; rw [MeasureTheory.integral_undef this]; positivity
      have hMeas : AEStronglyMeasurable (fun t ↦ Real.log t ^ 2 / t ^ 2)
          (MeasureTheory.volume.restrict (Set.Ici T)) :=
        Measurable.aestronglyMeasurable <| Measurable.mul
          (Measurable.pow_const Real.measurable_log _)
          (Measurable.inv (measurable_id.pow_const _))
      have hBound : ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.Ici T),
          ‖Real.log t ^ 2 / t ^ 2‖ ≤ C / t ^ (3 / 2 : ℝ) := by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
        rw [Real.norm_of_nonneg (by positivity)]
        exact hC_bound t (by linarith [ht.out])
      exact MeasureTheory.Integrable.mono' hInteg hMeas hBound
    · have := h_integral_bound T hT
      contrapose! this; rw [MeasureTheory.integral_undef this]; positivity

lemma NormXPowS {X : ℝ} (X_gt_one : 1 < X) {s : ℂ} (hs : s.re = 1 + (Real.log X)⁻¹) :
    ‖(X : ℂ) ^ s‖ = X * Real.exp 1 := by
  simp [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < X), hs,
    Real.rpow_add (by positivity : 0 < X), Real.rpow_inv_log (by positivity) X_gt_one.ne']

set_option backward.isDefEq.respectTransparency false in

@[blueprint
  (title := "I2New")
  (statement := /--
    Let
    $$I_2(\nu,\varepsilon,X,T)
      =\frac{1}{2\pi i}\int_{\sigma'}^\sigma\left(-\frac{\zeta'}{\zeta}(\sigma_0-iT)\right)
      \,\mathcal{M}(\tilde{1}_\varepsilon)(\sigma_0-iT)\,X^{\sigma_0-iT}\,d\sigma_0.$$
  -/)]
noncomputable def I2New (SmoothingF : ℝ → ℝ) (ε T X σ' : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ₀ in σ'..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₀ - T * I)))

@[blueprint
  (title := "I4New")
  (statement := /--
    Let
    $$I_4(\nu,\varepsilon,X,T)
    =\frac{1}{2\pi i}\int_{\sigma'}^\sigma\left(-\frac{\zeta'}{\zeta}(\sigma_0+iT)\right)
    \,\mathcal{M}(\tilde{1}_\varepsilon)(\sigma_0+iT)\,X^{\sigma_0+iT}\,d\sigma_0.$$
  -/)]
noncomputable def I4New (SmoothingF : ℝ → ℝ) (ε T X σ' : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ₀ in σ'..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₀ + T * I)))

@[blueprint
  (title := "I3New")
  (statement := /--
    Let
    $$I_3(\nu,\varepsilon,X,T)
      =\frac{1}{2\pi i}\int_{-T}^T\left(-\frac{\zeta'}{\zeta}(\sigma'+it)\right)
      \,\mathcal{M}(\tilde{1}_\varepsilon)(\sigma'+it)\,X^{\sigma'+it}\,dt.$$
  -/)]
noncomputable def I3New (SmoothingF : ℝ → ℝ) (ε T X σ' : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..T,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ' + t * I)))

@[blueprint
  (title := "SmoothedChebyshevPull3")
  (statement := /--
    We have that
    $$\psi_\varepsilon(X)=\mathcal{M}(\tilde{1}_\varepsilon)(1)\,X^1+I_1-I_2+I_3+I_4+I_5.$$
  -/)
  (proof := /--
    Pull contours and accumulate the pole of $\zeta'/\zeta$ at $s=1$.
  -/)]
theorem SmoothedChebyshevPull3 {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos : 0 < ε)
    (ε_lt_one : ε < 1)
    (X : ℝ) (X_gt : 3 < X)
    {T : ℝ} (T_pos : 0 < T) {σ' : ℝ}
    (σ'_pos : 0 < σ') (σ'_lt_one : σ' < 1)
    (holoOn : HolomorphicOn (ζ' / ζ) ((Icc σ' 2) ×ℂ (Icc (-T) T) \ {1}))
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
    SmoothedChebyshev SmoothingF ε X =
      I1New SmoothingF ε X T -
      I2New SmoothingF ε T X σ' +
      I3New SmoothingF ε T X σ' +
      I4New SmoothingF ε T X σ' +
      I5New SmoothingF ε X T
      + 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) 1 * X := by
    unfold SmoothedChebyshev VerticalIntegral'
    have X_eq_gt_one : 1 < 1 + (Real.log X)⁻¹ := by nth_rewrite 1 [← add_zero 1]; bound
    have X_eq_lt_two : (1 + (Real.log X)⁻¹) < 2 := by
        rw [← one_add_one_eq_two]; gcongr; exact inv_lt_one_of_one_lt₀ <| logt_gt_one X_gt.le
    have X_eq_le_two : 1 + (Real.log X)⁻¹ ≤ 2 := X_eq_lt_two.le
    rw [verticalIntegral_split_three (a := -T) (b := T)]
    swap
    ·   exact SmoothedChebyshevPull1_aux_integrable ε_pos ε_lt_one X_gt X_eq_gt_one
            X_eq_le_two suppSmoothingF SmoothingFnonneg mass_one ContDiffSmoothingF
    ·   have temp : ↑(1 + (Real.log X)⁻¹) = (1 : ℂ) + ↑(Real.log X)⁻¹ := by simp
        unfold I1New; simp only [smul_eq_mul, mul_add, temp, sub_eq_add_neg, add_assoc,
          add_left_cancel_iff]
        unfold I5New; nth_rewrite 6 [add_comm]; simp only [← add_assoc]
        rw [add_right_cancel_iff, ← add_right_inj (1 / (2 * ↑π * I) *
            -VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) (1 + (Real.log X)⁻¹) (-T) T),
            ← mul_add, ← sub_eq_neg_add, sub_self, mul_zero]
        unfold VIntegral I2New I3New I4New
        simp only [smul_eq_mul, temp, ← add_assoc, ← mul_neg, ← mul_add]
        let fTempRR : ℝ → ℝ → ℂ := fun x ↦ fun y ↦
            SmoothedChebyshevIntegrand SmoothingF ε X ((x : ℝ) + (y : ℝ) * I)
        let fTempC : ℂ → ℂ := fun z ↦ fTempRR z.re z.im
        have : ∫ (y : ℝ) in -T..T,
            SmoothedChebyshevIntegrand SmoothingF ε X (1 + ↑(Real.log X)⁻¹ + ↑y * I) =
            ∫ (y : ℝ) in -T..T, fTempRR (1 + (Real.log X)⁻¹) y := by unfold fTempRR; simp [temp]
        rw [this]
        have : ∫ (σ₀ : ℝ) in σ'..1 + (Real.log X)⁻¹,
            SmoothedChebyshevIntegrand SmoothingF ε X (↑σ₀ - ↑T * I) =
            ∫ (x : ℝ) in σ'..1 + (Real.log X)⁻¹, fTempRR x (-T) := by
            unfold fTempRR; simp [ofReal_neg, neg_mul, sub_eq_add_neg]
        rw [this]
        have : ∫ (t : ℝ) in -T..T,
            SmoothedChebyshevIntegrand SmoothingF ε X (↑σ' + ↑t * I) =
            ∫ (y : ℝ) in -T..T, fTempRR σ' y := rfl
        rw [this]
        have : ∫ (σ₀ : ℝ) in σ'..1 + (Real.log X)⁻¹,
            SmoothedChebyshevIntegrand SmoothingF ε X (↑σ₀ + ↑T * I) =
            ∫ (x : ℝ) in σ'..1 + (Real.log X)⁻¹, fTempRR x T := rfl
        rw [this]
        have : (((I * -∫ (y : ℝ) in -T..T, fTempRR (1 + (Real.log X)⁻¹) y) +
            -∫ (x : ℝ) in σ'..1 + (Real.log X)⁻¹, fTempRR x (-T)) +
            I * ∫ (y : ℝ) in -T..T, fTempRR σ' y) +
            ∫ (x : ℝ) in σ'..1 + (Real.log X)⁻¹, fTempRR x T =
            -(2 * ↑π * I) * RectangleIntegral' fTempC (σ' - T * I) (1 + ↑(Real.log X)⁻¹ + T * I) := by
            unfold RectangleIntegral' RectangleIntegral HIntegral VIntegral fTempC
            simp only [mul_neg, one_div, mul_inv_rev, inv_I, neg_mul, sub_im, ofReal_im, mul_im,
              ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_sub, ofReal_neg, add_re,
              neg_re, mul_re, sub_self, neg_zero, add_im, neg_im, zero_add, sub_re, sub_zero,
              ofReal_inv, one_re, inv_re, normSq_ofReal, div_self_mul_self', one_im, inv_im,
              zero_div, ofReal_add, ofReal_one, smul_eq_mul, neg_neg]
            ring_nf
            simp only [I_sq, neg_mul, one_mul, ne_eq, ofReal_eq_zero, pi_ne_zero, not_false_eq_true,
              mul_inv_cancel_right₀, sub_neg_eq_add, I_pow_three]
            ring_nf
        rw [this]
        field_simp
        rw [mul_comm, eq_comm, neg_add_eq_zero]
        have pInRectangleInterior : (Rectangle (σ' - ↑T * I) (1 + (Real.log X)⁻¹ + T * I) ∈ nhds 1) := by
            refine rectangle_mem_nhds_iff.mpr <| mem_reProdIm.mpr ?_
            simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
                sub_zero, ofReal_inv, add_re, one_re, inv_re, normSq_ofReal, div_self_mul_self', add_zero,
                sub_im, mul_im, zero_sub, add_im, one_im, inv_im, neg_zero, zero_div, zero_add]
            constructor
            · unfold uIoo; rw [min_eq_left (by linarith), max_eq_right (by linarith)]
              exact mem_Ioo.mpr ⟨σ'_lt_one, by linarith⟩
            · unfold uIoo; rw [min_eq_left (by linarith), max_eq_right (by linarith)]
              exact mem_Ioo.mpr ⟨by linarith, by linarith⟩
        apply ResidueTheoremOnRectangleWithSimplePole'
        · simp; linarith
        · simp; linarith
        · simp only [one_div]; exact pInRectangleInterior
        ·   apply DifferentiableOn.mul
            ·   apply DifferentiableOn.mul
                ·   simp only [re_add_im]
                    have : (fun z ↦ -ζ' z / ζ z) = -(ζ' / ζ) := by ext; simp; ring
                    rw [this]; apply DifferentiableOn.neg; apply holoOn.mono
                    apply Set.sdiff_subset_sdiff_left; apply reProdIm_subset_iff'.mpr; left
                    simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
                        sub_zero, one_div, ofReal_inv, add_re, one_re, inv_re, normSq_ofReal,
                        div_self_mul_self', add_zero, sub_im, mul_im, zero_sub, add_im, one_im, inv_im,
                        neg_zero, zero_div, zero_add]
                    constructor <;> apply uIcc_subset_Icc <;> constructor <;> linarith
                ·   intro s hs; apply DifferentiableAt.differentiableWithinAt; simp only [re_add_im]
                    apply Smooth1MellinDifferentiable ContDiffSmoothingF suppSmoothingF ⟨ε_pos, ε_lt_one⟩ SmoothingFnonneg mass_one
                    have := mem_reProdIm.mp hs.1 |>.1
                    simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
                        sub_zero, one_div, ofReal_inv, add_re, one_re, inv_re, normSq_ofReal,
                        div_self_mul_self', add_zero] at this
                    rw [uIcc_of_le (by linarith)] at this; linarith [this.1]
            ·   intro s hs; apply DifferentiableAt.differentiableWithinAt; simp only [re_add_im]
                apply DifferentiableAt.const_cpow (by fun_prop); left; norm_cast; linarith
        ·   let U : Set ℂ := Rectangle (σ' - ↑T * I) (1 + (Real.log X)⁻¹ + T * I)
            let f : ℂ → ℂ := fun z ↦ -ζ' z / ζ z
            let g : ℂ → ℂ := fun z ↦ 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) z * ↑X ^ z
            unfold fTempC fTempRR SmoothedChebyshevIntegrand
            simp only [re_add_im]
            have g_holc : HolomorphicOn g U := by
                intro u uInU
                apply DifferentiableAt.differentiableWithinAt; simp only [g]
                apply DifferentiableAt.mul
                ·   apply Smooth1MellinDifferentiable ContDiffSmoothingF suppSmoothingF ⟨ε_pos, ε_lt_one⟩ SmoothingFnonneg mass_one
                    simp only [ofReal_inv, U] at uInU; unfold Rectangle at uInU
                    rw[Complex.mem_reProdIm] at uInU; have := uInU.1
                    simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
                        sub_zero, add_re, one_re, inv_re, normSq_ofReal, div_self_mul_self', add_zero] at this
                    rw [uIcc_of_le (by linarith)] at this; linarith [this.1]
                ·   unfold HPow.hPow instHPow
                    apply DifferentiableAt.const_cpow differentiableAt_fun_id
                    left; norm_cast; linarith
            have f_near_p : (f - fun (z : ℂ) => 1 * (z - 1)⁻¹) =O[nhdsWithin 1 {1}ᶜ] (1 : ℂ → ℂ) := by
                simp only [one_mul, f]; exact riemannZetaLogDerivResidueBigO
            convert ResidueMult g_holc pInRectangleInterior f_near_p using 1
            ext; simp [f, g]; ring

blueprint_comment /--
\begin{theorem}[StrongPNT]\label{StrongPNT}
    We have
    $$\sum_{n\leq x}\Lambda(n)=x+O\left(x\exp(-c\sqrt{\log x})\right).$$
\end{theorem}
-/

blueprint_comment /--
\begin{proof}
\uses{SmoothedChebyshevClose, SmoothedChebyshevPull3, MellinOfSmooth1c, I1NewBound, I2NewBound,
  I3NewBound, I4NewBound, I5NewBound}
    By Theorem \ref{SmoothedChebyshevClose} and \ref{SmoothedChebyshevPull3} we have that
    $$\mathcal{M}(\tilde{1}_\varepsilon)(1)\,x^1+I_1-I_2+I_3+I_4+I_5
      =\psi(x)+O(\varepsilon x\log x).$$
    Applying Theorem \ref{MellinOfSmooth1c} and Lemmas \ref{I1NewBound}, \ref{I2NewBound},
    \ref{I3NewBound}, \ref{I4NewBound}, and \ref{I5NewBound} we have that
    $$\psi(x)=x+O(\varepsilon x)+O(\varepsilon x\log x)
      +O\left(\frac{x}{\varepsilon\sqrt{T}}\right)
      +O\left(\frac{x^{1-F/\log T}\sqrt{T}}{\varepsilon}\right).$$
    We absorb the $O(\varepsilon x)$ term into the $O(\varepsilon x\log x)$ term and
    balance the last two terms in $T$.
    $$\frac{x}{\varepsilon\sqrt{T}}
      =\frac{x^{1-F/\log T}\sqrt{T}}{\varepsilon}\implies T
      =\exp(\sqrt{F\log x}).$$
    Thus,
    $$\psi(x)=x+O(\varepsilon x\log x)
      +O\left(\frac{x}{\displaystyle\varepsilon\exp((1/2)\cdot\sqrt{F\log x})}\right).$$
    Now we balance the last two terms in $\varepsilon$.
    $$\varepsilon x\log x
      =\frac{x}{\displaystyle\varepsilon\exp((1/2)\cdot\sqrt{F\log x})}
      \implies\varepsilon\log x
      =\frac{\displaystyle\sqrt{\log x}}{\displaystyle\exp((1/4)\cdot\sqrt{F\log x})}.$$
    Thus,
    $$\psi(x)=x+O\left(x\exp(-(\sqrt{F}/4)\cdot\sqrt{\log x})\sqrt{\log x}\right).$$
    Absorbing the $\displaystyle\sqrt{\log x}$ into the
    $\displaystyle\exp(-(\sqrt{F}/4)\cdot\sqrt{\log x})$ completes the proof.
\end{proof}
-/

-- *** Prime Number Theorem *** The `ChebyshevPsi` function is asymptotic to `x`.
-- theorem PrimeNumberTheorem : ∃ (c : ℝ) (hc : c > 0),
--     (ChebyshevPsi - id) =O[atTop] (fun (x : ℝ) ↦ x * Real.exp (-c * Real.sqrt (Real.log x))) := by
--  sorry
