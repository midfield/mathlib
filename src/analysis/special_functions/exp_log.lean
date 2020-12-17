/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
import data.complex.exponential
import analysis.complex.basic
import analysis.calculus.mean_value
import measure_theory.borel_space

/-!
# Complex and real exponential, real logarithm

## Main statements

This file establishes the basic analytical properties of the complex and real exponential functions
(continuity, differentiability, computation of the derivative).

It also contains the definition of the real logarithm function (as the inverse of the
exponential on `(0, +∞)`, extended to `ℝ` by setting `log (-x) = log x`) and its basic
properties (continuity, differentiability, formula for the derivative).

The complex logarithm is *not* defined in this file as it relies on trigonometric functions. See
instead `trigonometric.lean`.

## Tags

exp, log
-/

noncomputable theory

open finset filter metric asymptotics set function
open_locale classical topological_space

namespace complex

/-- The complex exponential is everywhere differentiable, with the derivative `exp x`. -/
lemma has_deriv_at_exp (x : ℂ) : has_deriv_at exp (exp x) x :=
begin
  rw has_deriv_at_iff_is_o_nhds_zero,
  have : (1 : ℕ) < 2 := by norm_num,
  refine (is_O.of_bound (∥exp x∥) _).trans_is_o (is_o_pow_id this),
  filter_upwards [metric.ball_mem_nhds (0 : ℂ) zero_lt_one],
  simp only [metric.mem_ball, dist_zero_right, normed_field.norm_pow],
  intros z hz,
  calc ∥exp (x + z) - exp x - z * exp x∥
    = ∥exp x * (exp z - 1 - z)∥ : by { congr, rw [exp_add], ring }
    ... = ∥exp x∥ * ∥exp z - 1 - z∥ : normed_field.norm_mul _ _
    ... ≤ ∥exp x∥ * ∥z∥^2 :
      mul_le_mul_of_nonneg_left (abs_exp_sub_one_sub_id_le (le_of_lt hz)) (norm_nonneg _)
end

lemma differentiable_exp : differentiable ℂ exp :=
λx, (has_deriv_at_exp x).differentiable_at

lemma differentiable_at_exp {x : ℂ} : differentiable_at ℂ exp x :=
differentiable_exp x

@[simp] lemma deriv_exp : deriv exp = exp :=
funext $ λ x, (has_deriv_at_exp x).deriv

@[simp] lemma iter_deriv_exp : ∀ n : ℕ, (deriv^[n] exp) = exp
| 0 := rfl
| (n+1) := by rw [iterate_succ_apply, deriv_exp, iter_deriv_exp n]

lemma continuous_exp : continuous exp :=
differentiable_exp.continuous

lemma times_cont_diff_exp : ∀ {n}, times_cont_diff ℂ n exp :=
begin
  refine times_cont_diff_all_iff_nat.2 (λ n, _),
  induction n with n ihn,
  { exact times_cont_diff_zero.2 continuous_exp },
  { rw times_cont_diff_succ_iff_deriv,
    use differentiable_exp,
    rwa deriv_exp }
end

lemma measurable_exp : measurable exp := continuous_exp.measurable

end complex

section
variables {f : ℂ → ℂ} {f' x : ℂ} {s : set ℂ}

lemma has_deriv_at.cexp (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, complex.exp (f x)) (complex.exp (f x) * f') x :=
(complex.has_deriv_at_exp (f x)).comp x hf

lemma has_deriv_within_at.cexp (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, complex.exp (f x)) (complex.exp (f x) * f') s x :=
(complex.has_deriv_at_exp (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_cexp (hf : differentiable_within_at ℂ f s x)
  (hxs : unique_diff_within_at ℂ s x) :
  deriv_within (λx, complex.exp (f x)) s x = complex.exp (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.cexp.deriv_within hxs

@[simp] lemma deriv_cexp (hc : differentiable_at ℂ f x) :
  deriv (λx, complex.exp (f x)) x = complex.exp (f x) * (deriv f x) :=
hc.has_deriv_at.cexp.deriv

end

section

variables {E : Type*} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {f' : E →L[ℂ] ℂ}
  {x : E} {s : set E}

lemma measurable.cexp {α : Type*} [measurable_space α] {f : α → ℂ} (hf : measurable f) :
  measurable (λ x, complex.exp (f x)) :=
complex.measurable_exp.comp hf

lemma has_fderiv_within_at.cexp (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, complex.exp (f x)) (complex.exp (f x) • f') s x :=
(complex.has_deriv_at_exp (f x)).comp_has_fderiv_within_at x hf

lemma has_fderiv_at.cexp (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, complex.exp (f x)) (complex.exp (f x) • f') x :=
has_fderiv_within_at_univ.1 $ hf.has_fderiv_within_at.cexp

lemma differentiable_within_at.cexp (hf : differentiable_within_at ℂ f s x) :
  differentiable_within_at ℂ (λ x, complex.exp (f x)) s x :=
hf.has_fderiv_within_at.cexp.differentiable_within_at

@[simp] lemma differentiable_at.cexp (hc : differentiable_at ℂ f x) :
  differentiable_at ℂ (λx, complex.exp (f x)) x :=
hc.has_fderiv_at.cexp.differentiable_at

lemma differentiable_on.cexp (hc : differentiable_on ℂ f s) :
  differentiable_on ℂ (λx, complex.exp (f x)) s :=
λx h, (hc x h).cexp

@[simp] lemma differentiable.cexp (hc : differentiable ℂ f) :
  differentiable ℂ (λx, complex.exp (f x)) :=
λx, (hc x).cexp

lemma times_cont_diff.cexp {n} (h : times_cont_diff ℂ n f) :
  times_cont_diff ℂ n (λ x, complex.exp (f x)) :=
complex.times_cont_diff_exp.comp h

lemma times_cont_diff_at.cexp {n} (hf : times_cont_diff_at ℂ n f x) :
  times_cont_diff_at ℂ n (λ x, complex.exp (f x)) x :=
complex.times_cont_diff_exp.times_cont_diff_at.comp x hf

lemma times_cont_diff_on.cexp {n} (hf : times_cont_diff_on ℂ n f s) :
  times_cont_diff_on ℂ n (λ x, complex.exp (f x)) s :=
complex.times_cont_diff_exp.comp_times_cont_diff_on  hf

lemma times_cont_diff_within_at.cexp {n} (hf : times_cont_diff_within_at ℂ n f s x) :
  times_cont_diff_within_at ℂ n (λ x, complex.exp (f x)) s x :=
complex.times_cont_diff_exp.times_cont_diff_at.comp_times_cont_diff_within_at x hf

end

namespace real

variables {x y z : ℝ}

lemma has_deriv_at_exp (x : ℝ) : has_deriv_at exp (exp x) x :=
(complex.has_deriv_at_exp x).real_of_complex

lemma times_cont_diff_exp {n} : times_cont_diff ℝ n exp :=
complex.times_cont_diff_exp.real_of_complex

lemma differentiable_exp : differentiable ℝ exp :=
λx, (has_deriv_at_exp x).differentiable_at

lemma differentiable_at_exp : differentiable_at ℝ exp x :=
differentiable_exp x

@[simp] lemma deriv_exp : deriv exp = exp :=
funext $ λ x, (has_deriv_at_exp x).deriv

@[simp] lemma iter_deriv_exp : ∀ n : ℕ, (deriv^[n] exp) = exp
| 0 := rfl
| (n+1) := by rw [iterate_succ_apply, deriv_exp, iter_deriv_exp n]

lemma continuous_exp : continuous exp :=
differentiable_exp.continuous

lemma measurable_exp : measurable exp := continuous_exp.measurable

end real


section
/-! Register lemmas for the derivatives of the composition of `real.exp` with a differentiable
function, for standalone use and use with `simp`. -/

variables {f : ℝ → ℝ} {f' x : ℝ} {s : set ℝ}

lemma has_deriv_at.exp (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, real.exp (f x)) (real.exp (f x) * f') x :=
(real.has_deriv_at_exp (f x)).comp x hf

lemma has_deriv_within_at.exp (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, real.exp (f x)) (real.exp (f x) * f') s x :=
(real.has_deriv_at_exp (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_exp (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  deriv_within (λx, real.exp (f x)) s x = real.exp (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.exp.deriv_within hxs

@[simp] lemma deriv_exp (hc : differentiable_at ℝ f x) :
  deriv (λx, real.exp (f x)) x = real.exp (f x) * (deriv f x) :=
hc.has_deriv_at.exp.deriv

end

section
/-! Register lemmas for the derivatives of the composition of `real.exp` with a differentiable
function, for standalone use and use with `simp`. -/

variables {E : Type*} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {f' : E →L[ℝ] ℝ}
  {x : E} {s : set E}

lemma measurable.exp {α : Type*} [measurable_space α] {f : α → ℝ} (hf : measurable f) :
  measurable (λ x, real.exp (f x)) :=
real.measurable_exp.comp hf

lemma times_cont_diff.exp {n} (hf : times_cont_diff ℝ n f) :
  times_cont_diff ℝ n (λ x, real.exp (f x)) :=
real.times_cont_diff_exp.comp hf

lemma times_cont_diff_at.exp {n} (hf : times_cont_diff_at ℝ n f x) :
  times_cont_diff_at ℝ n (λ x, real.exp (f x)) x :=
real.times_cont_diff_exp.times_cont_diff_at.comp x hf

lemma times_cont_diff_on.exp {n} (hf : times_cont_diff_on ℝ n f s) :
  times_cont_diff_on ℝ n (λ x, real.exp (f x)) s :=
real.times_cont_diff_exp.comp_times_cont_diff_on  hf

lemma times_cont_diff_within_at.exp {n} (hf : times_cont_diff_within_at ℝ n f s x) :
  times_cont_diff_within_at ℝ n (λ x, real.exp (f x)) s x :=
real.times_cont_diff_exp.times_cont_diff_at.comp_times_cont_diff_within_at x hf

lemma has_fderiv_within_at.exp (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, real.exp (f x)) (real.exp (f x) • f') s x :=
begin
  convert (has_deriv_at_iff_has_fderiv_at.1 $
    real.has_deriv_at_exp (f x)).comp_has_fderiv_within_at x hf,
  ext y, simp [mul_comm]
end

lemma has_fderiv_at.exp (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, real.exp (f x)) (real.exp (f x) • f') x :=
has_fderiv_within_at_univ.1 $ hf.has_fderiv_within_at.exp

lemma differentiable_within_at.exp (hf : differentiable_within_at ℝ f s x) :
  differentiable_within_at ℝ (λ x, real.exp (f x)) s x :=
hf.has_fderiv_within_at.exp.differentiable_within_at

@[simp] lemma differentiable_at.exp (hc : differentiable_at ℝ f x) :
  differentiable_at ℝ (λx, real.exp (f x)) x :=
hc.has_fderiv_at.exp.differentiable_at

lemma differentiable_on.exp (hc : differentiable_on ℝ f s) :
  differentiable_on ℝ (λx, real.exp (f x)) s :=
λx h, (hc x h).exp

@[simp] lemma differentiable.exp (hc : differentiable ℝ f) :
  differentiable ℝ (λx, real.exp (f x)) :=
λx, (hc x).exp

lemma fderiv_within_exp (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  fderiv_within ℝ (λx, real.exp (f x)) s x = real.exp (f x) • (fderiv_within ℝ f s x) :=
hf.has_fderiv_within_at.exp.fderiv_within hxs

@[simp] lemma fderiv_exp (hc : differentiable_at ℝ f x) :
  fderiv ℝ (λx, real.exp (f x)) x = real.exp (f x) • (fderiv ℝ f x) :=
hc.has_fderiv_at.exp.fderiv

end

namespace real

variables {x y z : ℝ}

/-- The real exponential function tends to `+∞` at `+∞`. -/
lemma tendsto_exp_at_top : tendsto exp at_top at_top :=
begin
  have A : tendsto (λx:ℝ, x + 1) at_top at_top :=
    tendsto_at_top_add_const_right at_top 1 tendsto_id,
  have B : ∀ᶠ x in at_top, x + 1 ≤ exp x :=
    eventually_at_top.2 ⟨0, λx hx, add_one_le_exp_of_nonneg hx⟩,
  exact tendsto_at_top_mono' at_top B A
end

/-- The real exponential function tends to `0` at `-∞` or, equivalently, `exp(-x)` tends to `0`
at `+∞` -/
lemma tendsto_exp_neg_at_top_nhds_0 : tendsto (λx, exp (-x)) at_top (𝓝 0) :=
(tendsto_inv_at_top_zero.comp tendsto_exp_at_top).congr (λx, (exp_neg x).symm)

/-- The real exponential function tends to `1` at `0`. -/
lemma tendsto_exp_nhds_0_nhds_1 : tendsto exp (𝓝 0) (𝓝 1) :=
by { convert continuous_exp.tendsto 0, simp }

lemma tendsto_exp_at_bot : tendsto exp at_bot (𝓝 0) :=
(tendsto_exp_neg_at_top_nhds_0.comp tendsto_neg_at_bot_at_top).congr $
  λ x, congr_arg exp $ neg_neg x

lemma tendsto_exp_at_bot_nhds_within : tendsto exp at_bot (𝓝[Ioi 0] 0) :=
tendsto_inf.2 ⟨tendsto_exp_at_bot, tendsto_principal.2 $ eventually_of_forall exp_pos⟩

/-- `real.exp` as an order isomorphism between `ℝ` and `(0, +∞)`. -/
def exp_order_iso : ℝ ≃o Ioi (0 : ℝ) :=
strict_mono.order_iso_of_surjective _ (exp_strict_mono.cod_restrict exp_pos) $
  surjective_of_continuous (continuous_subtype_mk _ continuous_exp)
    (by simp only [tendsto_Ioi_at_top, coe_cod_restrict_apply, tendsto_exp_at_top])
    (by simp [tendsto_exp_at_bot_nhds_within])

@[simp] lemma coe_exp_order_iso_apply (x : ℝ) : (exp_order_iso x : ℝ) = exp x := rfl

@[simp] lemma coe_comp_exp_order_iso : coe ∘ exp_order_iso = exp := rfl

@[simp] lemma range_exp : range exp = Ioi 0 :=
by rw [← coe_comp_exp_order_iso, range_comp, exp_order_iso.range_eq, image_univ, subtype.range_coe]

@[simp] lemma map_exp_at_top : map exp at_top = at_top :=
by rw [← coe_comp_exp_order_iso, ← filter.map_map, order_iso.map_at_top, map_coe_Ioi_at_top]

@[simp] lemma comap_exp_at_top : comap exp at_top = at_top :=
by rw [← map_exp_at_top, comap_map exp_injective, map_exp_at_top]

@[simp] lemma tendsto_exp_comp_at_top {α : Type*} {l : filter α} {f : α → ℝ} :
  tendsto (λ x, exp (f x)) l at_top ↔ tendsto f l at_top :=
by rw [← tendsto_comap_iff, comap_exp_at_top]

lemma tendsto_comp_exp_at_top {α : Type*} {l : filter α} {f : ℝ → α} :
  tendsto (λ x, f (exp x)) at_top l ↔ tendsto f at_top l :=
by rw [← tendsto_map'_iff, map_exp_at_top]

@[simp] lemma map_exp_at_bot : map exp at_bot = 𝓝[Ioi 0] 0 :=
by rw [← coe_comp_exp_order_iso, ← filter.map_map, exp_order_iso.map_at_bot, ← map_coe_Ioi_at_bot]

lemma comap_exp_nhds_within_Ioi_zero : comap exp (𝓝[Ioi 0] 0) = at_bot :=
by rw [← map_exp_at_bot, comap_map exp_injective]

lemma tendsto_comp_exp_at_bot {α : Type*} {l : filter α} {f : ℝ → α} :
  tendsto (λ x, f (exp x)) at_bot l ↔ tendsto f (𝓝[Ioi 0] 0) l :=
by rw [← map_exp_at_bot, tendsto_map'_iff]

/-- The real logarithm function, equal to the inverse of the exponential for `x > 0`,
to `log |x|` for `x < 0`, and to `0` for `0`. We use this unconventional extension to
`(-∞, 0]` as it gives the formula `log (x * y) = log x + log y` for all nonzero `x` and `y`, and
the derivative of `log` is `1/x` away from `0`. -/
@[pp_nodot] noncomputable def log (x : ℝ) : ℝ :=
if hx : x = 0 then 0 else exp_order_iso.symm ⟨abs x, abs_pos.2 hx⟩

lemma log_of_ne_zero (hx : x ≠ 0) : log x = exp_order_iso.symm ⟨abs x, abs_pos.2 hx⟩ := dif_neg hx

lemma log_of_pos (hx : 0 < x) : log x = exp_order_iso.symm ⟨x, hx⟩ :=
by { rw [log_of_ne_zero hx.ne'], congr, exact abs_of_pos hx }

lemma exp_log_eq_abs (hx : x ≠ 0) : exp (log x) = abs x :=
by rw [log_of_ne_zero hx, ← coe_exp_order_iso_apply, order_iso.apply_symm_apply, subtype.coe_mk]

lemma exp_log (hx : 0 < x) : exp (log x) = x :=
by { rw exp_log_eq_abs hx.ne', exact abs_of_pos hx }

lemma exp_log_of_neg (hx : x < 0) : exp (log x) = -x :=
by { rw exp_log_eq_abs (ne_of_lt hx), exact abs_of_neg hx }

@[simp] lemma log_exp (x : ℝ) : log (exp x) = x :=
exp_injective $ exp_log (exp_pos x)

lemma surj_on_log : surj_on log (Ioi 0) univ :=
λ x _, ⟨exp x, exp_pos x, log_exp x⟩

lemma log_surjective : surjective log :=
λ x, ⟨exp x, log_exp x⟩

@[simp] lemma range_log : range log = univ :=
log_surjective.range_eq

@[simp] lemma log_zero : log 0 = 0 := dif_pos rfl

@[simp] lemma log_one : log 1 = 0 :=
exp_injective $ by rw [exp_log zero_lt_one, exp_zero]

@[simp] lemma log_abs (x : ℝ) : log (abs x) = log x :=
begin
  by_cases h : x = 0,
  { simp [h] },
  { rw [← exp_eq_exp, exp_log_eq_abs h, exp_log_eq_abs (abs_pos.2 h).ne', abs_abs] }
end

@[simp] lemma log_neg_eq_log (x : ℝ) : log (-x) = log x :=
by rw [← log_abs x, ← log_abs (-x), abs_neg]

lemma surj_on_log' : surj_on log (Iio 0) univ :=
λ x _, ⟨-exp x, neg_lt_zero.2 $ exp_pos x, by rw [log_neg_eq_log, log_exp]⟩

lemma log_mul (hx : x ≠ 0) (hy : y ≠ 0) : log (x * y) = log x + log y :=
exp_injective $
by rw [exp_log_eq_abs (mul_ne_zero hx hy), exp_add, exp_log_eq_abs hx, exp_log_eq_abs hy, abs_mul]

@[simp] lemma log_inv (x : ℝ) : log (x⁻¹) = -log x :=
begin
  by_cases hx : x = 0, { simp [hx] },
  rw [← exp_eq_exp, exp_log_eq_abs (inv_ne_zero hx), exp_neg, exp_log_eq_abs hx, abs_inv]
end

lemma log_le_log (h : 0 < x) (h₁ : 0 < y) : real.log x ≤ real.log y ↔ x ≤ y :=
by rw [← exp_le_exp, exp_log h, exp_log h₁]

lemma log_lt_log (hx : 0 < x) : x < y → log x < log y :=
by { intro h, rwa [← exp_lt_exp, exp_log hx, exp_log (lt_trans hx h)] }

lemma log_lt_log_iff (hx : 0 < x) (hy : 0 < y) : log x < log y ↔ x < y :=
by { rw [← exp_lt_exp, exp_log hx, exp_log hy] }

lemma log_pos_iff (hx : 0 < x) : 0 < log x ↔ 1 < x :=
by { rw ← log_one, exact log_lt_log_iff zero_lt_one hx }

lemma log_pos (hx : 1 < x) : 0 < log x :=
(log_pos_iff (lt_trans zero_lt_one hx)).2 hx

lemma log_neg_iff (h : 0 < x) : log x < 0 ↔ x < 1 :=
by { rw ← log_one, exact log_lt_log_iff h zero_lt_one }

lemma log_neg (h0 : 0 < x) (h1 : x < 1) : log x < 0 := (log_neg_iff h0).2 h1

lemma log_nonneg_iff (hx : 0 < x) : 0 ≤ log x ↔ 1 ≤ x :=
by rw [← not_lt, log_neg_iff hx, not_lt]

lemma log_nonneg (hx : 1 ≤ x) : 0 ≤ log x :=
(log_nonneg_iff (zero_lt_one.trans_le hx)).2 hx

lemma log_nonpos_iff (hx : 0 < x) : log x ≤ 0 ↔ x ≤ 1 :=
by rw [← not_lt, log_pos_iff hx, not_lt]

lemma log_nonpos_iff' (hx : 0 ≤ x) : log x ≤ 0 ↔ x ≤ 1 :=
begin
  rcases hx.eq_or_lt with (rfl|hx),
  { simp [le_refl, zero_le_one] },
  exact log_nonpos_iff hx
end

lemma log_nonpos (hx : 0 ≤ x) (h'x : x ≤ 1) : log x ≤ 0 :=
(log_nonpos_iff' hx).2 h'x

lemma strict_mono_incr_on_log : strict_mono_incr_on log (set.Ioi 0) :=
λ x hx y hy hxy, log_lt_log hx hxy

lemma strict_mono_decr_on_log : strict_mono_decr_on log (set.Iio 0) :=
begin
  rintros x (hx : x < 0) y (hy : y < 0) hxy,
  rw [← log_abs y, ← log_abs x],
  refine log_lt_log (abs_pos.2 hy.ne) _,
  rwa [abs_of_neg hy, abs_of_neg hx, neg_lt_neg_iff]
end

/-- The real logarithm function tends to `+∞` at `+∞`. -/
lemma tendsto_log_at_top : tendsto log at_top at_top :=
tendsto_comp_exp_at_top.1 $ by simpa only [log_exp] using tendsto_id

lemma tendsto_log_nhds_within_zero : tendsto log (𝓝[{0}ᶜ] 0) at_bot :=
begin
  rw [← (show _ = log, from funext log_abs)],
  refine tendsto.comp _ tendsto_abs_nhds_within_zero,
  simpa [← tendsto_comp_exp_at_bot] using tendsto_id
end

lemma continuous_on_log : continuous_on log {0}ᶜ :=
begin
  rw [continuous_on_iff_continuous_restrict, restrict],
  conv in (log _) { rw [log_of_ne_zero (show (x : ℝ) ≠ 0, from x.2)] },
  exact exp_order_iso.symm.continuous.comp (continuous_subtype_mk _ continuous_subtype_coe.norm)
end

lemma continuous_log' : continuous (λ x : {x : ℝ // 0 < x}, log x) :=
continuous_on_iff_continuous_restrict.1 $ continuous_on_log.mono $ λ x hx, ne_of_gt hx

lemma continuous_at_log (hx : x ≠ 0) : continuous_at log x :=
(continuous_on_log x hx).continuous_at $ mem_nhds_sets is_open_compl_singleton hx

@[simp] lemma continuous_at_log_iff : continuous_at log x ↔ x ≠ 0 :=
begin
  refine ⟨_, continuous_at_log⟩,
  rintros h rfl,
  exact not_tendsto_nhds_of_tendsto_at_bot tendsto_log_nhds_within_zero _
    (h.tendsto.mono_left inf_le_left)
end

lemma has_deriv_at_log_of_pos (hx : 0 < x) : has_deriv_at log x⁻¹ x :=
have has_deriv_at log (exp $ log x)⁻¹ x,
from (has_deriv_at_exp $ log x).of_local_left_inverse (continuous_at_log hx.ne')
  (ne_of_gt $ exp_pos _) $ eventually.mono (lt_mem_nhds hx) @exp_log,
by rwa [exp_log hx] at this

lemma has_deriv_at_log (hx : x ≠ 0) : has_deriv_at log x⁻¹ x :=
begin
  cases hx.lt_or_lt with hx hx,
  { convert (has_deriv_at_log_of_pos (neg_pos.mpr hx)).comp x (has_deriv_at_neg x),
    { ext y, exact (log_neg_eq_log y).symm },
    { field_simp [hx.ne] } },
  { exact has_deriv_at_log_of_pos hx }
end

lemma differentiable_at_log (hx : x ≠ 0) : differentiable_at ℝ log x :=
(has_deriv_at_log hx).differentiable_at

lemma differentiable_on_log : differentiable_on ℝ log {0}ᶜ :=
λ x hx, (differentiable_at_log hx).differentiable_within_at

@[simp] lemma differentiable_at_log_iff : differentiable_at ℝ log x ↔ x ≠ 0 :=
⟨λ h, continuous_at_log_iff.1 h.continuous_at, differentiable_at_log⟩

lemma deriv_log (x : ℝ) : deriv log x = x⁻¹ :=
if hx : x = 0 then
  by rw [deriv_zero_of_not_differentiable_at (mt differentiable_at_log_iff.1 (not_not.2 hx)), hx,
    inv_zero]
else (has_deriv_at_log hx).deriv

@[simp] lemma deriv_log' : deriv log = has_inv.inv := funext deriv_log

lemma measurable_log : measurable log :=
measurable_of_measurable_on_compl_singleton 0 $ continuous.measurable $
  continuous_on_iff_continuous_restrict.1 continuous_on_log

lemma times_cont_diff_on_log {n : with_top ℕ} : times_cont_diff_on ℝ n log {0}ᶜ :=
begin
  suffices : times_cont_diff_on ℝ ⊤ log {0}ᶜ, from this.of_le le_top,
  refine (times_cont_diff_on_top_iff_deriv_of_open is_open_compl_singleton).2 _,
  simp [differentiable_on_log, times_cont_diff_on_inv]
end

lemma times_cont_diff_at_log (hx : x ≠ 0) {n : with_top ℕ} : times_cont_diff_at ℝ n log x :=
(times_cont_diff_on_log x hx).times_cont_diff_at $ mem_nhds_sets is_open_compl_singleton hx

end real

section log_differentiable
open real

section continuity

variables {α : Type*}

lemma filter.tendsto.log {f : α → ℝ} {l : filter α} {x : ℝ} (h : tendsto f l (𝓝 x)) (hx : x ≠ 0) :
  tendsto (λ x, log (f x)) l (𝓝 (log x)) :=
(continuous_at_log hx).tendsto.comp h

variables [topological_space α] {f : α → ℝ} {s : set α} {a : α}

lemma continuous.log (hf : continuous f) (h₀ : ∀ x, f x ≠ 0) : continuous (λ x, log (f x)) :=
continuous_on_log.comp_continuous hf h₀

lemma continuous_at.log (hf : continuous_at f a) (h₀ : f a ≠ 0) :
  continuous_at (λ x, log (f x)) a :=
hf.log h₀

lemma continuous_within_at.log (hf : continuous_within_at f s a) (h₀ : f a ≠ 0) :
  continuous_within_at (λ x, log (f x)) s a :=
hf.log h₀

lemma continuous_on.log (hf : continuous_on f s) (h₀ : ∀ x ∈ s, f x ≠ 0) :
  continuous_on (λ x, log (f x)) s :=
λ x hx, (hf x hx).log (h₀ x hx)

end continuity

section deriv

variables {f : ℝ → ℝ} {x f' : ℝ} {s : set ℝ}

lemma measurable.log {α : Type*} [measurable_space α] {f : α → ℝ} (hf : measurable f) :
  measurable (λ x, log (f x)) :=
measurable_log.comp hf

lemma has_deriv_within_at.log (hf : has_deriv_within_at f f' s x) (hx : f x ≠ 0) :
  has_deriv_within_at (λ y, log (f y)) (f' / (f x)) s x :=
begin
  rw div_eq_inv_mul,
  exact (has_deriv_at_log hx).comp_has_deriv_within_at x hf
end

lemma has_deriv_at.log (hf : has_deriv_at f f' x) (hx : f x ≠ 0) :
  has_deriv_at (λ y, log (f y)) (f' / f x) x :=
begin
  rw ← has_deriv_within_at_univ at *,
  exact hf.log hx
end

lemma deriv_within.log (hf : differentiable_within_at ℝ f s x) (hx : f x ≠ 0)
  (hxs : unique_diff_within_at ℝ s x) :
  deriv_within (λx, log (f x)) s x = (deriv_within f s x) / (f x) :=
(hf.has_deriv_within_at.log hx).deriv_within hxs

@[simp] lemma deriv.log (hf : differentiable_at ℝ f x) (hx : f x ≠ 0) :
  deriv (λx, log (f x)) x = (deriv f x) / (f x) :=
(hf.has_deriv_at.log hx).deriv

end deriv

section fderiv

variables {E : Type*} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} {f' : E →L[ℝ] ℝ}
  {s : set E}

lemma has_fderiv_within_at.log (hf : has_fderiv_within_at f f' s x) (hx : f x ≠ 0) :
  has_fderiv_within_at (λ x, log (f x)) ((f x)⁻¹ • f') s x :=
(has_deriv_at_log hx).comp_has_fderiv_within_at x hf

lemma has_fderiv_at.log (hf : has_fderiv_at f f' x) (hx : f x ≠ 0) :
  has_fderiv_at (λ x, log (f x)) ((f x)⁻¹ • f') x :=
(has_deriv_at_log hx).comp_has_fderiv_at x hf

lemma differentiable_within_at.log (hf : differentiable_within_at ℝ f s x) (hx : f x ≠ 0) :
  differentiable_within_at ℝ (λx, log (f x)) s x :=
(hf.has_fderiv_within_at.log hx).differentiable_within_at

@[simp] lemma differentiable_at.log (hf : differentiable_at ℝ f x) (hx : f x ≠ 0) :
  differentiable_at ℝ (λx, log (f x)) x :=
(hf.has_fderiv_at.log hx).differentiable_at

lemma differentiable_on.log (hf : differentiable_on ℝ f s) (hx : ∀ x ∈ s, f x ≠ 0) :
  differentiable_on ℝ (λx, log (f x)) s :=
λx h, (hf x h).log (hx x h)

@[simp] lemma differentiable.log (hf : differentiable ℝ f) (hx : ∀ x, f x ≠ 0) :
  differentiable ℝ (λx, log (f x)) :=
λx, (hf x).log (hx x)

lemma fderiv_within.log (hf : differentiable_within_at ℝ f s x) (hx : f x ≠ 0)
  (hxs : unique_diff_within_at ℝ s x) :
  fderiv_within ℝ (λx, log (f x)) s x = (f x)⁻¹ • fderiv_within ℝ f s x :=
(hf.has_fderiv_within_at.log hx).fderiv_within hxs

@[simp] lemma fderiv.log (hf : differentiable_at ℝ f x) (hx : f x ≠ 0) :
  fderiv ℝ (λx, log (f x)) x = (f x)⁻¹ • fderiv ℝ f x :=
(hf.has_fderiv_at.log hx).fderiv

end fderiv

end log_differentiable

namespace real

/-- The function `exp(x)/x^n` tends to `+∞` at `+∞`, for any natural number `n` -/
lemma tendsto_exp_div_pow_at_top (n : ℕ) : tendsto (λx, exp x / x^n) at_top at_top :=
begin
  have n_pos : (0 : ℝ) < n + 1 := nat.cast_add_one_pos n,
  have n_ne_zero : (n : ℝ) + 1 ≠ 0 := ne_of_gt n_pos,
  have A : ∀x:ℝ, 0 < x → exp (x / (n+1)) / (n+1)^n ≤ exp x / x^n,
  { assume x hx,
    let y := x / (n+1),
    have y_pos : 0 < y := div_pos hx n_pos,
    have : exp (x / (n+1)) ≤ (n+1)^n * (exp x / x^n), from calc
      exp y = exp y * 1 : by simp
      ... ≤ exp y * (exp y / y)^n : begin
          apply mul_le_mul_of_nonneg_left (one_le_pow_of_one_le _ n) (le_of_lt (exp_pos _)),
          rw one_le_div y_pos,
          apply le_trans _ (add_one_le_exp_of_nonneg (le_of_lt y_pos)),
          exact le_add_of_le_of_nonneg (le_refl _) (zero_le_one)
        end
      ... = exp y * exp (n * y) / y^n :
        by rw [div_pow, exp_nat_mul, mul_div_assoc]
      ... = exp ((n + 1) * y) / y^n :
        by rw [← exp_add, add_mul, one_mul, add_comm]
      ... = exp x / (x / (n+1))^n :
        by { dsimp [y], rw mul_div_cancel' _ n_ne_zero }
      ... = (n+1)^n * (exp x / x^n) :
        by rw [← mul_div_assoc, div_pow, div_div_eq_mul_div, mul_comm],
    rwa div_le_iff' (pow_pos n_pos n) },
  have B : ∀ᶠ x in at_top, exp (x / (n+1)) / (n+1)^n ≤ exp x / x^n :=
    mem_at_top_sets.2 ⟨1, λx hx, A _ (lt_of_lt_of_le zero_lt_one hx)⟩,
  have C : tendsto (λx, exp (x / (n+1)) / (n+1)^n) at_top at_top :=
    (tendsto_exp_at_top.comp (tendsto_id.at_top_div_const
      (nat.cast_add_one_pos n))).at_top_div_const (pow_pos n_pos n),
  exact tendsto_at_top_mono' at_top B C
end

/-- The function `x^n * exp(-x)` tends to `0` at `+∞`, for any natural number `n`. -/
lemma tendsto_pow_mul_exp_neg_at_top_nhds_0 (n : ℕ) : tendsto (λx, x^n * exp (-x)) at_top (𝓝 0) :=
(tendsto_inv_at_top_zero.comp (tendsto_exp_div_pow_at_top n)).congr $ λx,
  by rw [comp_app, inv_eq_one_div, div_div_eq_mul_div, one_mul, div_eq_mul_inv, exp_neg]

/-- The function `(b * exp x + c) / (x ^ n)` tends to `+∞` at `+∞`, for any positive natural number
`n` and any real numbers `b` and `c` such that `b` is positive. -/
lemma tendsto_mul_exp_add_div_pow_at_top (b c : ℝ) (n : ℕ) (hb : 0 < b) (hn : 1 ≤ n) :
  tendsto (λ x, (b * (exp x) + c) / (x^n)) at_top at_top :=
begin
  refine tendsto.congr' (eventually_eq_of_mem (Ioi_mem_at_top 0) _)
    (((tendsto_exp_div_pow_at_top n).const_mul_at_top hb).at_top_add
      ((tendsto_pow_neg_at_top hn).mul (@tendsto_const_nhds _ _ _ c _))),
  intros x hx,
  simp only [fpow_neg x n],
  ring,
end

/-- The function `(x ^ n) / (b * exp x + c)` tends to `0` at `+∞`, for any positive natural number
`n` and any real numbers `b` and `c` such that `b` is nonzero. -/
lemma tendsto_div_pow_mul_exp_add_at_top (b c : ℝ) (n : ℕ) (hb : 0 ≠ b) (hn : 1 ≤ n) :
  tendsto (λ x, x^n / (b * (exp x) + c)) at_top (𝓝 0) :=
begin
  have H : ∀ d e, 0 < d → tendsto (λ (x:ℝ), x^n / (d * (exp x) + e)) at_top (𝓝 0),
  { intros b' c' h,
    convert tendsto.inv_tendsto_at_top (tendsto_mul_exp_add_div_pow_at_top b' c' n h hn),
    ext x,
    simpa only [pi.inv_apply] using inv_div.symm },
  cases lt_or_gt_of_ne hb,
  { exact H b c h },
  { convert (H (-b) (-c) (neg_pos.mpr h)).neg,
    { ext x,
      field_simp,
      rw [← neg_add (b * exp x) c, neg_div_neg_eq] },
    { exact neg_zero.symm } },
end

open_locale big_operators

/-- A crude lemma estimating the difference between `log (1-x)` and its Taylor series at `0`,
where the main point of the bound is that it tends to `0`. The goal is to deduce the series
expansion of the logarithm, in `has_sum_pow_div_log_of_abs_lt_1`.
-/
lemma abs_log_sub_add_sum_range_le {x : ℝ} (h : abs x < 1) (n : ℕ) :
  abs ((∑ i in range n, x^(i+1)/(i+1)) + log (1-x)) ≤ (abs x)^(n+1) / (1 - abs x) :=
begin
  /- For the proof, we show that the derivative of the function to be estimated is small,
  and then apply the mean value inequality. -/
  let F : ℝ → ℝ := λ x, ∑ i in range n, x^(i+1)/(i+1) + log (1-x),
  -- First step: compute the derivative of `F`
  have A : ∀ y ∈ Ioo (-1 : ℝ) 1, deriv F y = - (y^n) / (1 - y),
  { assume y hy,
    have : (∑ i in range n, (↑i + 1) * y ^ i / (↑i + 1)) = (∑ i in range n, y ^ i),
    { congr' with i,
      have : (i : ℝ) + 1 ≠ 0 := ne_of_gt (nat.cast_add_one_pos i),
      field_simp [this, mul_comm] },
    field_simp [F, this, ← geom_series_def, geom_sum (ne_of_lt hy.2),
                sub_ne_zero_of_ne (ne_of_gt hy.2), sub_ne_zero_of_ne (ne_of_lt hy.2)],
    ring },
  -- second step: show that the derivative of `F` is small
  have B : ∀ y ∈ Icc (-abs x) (abs x), abs (deriv F y) ≤ (abs x)^n / (1 - abs x),
  { assume y hy,
    have : y ∈ Ioo (-(1 : ℝ)) 1 := ⟨lt_of_lt_of_le (neg_lt_neg h) hy.1, lt_of_le_of_lt hy.2 h⟩,
    calc abs (deriv F y) = abs (-(y^n) / (1 - y)) : by rw [A y this]
    ... ≤ (abs x)^n / (1 - abs x) :
      begin
        have : abs y ≤ abs x := abs_le.2 hy,
        have : 0 < 1 - abs x, by linarith,
        have : 1 - abs x ≤ abs (1 - y) := le_trans (by linarith [hy.2]) (le_abs_self _),
        simp only [← pow_abs, abs_div, abs_neg],
        apply_rules [div_le_div, pow_nonneg, abs_nonneg, pow_le_pow_of_le_left]
      end },
  -- third step: apply the mean value inequality
  have C : ∥F x - F 0∥ ≤ ((abs x)^n / (1 - abs x)) * ∥x - 0∥,
  { have : ∀ y ∈ Icc (- abs x) (abs x), differentiable_at ℝ F y,
    { assume y hy,
      have : 1 - y ≠ 0 := sub_ne_zero_of_ne (ne_of_gt (lt_of_le_of_lt hy.2 h)),
      simp [F, this] },
    apply convex.norm_image_sub_le_of_norm_deriv_le this B (convex_Icc _ _) _ _,
    { simpa using abs_nonneg x },
    { simp [le_abs_self x, neg_le.mp (neg_le_abs_self x)] } },
  -- fourth step: conclude by massaging the inequality of the third step
  simpa [F, norm_eq_abs, div_mul_eq_mul_div, pow_succ'] using C
end

/-- Power series expansion of the logarithm around `1`. -/
theorem has_sum_pow_div_log_of_abs_lt_1 {x : ℝ} (h : abs x < 1) :
  has_sum (λ (n : ℕ), x ^ (n + 1) / (n + 1)) (-log (1 - x)) :=
begin
  rw summable.has_sum_iff_tendsto_nat,
  show tendsto (λ (n : ℕ), ∑ (i : ℕ) in range n, x ^ (i + 1) / (i + 1)) at_top (𝓝 (-log (1 - x))),
  { rw [tendsto_iff_norm_tendsto_zero],
    simp only [norm_eq_abs, sub_neg_eq_add],
    refine squeeze_zero (λ n, abs_nonneg _) (abs_log_sub_add_sum_range_le h) _,
    suffices : tendsto (λ (t : ℕ), abs x ^ (t + 1) / (1 - abs x)) at_top
      (𝓝 (abs x * 0 / (1 - abs x))), by simpa,
    simp only [pow_succ],
    refine (tendsto_const_nhds.mul _).div_const,
    exact tendsto_pow_at_top_nhds_0_of_lt_1 (abs_nonneg _) h },
  show summable (λ (n : ℕ), x ^ (n + 1) / (n + 1)),
  { refine summable_of_norm_bounded _ (summable_geometric_of_lt_1 (abs_nonneg _) h) (λ i, _),
    calc ∥x ^ (i + 1) / (i + 1)∥
    = abs x ^ (i+1) / (i+1) :
      begin
        have : (0 : ℝ) ≤ i + 1 := le_of_lt (nat.cast_add_one_pos i),
        rw [norm_eq_abs, abs_div, ← pow_abs, abs_of_nonneg this],
      end
    ... ≤ abs x ^ (i+1) / (0 + 1) :
      begin
        apply_rules [div_le_div_of_le_left, pow_nonneg, abs_nonneg, add_le_add_right,
          i.cast_nonneg],
        norm_num,
      end
    ... ≤ abs x ^ i :
      by simpa [pow_succ'] using mul_le_of_le_one_right (pow_nonneg (abs_nonneg x) i) (le_of_lt h) }
end

end real
