/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import measure_theory.set_integral
import measure_theory.lebesgue_measure
import analysis.calculus.deriv

/-!
# Integral over an interval

In this file we define `∫ x in a..b, f x ∂μ` to be `∫ x in Ioc a b, f x ∂μ` if `a ≤ b`
and `-∫ x in Ioc b a, f x ∂μ` if `b ≤ a`. We prove a few simple properties and many versions
of the first part of the
[fundamental theorem of calculus](https://en.wikipedia.org/wiki/Fundamental_theorem_of_calculus).
Recall that it states that the function `(u, v) ↦ ∫ x in u..v, f x` has derivative
`(δu, δv) ↦ δv • f b - δu • f a` at `(a, b)` provided that `f` is continuous at `a` and `b`.

## Main statements

### FTC-1 for Lebesgue measure

We prove several versions of FTC-1, all in the `interval_integral` namespace. Many of them follow
the naming scheme `integral_has(_strict?)_(f?)deriv(_within?)_at(_of_tendsto_ae?)(_right|_left?)`.
They formulate FTC in terms of `has(_strict?)_(f?)deriv(_within?)_at`.
Let us explain the meaning of each part of the name:

* `_strict` means that the theorem is about strict differentiability;
* `f` means that the theorem is about differentiability in both endpoints; incompatible with
  `_right|_left`;
* `_within` means that the theorem is about one-sided derivatives, see below for details;
* `_of_tendsto_ae` means that instead of continuity the theorem assumes that `f` has a finite limit
  almost surely as `x` tends to `a` and/or `b`;
* `_right` or `_left` mean that the theorem is about differentiability in the right (resp., left)
  endpoint.

We also reformulate these theorems in terms of `(f?)deriv(_within?)`. These theorems are named
`(f?)deriv(_within?)_integral(_of_tendsto_ae?)(_right|_left?)` with the same meaning of parts of the
name.

### One-sided derivatives

Theorem `integral_has_fderiv_within_at_of_tendsto_ae` states that `(u, v) ↦ ∫ x in u..v, f x` has a
derivative `(δu, δv) ↦ δv • cb - δu • ca` within the set `s × t` at `(a, b)` provided that `f` tends
to `ca` (resp., `cb`) almost surely at `la` (resp., `lb`), where possible values of `s`, `t`, and
corresponding filters `la`, `lb` are given in the following table.

| `s`     | `la`         | `t`     | `lb`         |
| ------- | ----         | ---     | ----         |
| `Iic a` | `𝓝[Iic a] a` | `Iic b` | `𝓝[Iic b] b` |
| `Ici a` | `𝓝[Ioi a] a` | `Ici b` | `𝓝[Ioi b] b` |
| `{a}`   | `⊥`          | `{b}`   | `⊥`          |
| `univ`  | `𝓝 a`        | `univ`  | `𝓝 b`        |

We use a typeclass `FTC_filter` to make Lean automatically find `la`/`lb` based on `s`/`t`. This way
we can formulate one theorem instead of `16` (or `8` if we leave only non-trivial ones not covered
by `integral_has_deriv_within_at_of_tendsto_ae_(left|right)` and
`integral_has_fderiv_at_of_tendsto_ae`). Similarly,
`integral_has_deriv_within_at_of_tendsto_ae_right` works for both one-sided derivatives using the
same typeclass to find an appropriate filter.

### FTC for a locally finite measure

Before proving FTC for the Lebesgue measure, we prove a few statements that can be seen as FTC for
any measure. The most general of them,
`measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae`, states the following. Let `(la, la')`
be an `FTC_filter` pair of filters around `a` (i.e., `FTC_filter a la la'`) and let `(lb, lb')` be
an `FTC_filter` pair of filters around `b`. If `f` has finite limits `ca` and `cb` almost surely at
`la'` and `lb'`, respectively, then
`∫ x in va..vb, f x ∂μ - ∫ x in ua..ub, f x ∂μ = ∫ x in ub..vb, cb ∂μ - ∫ x in ua..va, ca ∂μ +
  o(∥∫ x in ua..va, (1:ℝ) ∂μ∥ + ∥∫ x in ub..vb, (1:ℝ) ∂μ∥)` as `ua` and `va` tend to `la` while
`ub` and `vb` tend to `lb`.

## Implementation notes

### Avoiding `if`, `min`, and `max`

In order to avoid `if`s in the definition, we define `interval_integrable f μ a b` as
`integrable_on f (Ioc a b) μ ∧ integrable_on f (Ioc b a) μ`. For any `a`, `b` one of these
intervals is empty and the other coincides with `Ioc (min a b) (max a b)`.

Similarly, we define `∫ x in a..b, f x ∂μ` to be `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`.
Again, for any `a`, `b` one of these integrals is zero, and the other gives the expected result.

This way some properties can be translated from integrals over sets without dealing with
the cases `a ≤ b` and `b ≤ a` separately.

### Choice of the interval

We use integral over `Ioc (min a b) (max a b)` instead of one of the other three possible
intervals with the same endpoints for two reasons:

* this way `∫ x in a..b, f x ∂μ + ∫ x in b..c, f x ∂μ = ∫ x in a..c, f x ∂μ` holds whenever
  `f` is integrable on each interval; in particular, it works even if the measure `μ` has an atom
  at `b`; this rules out `Ioo` and `Icc` intervals;
* with this definition for a probability measure `μ`, the integral `∫ x in a..b, 1 ∂μ` equals
  the difference $F_μ(b)-F_μ(a)$, where $F_μ(a)=μ(-∞, a]$ is the
  [cumulative distribution function](https://en.wikipedia.org/wiki/Cumulative_distribution_function)
  of `μ`.

### `FTC_filter` class

As explained above, many theorems in this file rely on the typeclass
`FTC_filter (a : α) (l l' : filter α)` to avoid code duplication. This typeclass combines four
assumptions:

- `pure a ≤ l`;
- `l' ≤ 𝓝 a`;
- `l'` has a basis of measurable sets;
- if `u n` and `v n` tend to `l`, then for any `s ∈ l'`, `Ioc (u n) (v n)` is eventually included
  in `s`.

This typeclass has exactly four “real” instances: `(a, pure a, ⊥)`, `(a, 𝓝[Ici a] a, 𝓝[Ioi a] a)`,
`(a, 𝓝[Iic a] a, 𝓝[Iic a] a)`, `(a, 𝓝 a, 𝓝 a)`, and two instances that are equal to the first and
last “real” instances: `(a, 𝓝[{a}] a, ⊥)` and `(a, 𝓝[univ] a, 𝓝[univ] a)`. While the difference
between `Ici a` and `Ioi a` doesn't matter for theorems about Lebesgue measure, it becomes important
in the versions of FTC about any locally finite measure if this measure has an atom at one of the
endpoints.

## Tags

integral, fundamental theorem of calculus
 -/

noncomputable theory
open topological_space (second_countable_topology)
open measure_theory set classical filter

open_locale classical topological_space filter

variables {α β 𝕜 E F : Type*} [linear_order α] [measurable_space α]
  [measurable_space E] [normed_group E]

/-!
### Integrability at an interval
-/

/-- A function `f` is called *interval integrable* with respect to a measure `μ` on an unordered
interval `a..b` if it is integrable on both intervals `(a, b]` and `(b, a]`. One of these
intervals is always empty, so this property is equivalent to `f` being integrable on
`(min a b, max a b]`. -/
def interval_integrable (f : α → E) (μ : measure α) (a b : α) :=
integrable_on f (Ioc a b) μ ∧ integrable_on f (Ioc b a) μ

lemma measure_theory.integrable.interval_integrable {f : α → E} {μ : measure α}
  (hf : integrable f μ) {a b : α} :
  interval_integrable f μ a b :=
⟨hf.integrable_on, hf.integrable_on⟩

namespace interval_integrable

section

variables {f : α → E} {a b c : α} {μ : measure α}

@[symm] lemma symm (h : interval_integrable f μ a b) : interval_integrable f μ b a :=
h.symm

@[refl] lemma refl (hf : measurable f) : interval_integrable f μ a a :=
by split; simp [hf]

@[trans] lemma trans  (hab : interval_integrable f μ a b)
  (hbc : interval_integrable f μ b c) :
  interval_integrable f μ a c :=
⟨(hab.1.union hbc.1).mono_set Ioc_subset_Ioc_union_Ioc,
  (hbc.2.union hab.2).mono_set Ioc_subset_Ioc_union_Ioc⟩

lemma neg [borel_space E] (h : interval_integrable f μ a b) : interval_integrable (-f) μ a b :=
⟨h.1.neg, h.2.neg⟩

protected lemma measurable (h : interval_integrable f μ a b) : measurable f :=
h.1.measurable

end

variables [borel_space E] {f g : α → E} {a b : α} {μ : measure α}

lemma smul [normed_field 𝕜] [normed_space 𝕜 E] {f : α → E} {a b : α} {μ : measure α}
  (h : interval_integrable f μ a b) (r : 𝕜) :
  interval_integrable (r • f) μ a b :=
⟨h.1.smul r, h.2.smul r⟩

lemma add [second_countable_topology E] (hf : interval_integrable f μ a b)
  (hg : interval_integrable g μ a b) : interval_integrable (f + g) μ a b :=
⟨hf.1.add hg.1, hf.2.add hg.2⟩

lemma sub [second_countable_topology E] (hf : interval_integrable f μ a b)
  (hg : interval_integrable g μ a b) : interval_integrable (f - g) μ a b :=
⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

end interval_integrable

section

variables {μ : measure ℝ} [locally_finite_measure μ]

lemma continuous_on.interval_integrable {u : ℝ → E} {a b : ℝ} (hu : continuous_on u (interval a b))
  (hum : measurable u) :
  interval_integrable u μ a b :=
begin
  split,
  all_goals
  { refine measure_theory.integrable_on.mono_set _ Ioc_subset_Icc_self,
    refine continuous_on.integrable_on_compact compact_Icc hum (hu.mono _) },
  { exact Icc_subset_interval },
  { exact Icc_subset_interval' }
end

/-- A continuous function on `ℝ` is `interval_integrable` with respect to any locally finite measure
`ν` on ℝ. -/
lemma continuous.interval_integrable [borel_space E] {u : ℝ → E} (hu : continuous u) (a b : ℝ) :
  interval_integrable u μ a b :=
hu.continuous_on.interval_integrable hu.measurable

end

/-- Let `l'` be a measurably generated filter; let `l` be a of filter such that each `s ∈ l'`
eventually includes `Ioc u v` as both `u` and `v` tend to `l`. Let `μ` be a measure finite at `l'`.

Suppose that `f : α → E` has a finite limit at `l' ⊓ μ.ae`. Then `f` is interval integrable on
`u..v` provided that both `u` and `v` tend to `l`.

Typeclass instances allow Lean to find `l'` based on `l` but not vice versa, so
`apply tendsto.eventually_interval_integrable_ae` will generate goals `filter α` and
`tendsto_Ixx_class Ioc ?m_1 l'`. -/
lemma filter.tendsto.eventually_interval_integrable_ae {f : α → E} (hfm : measurable f)
  {μ : measure α} {l l' : filter α} [tendsto_Ixx_class Ioc l l'] [is_measurably_generated l']
  (hμ : μ.finite_at_filter l') {c : E} (hf : tendsto f (l' ⊓ μ.ae) (𝓝 c))
  {u v : β → α} {lt : filter β} (hu : tendsto u lt l) (hv : tendsto v lt l) :
  ∀ᶠ t in lt, interval_integrable f μ (u t) (v t) :=
have _ := (hf.integrable_at_filter_ae hfm hμ).eventually,
((hu.Ioc hv).eventually this).and $ (hv.Ioc hu).eventually this

/-- Let `l'` be a measurably generated filter; let `l` be a of filter such that each `s ∈ l'`
eventually includes `Ioc u v` as both `u` and `v` tend to `l`. Let `μ` be a measure finite at `l'`.

Suppose that `f : α → E` has a finite limit at `l`. Then `f` is interval integrable on `u..v`
provided that both `u` and `v` tend to `l`.

Typeclass instances allow Lean to find `l'` based on `l` but not vice versa, so
`apply tendsto.eventually_interval_integrable_ae` will generate goals `filter α` and
`tendsto_Ixx_class Ioc ?m_1 l'`. -/
lemma filter.tendsto.eventually_interval_integrable {f : α → E} (hfm : measurable f)
  {μ : measure α} {l l' : filter α} [tendsto_Ixx_class Ioc l l'] [is_measurably_generated l']
  (hμ : μ.finite_at_filter l') {c : E} (hf : tendsto f l' (𝓝 c))
  {u v : β → α} {lt : filter β} (hu : tendsto u lt l) (hv : tendsto v lt l) :
  ∀ᶠ t in lt, interval_integrable f μ (u t) (v t) :=
(hf.mono_left inf_le_left).eventually_interval_integrable_ae hfm hμ hu hv

/-!
### Interval integral: definition and basic properties

In this section we define `∫ x in a..b, f x ∂μ` as `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`
and prove some basic properties.
-/

variables [second_countable_topology E] [complete_space E] [normed_space ℝ E]
  [borel_space E]

/-- The interval integral `∫ x in a..b, f x ∂μ` is defined
as `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`. If `a ≤ b`, then it equals
`∫ x in Ioc a b, f x ∂μ`, otherwise it equals `-∫ x in Ioc b a, f x ∂μ`. -/
def interval_integral (f : α → E) (a b : α) (μ : measure α) :=
∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ

notation `∫` binders ` in ` a `..` b `, ` r:(scoped:60 f, f) ` ∂` μ:70 := interval_integral r a b μ
notation `∫` binders ` in ` a `..` b `, ` r:(scoped:60 f, interval_integral f a b volume) := r

namespace interval_integral

section

variables {a b c d : α} {f g : α → E} {μ : measure α}

@[simp] lemma integral_zero : ∫ x in a..b, (0 : E) ∂μ = 0 :=
by simp [interval_integral]

lemma integral_of_le (h : a ≤ b) : ∫ x in a..b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ :=
by simp [interval_integral, h]

@[simp] lemma integral_same : ∫ x in a..a, f x ∂μ = 0 :=
sub_self _

lemma integral_symm (a b) : ∫ x in b..a, f x ∂μ = -∫ x in a..b, f x ∂μ :=
by simp only [interval_integral, neg_sub]

lemma integral_of_ge (h : b ≤ a) : ∫ x in a..b, f x ∂μ = -∫ x in Ioc b a, f x ∂μ :=
by simp only [integral_symm b, integral_of_le h]

lemma integral_cases (f : α → E) (a b) :
  ∫ x in a..b, f x ∂μ ∈ ({∫ x in Ioc (min a b) (max a b), f x ∂μ,
    -∫ x in Ioc (min a b) (max a b), f x ∂μ} : set E) :=
(le_total a b).imp (λ h, by simp [h, integral_of_le]) (λ h, by simp [h, integral_of_ge])

lemma integral_non_measurable {f : α → E} {a b} (hf : ¬measurable f) :
  ∫ x in a..b, f x ∂μ = 0 :=
by rw [interval_integral, integral_non_measurable hf, integral_non_measurable hf, sub_zero]

lemma norm_integral_eq_norm_integral_Ioc :
  ∥∫ x in a..b, f x ∂μ∥ = ∥∫ x in Ioc (min a b) (max a b), f x ∂μ∥ :=
(integral_cases f a b).elim (congr_arg _) (λ h, (congr_arg _ h).trans (norm_neg _))

lemma norm_integral_le_integral_norm_Ioc :
  ∥∫ x in a..b, f x ∂μ∥ ≤ ∫ x in Ioc (min a b) (max a b), ∥f x∥ ∂μ :=
calc ∥∫ x in a..b, f x ∂μ∥ = ∥∫ x in Ioc (min a b) (max a b), f x ∂μ∥ :
  norm_integral_eq_norm_integral_Ioc
... ≤ ∫ x in Ioc (min a b) (max a b), ∥f x∥ ∂μ :
  norm_integral_le_integral_norm f

lemma norm_integral_le_abs_integral_norm : ∥∫ x in a..b, f x ∂μ∥ ≤ abs (∫ x in a..b, ∥f x∥ ∂μ) :=
begin
  simp only [← real.norm_eq_abs, norm_integral_eq_norm_integral_Ioc],
  exact le_trans (norm_integral_le_integral_norm _) (le_abs_self _)
end

lemma norm_integral_le_of_norm_le_const_ae {a b C : ℝ} {f : ℝ → E}
  (h : ∀ᵐ x, x ∈ Ioc (min a b) (max a b) → ∥f x∥ ≤ C) :
  ∥∫ x in a..b, f x∥ ≤ C * abs (b - a) :=
begin
  rw [norm_integral_eq_norm_integral_Ioc],
  convert norm_set_integral_le_of_norm_le_const_ae'' _ is_measurable_Ioc h,
  { rw [real.volume_Ioc, max_sub_min_eq_abs, ennreal.to_real_of_real (abs_nonneg _)] },
  { simp only [real.volume_Ioc, ennreal.of_real_lt_top] },
end

lemma norm_integral_le_of_norm_le_const {a b C : ℝ} {f : ℝ → E}
  (h : ∀ x ∈ Ioc (min a b) (max a b), ∥f x∥ ≤ C) :
  ∥∫ x in a..b, f x∥ ≤ C * abs (b - a) :=
norm_integral_le_of_norm_le_const_ae $ eventually_of_forall h

lemma integral_add (hf : interval_integrable f μ a b) (hg : interval_integrable g μ a b) :
  ∫ x in a..b, f x + g x ∂μ = ∫ x in a..b, f x ∂μ + ∫ x in a..b, g x ∂μ :=
by { simp only [interval_integral, integral_add hf.1 hg.1, integral_add hf.2 hg.2], abel }

@[simp] lemma integral_neg : ∫ x in a..b, -f x ∂μ = -∫ x in a..b, f x ∂μ :=
by { simp only [interval_integral, integral_neg], abel }

lemma integral_sub (hf : interval_integrable f μ a b) (hg : interval_integrable g μ a b) :
  ∫ x in a..b, f x - g x ∂μ = ∫ x in a..b, f x ∂μ - ∫ x in a..b, g x ∂μ :=
by simpa only [sub_eq_add_neg] using (integral_add hf hg.neg).trans (congr_arg _ integral_neg)

lemma integral_smul (r : ℝ) : ∫ x in a..b, r • f x ∂μ = r • ∫ x in a..b, f x ∂μ :=
by simp only [interval_integral, integral_smul, smul_sub]

lemma integral_const' (c : E) :
  ∫ x in a..b, c ∂μ = ((μ $ Ioc a b).to_real - (μ $ Ioc b a).to_real) • c :=
by simp only [interval_integral, set_integral_const, sub_smul]

lemma integral_const {a b : ℝ} (c : E) : (∫ (x : ℝ) in a..b, c) = (b - a) • c :=
by simp only [integral_const', real.volume_Ioc, ennreal.to_real_of_real', ← neg_sub b,
  max_zero_sub_eq_self]

lemma integral_smul_measure (c : ennreal) :
  ∫ x in a..b, f x ∂(c • μ) = c.to_real • ∫ x in a..b, f x ∂μ :=
by simp only [interval_integral, measure.restrict_smul, integral_smul_measure, smul_sub]

lemma integral_comp_add_right (a b c : ℝ) (f : ℝ → E) (hfm : measurable f) :
  ∫ x in a..b, f (x + c) = ∫ x in a+c..b+c, f x :=
calc ∫ x in a..b, f (x + c) = ∫ x in a+c..b+c, f x ∂(measure.map (λ x, x + c) volume) :
  by simp only [interval_integral, set_integral_map is_measurable_Ioc hfm (measurable_add_right _),
    preimage_add_const_Ioc, add_sub_cancel]
... = ∫ x in a+c..b+c, f x : by rw [real.map_volume_add_right]

lemma integral_comp_mul_right {c : ℝ} (hc : 0 < c) (a b : ℝ) (f : ℝ → E) (hfm : measurable f) :
  ∫ x in a..b, f (x * c) = c⁻¹ • ∫ x in a*c..b*c, f x :=
begin
  conv_rhs { rw [← real.smul_map_volume_mul_right (ne_of_gt hc)] },
  rw [integral_smul_measure],
  simp only [interval_integral, set_integral_map is_measurable_Ioc hfm (measurable_mul_right _),
    hc, preimage_mul_const_Ioc, mul_div_cancel _ (ne_of_gt hc), abs_of_pos,
    ennreal.to_real_of_real (le_of_lt hc), inv_smul_smul' (ne_of_gt hc)]
end

lemma integral_comp_neg (a b : ℝ) (f : ℝ → E) (hfm : measurable f) :
  ∫ x in a..b, f (-x) = ∫ x in -b..-a, f x :=
begin
  conv_rhs { rw ← real.map_volume_neg },
  simp only [interval_integral, set_integral_map is_measurable_Ioc hfm measurable_neg, neg_preimage,
    preimage_neg_Ioc, neg_neg, restrict_congr_set Ico_ae_eq_Ioc]
end

/-!
### Integral is an additive function of the interval

In this section we prove that `∫ x in a..b, f x ∂μ + ∫ x in b..c, f x ∂μ = ∫ x in a..c, f x ∂μ`
as well as a few other identities trivially equivalent to this one. We also prove that
`∫ x in a..b, f x ∂μ = ∫ x, f x ∂μ` provided that `support f ⊆ Ioc a b`.
-/

variables [topological_space α] [opens_measurable_space α]

section order_closed_topology

variables [order_closed_topology α]

lemma integral_add_adjacent_intervals_cancel (hab : interval_integrable f μ a b)
  (hbc : interval_integrable f μ b c) :
  ∫ x in a..b, f x ∂μ + ∫ x in b..c, f x ∂μ + ∫ x in c..a, f x ∂μ = 0 :=
begin
  have hac := hab.trans hbc,
  simp only [interval_integral, ← add_sub_comm, sub_eq_zero],
  iterate 4 { rw ← integral_union },
  { suffices : Ioc a b ∪ Ioc b c ∪ Ioc c a = Ioc b a ∪ Ioc c b ∪ Ioc a c, by rw this,
    rw [Ioc_union_Ioc_union_Ioc_cycle, union_right_comm, Ioc_union_Ioc_union_Ioc_cycle,
      min_left_comm, max_left_comm] },
  all_goals { simp [*, is_measurable.union, is_measurable_Ioc, Ioc_disjoint_Ioc_same,
    Ioc_disjoint_Ioc_same.symm, hab.1, hab.2, hbc.1, hbc.2, hac.1, hac.2] }
end

lemma integral_add_adjacent_intervals (hab : interval_integrable f μ a b)
  (hbc : interval_integrable f μ b c) :
  ∫ x in a..b, f x ∂μ + ∫ x in b..c, f x ∂μ = ∫ x in a..c, f x ∂μ :=
by rw [← add_neg_eq_zero, ← integral_symm, integral_add_adjacent_intervals_cancel hab hbc]

lemma integral_interval_sub_left (hab : interval_integrable f μ a b)
  (hac : interval_integrable f μ a c) :
  ∫ x in a..b, f x ∂μ - ∫ x in a..c, f x ∂μ = ∫ x in c..b, f x ∂μ :=
sub_eq_of_eq_add' $ eq.symm $ integral_add_adjacent_intervals hac (hac.symm.trans hab)

lemma integral_interval_add_interval_comm (hab : interval_integrable f μ a b)
  (hcd : interval_integrable f μ c d) (hac : interval_integrable f μ a c) :
  ∫ x in a..b, f x ∂μ + ∫ x in c..d, f x ∂μ = ∫ x in a..d, f x ∂μ + ∫ x in c..b, f x ∂μ :=
by rw [← integral_add_adjacent_intervals hac hcd, add_assoc, add_left_comm,
  integral_add_adjacent_intervals hac (hac.symm.trans hab), add_comm]

lemma integral_interval_sub_interval_comm (hab : interval_integrable f μ a b)
  (hcd : interval_integrable f μ c d) (hac : interval_integrable f μ a c) :
  ∫ x in a..b, f x ∂μ - ∫ x in c..d, f x ∂μ = ∫ x in a..c, f x ∂μ - ∫ x in b..d, f x ∂μ :=
by simp only [sub_eq_add_neg, ← integral_symm,
  integral_interval_add_interval_comm hab hcd.symm (hac.trans hcd)]

lemma integral_interval_sub_interval_comm' (hab : interval_integrable f μ a b)
  (hcd : interval_integrable f μ c d) (hac : interval_integrable f μ a c) :
  ∫ x in a..b, f x ∂μ - ∫ x in c..d, f x ∂μ = ∫ x in d..b, f x ∂μ - ∫ x in c..a, f x ∂μ :=
by { rw [integral_interval_sub_interval_comm hab hcd hac, integral_symm b d, integral_symm a c,
  sub_neg_eq_add, sub_eq_neg_add],  }

lemma integral_Iic_sub_Iic (ha : integrable_on f (Iic a) μ) (hb : integrable_on f (Iic b) μ) :
  ∫ x in Iic b, f x ∂μ - ∫ x in Iic a, f x ∂μ = ∫ x in a..b, f x ∂μ :=
begin
  wlog hab : a ≤ b using [a b] tactic.skip,
  { rw [sub_eq_iff_eq_add', integral_of_le hab, ← integral_union (Iic_disjoint_Ioc (le_refl _)),
      Iic_union_Ioc_eq_Iic hab],
    exacts [is_measurable_Iic, is_measurable_Ioc, ha, hb.mono_set (λ _, and.right)] },
  { intros ha hb,
    rw [integral_symm, ← this hb ha, neg_sub] }
end

/-- If `μ` is a finite measure then `∫ x in a..b, c ∂μ = (μ (Iic b) - μ (Iic a)) • c`. -/
lemma integral_const_of_cdf [finite_measure μ] (c : E) :
  ∫ x in a..b, c ∂μ = ((μ (Iic b)).to_real - (μ (Iic a)).to_real) • c :=
begin
  simp only [sub_smul, ← set_integral_const],
  refine (integral_Iic_sub_Iic _ _).symm;
    simp only [integrable_on_const, measure_lt_top, or_true]
end

lemma integral_eq_integral_of_support_subset {f : α → E} {a b} (h : function.support f ⊆ Ioc a b) :
  ∫ x in a..b, f x ∂μ = ∫ x, f x ∂μ :=
begin
  by_cases hfm : measurable f,
  { cases le_total a b with hab hab,
    { rw [integral_of_le hab, ← integral_indicator hfm is_measurable_Ioc, indicator_eq_self.2 h] },
    { rw [Ioc_eq_empty hab, subset_empty_iff, function.support_eq_empty_iff] at h,
      simp [h] } },
  { rw [integral_non_measurable hfm, measure_theory.integral_non_measurable hfm] },
end

end order_closed_topology

end

lemma integral_eq_zero_iff_of_le_of_nonneg_ae {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
  (hf : 0 ≤ᵐ[volume.restrict (Ioc a b)] f) (hfi : interval_integrable f volume a b) :
  ∫ x in a..b, f x = 0 ↔ f =ᵐ[volume.restrict (Ioc a b)] 0 :=
by rw [integral_of_le hab, integral_eq_zero_iff_of_nonneg_ae hf hfi.1]

lemma integral_eq_zero_iff_of_nonneg_ae {f : ℝ → ℝ} {a b : ℝ}
  (hf : 0 ≤ᵐ[volume.restrict (Ioc a b ∪ Ioc b a)] f) (hfi : interval_integrable f volume a b) :
  ∫ x in a..b, f x = 0 ↔ f =ᵐ[volume.restrict (Ioc a b ∪ Ioc b a)] 0 :=
begin
  cases le_total a b with hab hab;
    simp only [Ioc_eq_empty hab, empty_union, union_empty] at *,
  { exact integral_eq_zero_iff_of_le_of_nonneg_ae hab hf hfi },
  { rw [integral_symm, neg_eq_zero],
    exact integral_eq_zero_iff_of_le_of_nonneg_ae hab hf hfi.symm }
end

lemma integral_pos_iff_support_of_nonneg_ae' {f : ℝ → ℝ} {a b : ℝ}
  (hf : 0 ≤ᵐ[volume.restrict (Ioc a b ∪ Ioc b a)] f) (hfi : interval_integrable f volume a b) :
  0 < ∫ x in a..b, f x ↔ a < b ∧ 0 < volume (function.support f ∩ Ioc a b) :=
begin
  cases le_total a b with hab hab,
  { simp only [integral_of_le hab, Ioc_eq_empty hab, union_empty] at hf ⊢,
    symmetry,
    rw [set_integral_pos_iff_support_of_nonneg_ae hf hfi.1, and_iff_right_iff_imp],
    contrapose!,
    intro h,
    simp [Ioc_eq_empty h] },
  { rw [Ioc_eq_empty hab, empty_union] at hf,
    simp [integral_of_ge hab, Ioc_eq_empty hab, integral_nonneg_of_ae hf] }
end

lemma integral_pos_iff_support_of_nonneg_ae {f : ℝ → ℝ} {a b : ℝ}
  (hf : 0 ≤ᵐ[volume] f) (hfi : interval_integrable f volume a b) :
  0 < ∫ x in a..b, f x ↔ a < b ∧ 0 < volume (function.support f ∩ Ioc a b) :=
integral_pos_iff_support_of_nonneg_ae' (ae_mono measure.restrict_le_self hf) hfi

/-!
### Fundamental theorem of calculus, part 1, for any measure

In this section we prove a few lemmas that can be seen as versions of FTC-1 for interval integral
w.r.t. any measure. Many theorems are formulated for one or two pairs of filters related by
`FTC_filter a l l'`. This typeclass has exactly four “real” instances: `(a, pure a, ⊥)`,
`(a, 𝓝[Ici a] a, 𝓝[Ioi a] a)`, `(a, 𝓝[Iic a] a, 𝓝[Iic a] a)`, `(a, 𝓝 a, 𝓝 a)`, and two instances
that are equal to the first and last “real” instances: `(a, 𝓝[{a}] a, ⊥)` and
`(a, 𝓝[univ] a, 𝓝[univ] a)`.  We use this approach to avoid repeating arguments in many very similar
cases.  Lean can automatically find both `a` and `l'` based on `l`.

The most general theorem `measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae` can be seen
as a generalization of lemma `integral_has_strict_fderiv_at` below which states strict
differentiability of `∫ x in u..v, f x` in `(u, v)` at `(a, b)` for a measurable function `f` that
is integrable on `a..b` and is continuous at `a` and `b`. The lemma is generalized in three
directions: first, `measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae` deals with any
locally finite measure `μ`; second, it works for one-sided limits/derivatives; third, it assumes
only that `f` has finite limits almost surely at `a` and `b`.

Namely, let `f` be a measurable function integrable on `a..b`. Let `(la, la')` be a pair of
`FTC_filter`s around `a`; let `(lb, lb')` be a pair of `FTC_filter`s around `b`. Suppose that `f`
has finite limits `ca` and `cb` at `la' ⊓ μ.ae` and `lb' ⊓ μ.ae`, respectively.  Then
`∫ x in va..vb, f x ∂μ - ∫ x in ua..ub, f x ∂μ = ∫ x in ub..vb, cb ∂μ - ∫ x in ua..va, ca ∂μ +
  o(∥∫ x in ua..va, (1:ℝ) ∂μ∥ + ∥∫ x in ub..vb, (1:ℝ) ∂μ∥)`
as `ua` and `va` tend to `la` while `ub` and `vb` tend to `lb`.

This theorem is formulated with integral of constants instead of measures in the right hand sides
for two reasons: first, this way we avoid `min`/`max` in the statements; second, often it is
possible to write better `simp` lemmas for these integrals, see `integral_const` and
`integral_const_of_cdf`.

In the next subsection we apply this theorem to prove various theorems about differentiability
of the integral w.r.t. Lebesgue measure. -/

/-- An auxiliary typeclass for the Fundamental theorem of calculus, part 1. It is used to formulate
theorems that work simultaneously for left and right one-sided derivatives of `∫ x in u..v, f x`.
There are four instances: `(a, pure a, ⊥)`, `(a, 𝓝[Ici a], 𝓝[Ioi a])`,
`(a, 𝓝[Iic a], 𝓝[Iic a])`, and `(a, 𝓝 a, 𝓝 a)`. -/
class FTC_filter {β : Type*} [linear_order β] [measurable_space β] [topological_space β]
  (a : out_param β) (outer : filter β) (inner : out_param $ filter β)
  extends tendsto_Ixx_class Ioc outer inner : Prop :=
(pure_le : pure a ≤ outer)
(le_nhds : inner ≤ 𝓝 a)
[meas_gen : is_measurably_generated inner]

/- The `dangerous_instance` linter doesn't take `out_param`s into account, so it thinks that
`FTC_filter.to_tendsto_Ixx_class` is dangerous. Disable this linter using `nolint`.
-/
attribute [nolint dangerous_instance] FTC_filter.to_tendsto_Ixx_class

namespace FTC_filter

variables [linear_order β] [measurable_space β] [topological_space β]

instance pure (a : β) : FTC_filter a (pure a) ⊥ :=
{ pure_le := le_refl _,
  le_nhds := bot_le }

instance nhds_within_singleton (a : β) : FTC_filter a (𝓝[{a}] a) ⊥ :=
by { rw [nhds_within, principal_singleton, inf_eq_right.2 (pure_le_nhds a)], apply_instance }

lemma finite_at_inner {a : β} (l : filter β) {l'} [h : FTC_filter a l l']
  {μ : measure β} [locally_finite_measure μ] :
  μ.finite_at_filter l' :=
(μ.finite_at_nhds a).filter_mono h.le_nhds

variables [opens_measurable_space β] [order_topology β]

instance nhds (a : β) : FTC_filter a (𝓝 a) (𝓝 a) :=
{ pure_le := pure_le_nhds a,
  le_nhds := le_refl _ }

instance nhds_univ (a : β) : FTC_filter a (𝓝[univ] a) (𝓝 a) :=
by { rw nhds_within_univ, apply_instance }

instance nhds_left (a : β) : FTC_filter a (𝓝[Iic a] a) (𝓝[Iic a] a) :=
{ pure_le := pure_le_nhds_within right_mem_Iic,
  le_nhds := inf_le_left }

instance nhds_right (a : β) : FTC_filter a (𝓝[Ici a] a) (𝓝[Ioi a] a) :=
{ pure_le := pure_le_nhds_within left_mem_Ici,
  le_nhds := inf_le_left }

end FTC_filter

open asymptotics

section

variables {f : α → E} {a b : α} {c ca cb : E} {l l' la la' lb lb' : filter α} {lt : filter β}
  {μ : measure α} {u v ua va ub vb : β → α}

/-- Fundamental theorem of calculus-1, local version for any measure.
Let filters `l` and `l'` be related by `tendsto_Ixx_class Ioc`.
If `f` has a finite limit `c` at `l' ⊓ μ.ae`, where `μ` is a measure
finite at `l'`, then `∫ x in u..v, f x ∂μ = ∫ x in u..v, c ∂μ + o(∫ x in u..v, 1 ∂μ)` as both
`u` and `v` tend to `l`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae` for a version assuming
`[FTC_filter a l l']` and `[locally_finite_measure μ]`. If `l` is one of `𝓝[Ici a] a`,
`𝓝[Iic a] a`, `𝓝 a`, then it's easier to apply the non-primed version.
The primed version also works, e.g., for `l = l' = at_top`.

We use integrals of constants instead of measures because this way it is easier to formulate
a statement that works in both cases `u ≤ v` and `v ≤ u`. -/
lemma measure_integral_sub_linear_is_o_of_tendsto_ae'
  [is_measurably_generated l'] [tendsto_Ixx_class Ioc l l']
  (hfm : measurable f) (hf : tendsto f (l' ⊓ μ.ae) (𝓝 c)) (hl : μ.finite_at_filter l')
  (hu : tendsto u lt l) (hv : tendsto v lt l) :
  is_o (λ t, ∫ x in u t..v t, f x ∂μ - ∫ x in u t..v t, c ∂μ)
    (λ t, ∫ x in u t..v t, (1:ℝ) ∂μ) lt :=
begin
  have A := (hf.integral_sub_linear_is_o_ae hfm hl).comp_tendsto (hu.Ioc hv),
  have B := (hf.integral_sub_linear_is_o_ae hfm hl).comp_tendsto (hv.Ioc hu),
  simp only [integral_const'],
  convert (A.trans_le _).sub (B.trans_le _),
  { ext t,
    simp_rw [(∘), interval_integral, sub_smul],
    abel },
  all_goals { intro t, cases le_total (u t) (v t) with huv huv; simp [huv] }
end

/-- Fundamental theorem of calculus-1, local version for any measure.
Let filters `l` and `l'` be related by `tendsto_Ixx_class Ioc`.
If `f` has a finite limit `c` at `l ⊓ μ.ae`, where `μ` is a measure
finite at `l`, then `∫ x in u..v, f x ∂μ = μ (Ioc u v) • c + o(μ(Ioc u v))` as both
`u` and `v` tend to `l` so that `u ≤ v`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae_of_le` for a version assuming
`[FTC_filter a l l']` and `[locally_finite_measure μ]`. If `l` is one of `𝓝[Ici a] a`,
`𝓝[Iic a] a`, `𝓝 a`, then it's easier to apply the non-primed version.
The primed version also works, e.g., for `l = l' = at_top`. -/
lemma measure_integral_sub_linear_is_o_of_tendsto_ae_of_le'
  [is_measurably_generated l'] [tendsto_Ixx_class Ioc l l']
  (hfm : measurable f) (hf : tendsto f (l' ⊓ μ.ae) (𝓝 c)) (hl : μ.finite_at_filter l')
  (hu : tendsto u lt l) (hv : tendsto v lt l) (huv : u ≤ᶠ[lt] v) :
  is_o (λ t, ∫ x in u t..v t, f x ∂μ - (μ (Ioc (u t) (v t))).to_real • c)
    (λ t, (μ $ Ioc (u t) (v t)).to_real) lt :=
(measure_integral_sub_linear_is_o_of_tendsto_ae' hfm hf hl hu hv).congr'
  (huv.mono $ λ x hx, by simp [integral_const', hx])
  (huv.mono $ λ x hx, by simp [integral_const', hx])

/-- Fundamental theorem of calculus-1, local version for any measure.
Let filters `l` and `l'` be related by `tendsto_Ixx_class Ioc`.
If `f` has a finite limit `c` at `l ⊓ μ.ae`, where `μ` is a measure
finite at `l`, then `∫ x in u..v, f x ∂μ = -μ (Ioc v u) • c + o(μ(Ioc v u))` as both
`u` and `v` tend to `l` so that `v ≤ u`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge` for a version assuming
`[FTC_filter a l l']` and `[locally_finite_measure μ]`. If `l` is one of `𝓝[Ici a] a`,
`𝓝[Iic a] a`, `𝓝 a`, then it's easier to apply the non-primed version.
The primed version also works, e.g., for `l = l' = at_top`. -/
lemma measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge'
  [is_measurably_generated l'] [tendsto_Ixx_class Ioc l l']
  (hfm : measurable f) (hf : tendsto f (l' ⊓ μ.ae) (𝓝 c)) (hl : μ.finite_at_filter l')
  (hu : tendsto u lt l) (hv : tendsto v lt l) (huv : v ≤ᶠ[lt] u) :
  is_o (λ t, ∫ x in u t..v t, f x ∂μ + (μ (Ioc (v t) (u t))).to_real • c)
    (λ t, (μ $ Ioc (v t) (u t)).to_real) lt :=
(measure_integral_sub_linear_is_o_of_tendsto_ae_of_le' hfm hf hl hv hu huv).neg_left.congr_left $
  λ t, by simp [integral_symm (u t), add_comm]

variables [topological_space α]

section

variables [locally_finite_measure μ] [FTC_filter a l l']

include a

local attribute [instance] FTC_filter.meas_gen

/-- Fundamental theorem of calculus-1, local version for any measure.
Let filters `l` and `l'` be related by `[FTC_filter a l l']`; let `μ` be a locally finite measure.
If `f` has a finite limit `c` at `l' ⊓ μ.ae`, then
`∫ x in u..v, f x ∂μ = ∫ x in u..v, c ∂μ + o(∫ x in u..v, 1 ∂μ)` as both `u` and `v` tend to `l`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae'` for a version that also works, e.g., for
`l = l' = at_top`.

We use integrals of constants instead of measures because this way it is easier to formulate
a statement that works in both cases `u ≤ v` and `v ≤ u`. -/
lemma measure_integral_sub_linear_is_o_of_tendsto_ae (hfm : measurable f)
  (hf : tendsto f (l' ⊓ μ.ae) (𝓝 c)) (hu : tendsto u lt l) (hv : tendsto v lt l) :
  is_o (λ t, ∫ x in u t..v t, f x ∂μ - ∫ x in u t..v t, c ∂μ)
    (λ t, ∫ x in u t..v t, (1:ℝ) ∂μ) lt :=
measure_integral_sub_linear_is_o_of_tendsto_ae' hfm hf (FTC_filter.finite_at_inner l) hu hv

/-- Fundamental theorem of calculus-1, local version for any measure.
Let filters `l` and `l'` be related by `[FTC_filter a l l']`; let `μ` be a locally finite measure.
If `f` has a finite limit `c` at `l' ⊓ μ.ae`, then
`∫ x in u..v, f x ∂μ = μ (Ioc u v) • c + o(μ(Ioc u v))` as both `u` and `v` tend to `l`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae_of_le'` for a version that also works,
e.g., for `l = l' = at_top`. -/
lemma measure_integral_sub_linear_is_o_of_tendsto_ae_of_le
  (hfm : measurable f) (hf : tendsto f (l' ⊓ μ.ae) (𝓝 c))
  (hu : tendsto u lt l) (hv : tendsto v lt l) (huv : u ≤ᶠ[lt] v) :
  is_o (λ t, ∫ x in u t..v t, f x ∂μ - (μ (Ioc (u t) (v t))).to_real • c)
    (λ t, (μ $ Ioc (u t) (v t)).to_real) lt :=
measure_integral_sub_linear_is_o_of_tendsto_ae_of_le' hfm hf (FTC_filter.finite_at_inner l)
  hu hv huv

/-- Fundamental theorem of calculus-1, local version for any measure.
Let filters `l` and `l'` be related by `[FTC_filter a l l']`; let `μ` be a locally finite measure.
If `f` has a finite limit `c` at `l' ⊓ μ.ae`, then
`∫ x in u..v, f x ∂μ = -μ (Ioc v u) • c + o(μ(Ioc v u))` as both `u` and `v` tend to `l`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge'` for a version that also works,
e.g., for `l = l' = at_top`. -/
lemma measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge
  (hfm : measurable f) (hf : tendsto f (l' ⊓ μ.ae) (𝓝 c))
  (hu : tendsto u lt l) (hv : tendsto v lt l) (huv : v ≤ᶠ[lt] u) :
  is_o (λ t, ∫ x in u t..v t, f x ∂μ + (μ (Ioc (v t) (u t))).to_real • c)
    (λ t, (μ $ Ioc (v t) (u t)).to_real) lt :=
measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge' hfm hf (FTC_filter.finite_at_inner l)
  hu hv huv

end

variables [order_topology α] [borel_space α]

local attribute [instance] FTC_filter.meas_gen

variables [FTC_filter a la la'] [FTC_filter b lb lb'] [locally_finite_measure μ]

/-- Fundamental theorem of calculus-1, strict derivative in both limits for a locally finite
measure.

Let `f` be a measurable function integrable on `a..b`. Let `(la, la')` be a pair of `FTC_filter`s
around `a`; let `(lb, lb')` be a pair of `FTC_filter`s around `b`. Suppose that `f` has finite
limits `ca` and `cb` at `la' ⊓ μ.ae` and `lb' ⊓ μ.ae`, respectively.
Then `∫ x in va..vb, f x ∂μ - ∫ x in ua..ub, f x ∂μ =
  ∫ x in ub..vb, cb ∂μ - ∫ x in ua..va, ca ∂μ +
    o(∥∫ x in ua..va, (1:ℝ) ∂μ∥ + ∥∫ x in ub..vb, (1:ℝ) ∂μ∥)`
as `ua` and `va` tend to `la` while `ub` and `vb` tend to `lb`.
-/
lemma measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae
  (hab : interval_integrable f μ a b)
  (ha_lim : tendsto f (la' ⊓ μ.ae) (𝓝 ca)) (hb_lim : tendsto f (lb' ⊓ μ.ae) (𝓝 cb))
  (hua : tendsto ua lt la) (hva : tendsto va lt la)
  (hub : tendsto ub lt lb) (hvb : tendsto vb lt lb) :
  is_o (λ t, (∫ x in va t..vb t, f x ∂μ) - (∫ x in ua t..ub t, f x ∂μ) -
    (∫ x in ub t..vb t, cb ∂μ - ∫ x in ua t..va t, ca ∂μ))
    (λ t, ∥∫ x in ua t..va t, (1:ℝ) ∂μ∥ + ∥∫ x in ub t..vb t, (1:ℝ) ∂μ∥) lt :=
begin
  refine
    ((measure_integral_sub_linear_is_o_of_tendsto_ae hab.measurable ha_lim hua hva).neg_left.add_add
    (measure_integral_sub_linear_is_o_of_tendsto_ae hab.measurable hb_lim hub hvb)).congr'
      _ (eventually_eq.refl _ _),
  have A : ∀ᶠ t in lt, interval_integrable f μ (ua t) (va t) :=
    ha_lim.eventually_interval_integrable_ae hab.measurable (FTC_filter.finite_at_inner la) hua hva,
  have A' : ∀ᶠ t in lt, interval_integrable f μ a (ua t) :=
    ha_lim.eventually_interval_integrable_ae hab.measurable (FTC_filter.finite_at_inner la)
      (tendsto_const_pure.mono_right FTC_filter.pure_le) hua,
  have B : ∀ᶠ t in lt, interval_integrable f μ (ub t) (vb t) :=
    hb_lim.eventually_interval_integrable_ae hab.measurable (FTC_filter.finite_at_inner lb) hub hvb,
  have B' : ∀ᶠ t in lt, interval_integrable f μ b (ub t) :=
    hb_lim.eventually_interval_integrable_ae hab.measurable (FTC_filter.finite_at_inner lb)
      (tendsto_const_pure.mono_right FTC_filter.pure_le) hub,
  filter_upwards [A, A', B, B'],
  intros t ua_va a_ua ub_vb b_ub,
  rw [← integral_interval_sub_interval_comm'],
  { dsimp only [], abel },
  exacts [ub_vb, ua_va, b_ub.symm.trans $ hab.symm.trans a_ua]
end

/-- Fundamental theorem of calculus-1, strict derivative in right endpoint for a locally finite
measure.

Let `f` be a measurable function integrable on `a..b`. Let `(lb, lb')` be a pair of `FTC_filter`s
around `b`. Suppose that `f` has a finite limit `c` at `lb' ⊓ μ.ae`.

Then `∫ x in a..v, f x ∂μ - ∫ x in a..u, f x ∂μ = ∫ x in u..v, c ∂μ + o(∫ x in u..v, (1:ℝ) ∂μ)`
as `u` and `v` tend to `lb`.
-/
lemma measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae_right
  (hab : interval_integrable f μ a b) (hf : tendsto f (lb' ⊓ μ.ae) (𝓝 c))
  (hu : tendsto u lt lb) (hv : tendsto v lt lb) :
  is_o (λ t, ∫ x in a..v t, f x ∂μ - ∫ x in a..u t, f x ∂μ - ∫ x in u t..v t, c ∂μ)
    (λ t, ∫ x in u t..v t, (1:ℝ) ∂μ) lt :=
by simpa using measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae
  hab ((tendsto_bot : tendsto _ ⊥ (𝓝 0)).mono_left inf_le_left)
  hf (tendsto_const_pure : tendsto _ _ (pure a)) tendsto_const_pure hu hv

/-- Fundamental theorem of calculus-1, strict derivative in left endpoint for a locally finite
measure.

Let `f` be a measurable function integrable on `a..b`. Let `(la, la')` be a pair of `FTC_filter`s
around `a`. Suppose that `f` has a finite limit `c` at `la' ⊓ μ.ae`.

Then `∫ x in v..b, f x ∂μ - ∫ x in u..b, f x ∂μ = -∫ x in u..v, c ∂μ + o(∫ x in u..v, (1:ℝ) ∂μ)`
as `u` and `v` tend to `la`.
-/
lemma measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae_left
  (hab : interval_integrable f μ a b)
  (hf : tendsto f (la' ⊓ μ.ae) (𝓝 c)) (hu : tendsto u lt la) (hv : tendsto v lt la) :
  is_o (λ t, ∫ x in v t..b, f x ∂μ - ∫ x in u t..b, f x ∂μ + ∫ x in u t..v t, c ∂μ)
    (λ t, ∫ x in u t..v t, (1:ℝ) ∂μ) lt :=
by simpa using measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae
  hab hf ((tendsto_bot : tendsto _ ⊥ (𝓝 0)).mono_left inf_le_left)
  hu hv (tendsto_const_pure : tendsto _ _ (pure b)) tendsto_const_pure

end

/-!
### Fundamental theorem of calculus-1 for Lebesgue measure

In this section we restate theorems from the previous section for Lebesgue measure.
In particular, we prove that `∫ x in u..v, f x` is strictly differentiable in `(u, v)`
at `(a, b)` provided that `f` is integrable on `a..b` and is continuous at `a` and `b`.
-/

variables {f : ℝ → E} {c ca cb : E} {l l' la la' lb lb' : filter ℝ} {lt : filter β}
  {a b z : ℝ} {u v ua ub va vb : β → ℝ} [FTC_filter a la la'] [FTC_filter b lb lb']

/-!
#### Auxiliary `is_o` statements

In this section we prove several lemmas that can be interpreted as strict differentiability of
`(u, v) ↦ ∫ x in u..v, f x ∂μ` in `u` and/or `v` at a filter. The statements use `is_o` because
we have no definition of `has_strict_(f)deriv_at_filter` in the library.
-/

/-- Fundamental theorem of calculus-1, local version. If `f` has a finite limit `c` almost surely at
`l'`, where `(l, l')` is an `FTC_filter` pair around `a`, then
`∫ x in u..v, f x ∂μ = (v - u) • c + o (v - u)` as both `u` and `v` tend to `l`. -/
lemma integral_sub_linear_is_o_of_tendsto_ae [FTC_filter a l l']
  (hfm : measurable f) (hf : tendsto f (l' ⊓ volume.ae) (𝓝 c))
  {u v : β → ℝ} (hu : tendsto u lt l) (hv : tendsto v lt l) :
  is_o (λ t, (∫ x in u t..v t, f x) - (v t - u t) • c) (v - u) lt :=
by simpa [integral_const] using measure_integral_sub_linear_is_o_of_tendsto_ae hfm hf hu hv

/-- Fundamental theorem of calculus-1, strict differentiability at filter in both endpoints.
If `f` is a measurable function integrable on `a..b`, `(la, la')` is an `FTC_filter` pair around
`a`, and `(lb, lb')` is an `FTC_filter` pair around `b`, and `f` has finite limits `ca` and `cb`
almost surely at `la'` and `lb'`, respectively, then
`(∫ x in va..vb, f x) - ∫ x in ua..ub, f x = (vb - ub) • cb - (va - ua) • ca +
  o(∥va - ua∥ + ∥vb - ub∥)` as `ua` and `va` tend to `la` while `ub` and `vb` tend to `lb`.

This lemma could've been formulated using `has_strict_fderiv_at_filter` if we had this
definition. -/
lemma integral_sub_integral_sub_linear_is_o_of_tendsto_ae
  (hab : interval_integrable f volume a b)
  (ha_lim : tendsto f (la' ⊓ volume.ae) (𝓝 ca)) (hb_lim : tendsto f (lb' ⊓ volume.ae) (𝓝 cb))
  (hua : tendsto ua lt la) (hva : tendsto va lt la)
  (hub : tendsto ub lt lb) (hvb : tendsto vb lt lb) :
  is_o (λ t, (∫ x in va t..vb t, f x) - (∫ x in ua t..ub t, f x) -
    ((vb t - ub t) • cb - (va t - ua t) • ca)) (λ t, ∥va t - ua t∥ + ∥vb t - ub t∥) lt :=
by simpa [integral_const] using
measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae hab ha_lim hb_lim hua hva hub hvb

/-- Fundamental theorem of calculus-1, strict differentiability at filter in both endpoints.
If `f` is a measurable function integrable on `a..b`, `(lb, lb')` is an `FTC_filter` pair
around `b`, and `f` has a finite limit `c` almost surely at `lb'`, then
`(∫ x in a..v, f x) - ∫ x in a..u, f x = (v - u) • c + o(∥v - u∥)` as `u` and `v` tend to `lb`.

This lemma could've been formulated using `has_strict_deriv_at_filter` if we had this definition. -/
lemma integral_sub_integral_sub_linear_is_o_of_tendsto_ae_right
  (hab : interval_integrable f volume a b) (hf : tendsto f (lb' ⊓ volume.ae) (𝓝 c))
  (hu : tendsto u lt lb) (hv : tendsto v lt lb) :
  is_o (λ t, (∫ x in a..v t, f x) - (∫ x in a..u t, f x) - (v t - u t) • c) (v - u) lt :=
by simpa only [integral_const, smul_eq_mul, mul_one] using
  measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae_right hab hf hu hv

/-- Fundamental theorem of calculus-1, strict differentiability at filter in both endpoints.
If `f` is a measurable function integrable on `a..b`, `(la, la')` is an `FTC_filter` pair
around `a`, and `f` has a finite limit `c` almost surely at `la'`, then
`(∫ x in v..b, f x) - ∫ x in u..b, f x = -(v - u) • c + o(∥v - u∥)` as `u` and `v` tend to `la`.

This lemma could've been formulated using `has_strict_deriv_at_filter` if we had this definition. -/
lemma integral_sub_integral_sub_linear_is_o_of_tendsto_ae_left
  (hab : interval_integrable f volume a b) (hf : tendsto f (la' ⊓ volume.ae) (𝓝 c))
  (hu : tendsto u lt la) (hv : tendsto v lt la) :
  is_o (λ t, (∫ x in v t..b, f x) - (∫ x in u t..b, f x) + (v t - u t) • c) (v - u) lt :=
by simpa only [integral_const, smul_eq_mul, mul_one] using
  measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae_left hab hf hu hv

open continuous_linear_map (fst snd smul_right sub_apply smul_right_apply coe_fst' coe_snd' map_sub)

/-!
#### Strict differentiability

In this section we prove that for a measurable function `f` integrable on `a..b`,

* `integral_has_strict_fderiv_at_of_tendsto_ae`: the function `(u, v) ↦ ∫ x in u..v, f x` has
  derivative `(u, v) ↦ v • cb - u • ca` at `(a, b)` in the sense of strict differentiability
  provided that `f` tends to `ca` and `cb` almost surely as `x` tendsto to `a` and `b`,
  respectively;

* `integral_has_strict_fderiv_at`: the function `(u, v) ↦ ∫ x in u..v, f x` has
  derivative `(u, v) ↦ v • f b - u • f a` at `(a, b)` in the sense of strict differentiability
  provided that `f` is continuous at `a` and `b`;

* `integral_has_strict_deriv_at_of_tendsto_ae_right`: the function `u ↦ ∫ x in a..u, f x` has
  derivative `c` at `b` in the sense of strict differentiability provided that `f` tends to `c`
  almost surely as `x` tends to `b`;

* `integral_has_strict_deriv_at_right`: the function `u ↦ ∫ x in a..u, f x` has derivative `f b` at
  `b` in the sense of strict differentiability provided that `f` is continuous at `b`;

* `integral_has_strict_deriv_at_of_tendsto_ae_left`: the function `u ↦ ∫ x in u..b, f x` has
  derivative `-c` at `a` in the sense of strict differentiability provided that `f` tends to `c`
  almost surely as `x` tends to `a`;

* `integral_has_strict_deriv_at_left`: the function `u ↦ ∫ x in u..b, f x` has derivative `-f a` at
  `a` in the sense of strict differentiability provided that `f` is continuous at `a`.
-/

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f x` has finite
limits `ca` and `cb` almost surely as `x` tends to `a` and `b`, respectively, then
`(u, v) ↦ ∫ x in u..v, f x` has derivative `(u, v) ↦ v • cb - u • ca` at `(a, b)`
in the sense of strict differentiability. -/
lemma integral_has_strict_fderiv_at_of_tendsto_ae (hf : interval_integrable f volume a b)
  (ha : tendsto f (𝓝 a ⊓ volume.ae) (𝓝 ca)) (hb : tendsto f (𝓝 b ⊓ volume.ae) (𝓝 cb)) :
  has_strict_fderiv_at (λ p : ℝ × ℝ, ∫ x in p.1..p.2, f x)
    ((snd ℝ ℝ ℝ).smul_right cb - (fst ℝ ℝ ℝ).smul_right ca) (a, b) :=
begin
  have := integral_sub_integral_sub_linear_is_o_of_tendsto_ae hf ha hb
    ((continuous_fst.comp continuous_snd).tendsto ((a, b), (a, b)))
    ((continuous_fst.comp continuous_fst).tendsto ((a, b), (a, b)))
    ((continuous_snd.comp continuous_snd).tendsto ((a, b), (a, b)))
    ((continuous_snd.comp continuous_fst).tendsto ((a, b), (a, b))),
  refine (this.congr_left _).trans_is_O _,
  { intro x, simp [sub_smul] },
  { exact is_O_fst_prod.norm_left.add is_O_snd_prod.norm_left }
end

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `a` and `b`, then `(u, v) ↦ ∫ x in u..v, f x` has derivative `(u, v) ↦ v • cb - u • ca`
at `(a, b)` in the sense of strict differentiability. -/
lemma integral_has_strict_fderiv_at (hf : interval_integrable f volume a b)
  (ha : continuous_at f a) (hb : continuous_at f b) :
  has_strict_fderiv_at (λ p : ℝ × ℝ, ∫ x in p.1..p.2, f x)
    ((snd ℝ ℝ ℝ).smul_right (f b) - (fst ℝ ℝ ℝ).smul_right (f a)) (a, b) :=
integral_has_strict_fderiv_at_of_tendsto_ae hf
  (ha.mono_left inf_le_left) (hb.mono_left inf_le_left)

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely at `b`, then `u ↦ ∫ x in a..u, f x` has derivative `c` at `b` in the sense
of strict differentiability. -/
lemma integral_has_strict_deriv_at_of_tendsto_ae_right (hf : interval_integrable f volume a b)
  (hb : tendsto f (𝓝 b ⊓ volume.ae) (𝓝 c)) : has_strict_deriv_at (λ u, ∫ x in a..u, f x) c b :=
integral_sub_integral_sub_linear_is_o_of_tendsto_ae_right hf hb continuous_at_snd
  continuous_at_fst

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `b`, then `u ↦ ∫ x in a..u, f x` has derivative `f b` at `b` in the sense of strict
differentiability. -/
lemma integral_has_strict_deriv_at_right (hf : interval_integrable f volume a b)
  (hb : continuous_at f b) : has_strict_deriv_at (λ u, ∫ x in a..u, f x) (f b) b :=
integral_has_strict_deriv_at_of_tendsto_ae_right hf (hb.mono_left inf_le_left)

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely at `a`, then `u ↦ ∫ x in u..b, f x` has derivative `-c` at `a` in the sense
of strict differentiability. -/
lemma integral_has_strict_deriv_at_of_tendsto_ae_left (hf : interval_integrable f volume a b)
  (ha : tendsto f (𝓝 a ⊓ volume.ae) (𝓝 c)) : has_strict_deriv_at (λ u, ∫ x in u..b, f x) (-c) a :=
by simpa only [← integral_symm]
  using (integral_has_strict_deriv_at_of_tendsto_ae_right hf.symm ha).neg

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `a`, then `u ↦ ∫ x in u..b, f x` has derivative `-f a` at `a` in the sense of strict
differentiability. -/
lemma integral_has_strict_deriv_at_left (hf : interval_integrable f volume a b)
  (ha : continuous_at f a) : has_strict_deriv_at (λ u, ∫ x in u..b, f x) (-f a) a :=
by simpa only [← integral_symm] using (integral_has_strict_deriv_at_right hf.symm ha).neg

/-!
#### Fréchet differentiability

In this subsection we restate results from the previous subsection in terms of `has_fderiv_at`,
`has_deriv_at`, `fderiv`, and `deriv`.
-/

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f x` has finite
limits `ca` and `cb` almost surely as `x` tends to `a` and `b`, respectively, then
`(u, v) ↦ ∫ x in u..v, f x` has derivative `(u, v) ↦ v • cb - u • ca` at `(a, b)`. -/
lemma integral_has_fderiv_at_of_tendsto_ae (hf : interval_integrable f volume a b)
  (ha : tendsto f (𝓝 a ⊓ volume.ae) (𝓝 ca)) (hb : tendsto f (𝓝 b ⊓ volume.ae) (𝓝 cb)) :
  has_fderiv_at (λ p : ℝ × ℝ, ∫ x in p.1..p.2, f x)
    ((snd ℝ ℝ ℝ).smul_right cb - (fst ℝ ℝ ℝ).smul_right ca) (a, b) :=
(integral_has_strict_fderiv_at_of_tendsto_ae hf ha hb).has_fderiv_at

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `a` and `b`, then `(u, v) ↦ ∫ x in u..v, f x` has derivative `(u, v) ↦ v • cb - u • ca`
at `(a, b)`. -/
lemma integral_has_fderiv_at (hf : interval_integrable f volume a b)
  (ha : continuous_at f a) (hb : continuous_at f b) :
  has_fderiv_at (λ p : ℝ × ℝ, ∫ x in p.1..p.2, f x)
    ((snd ℝ ℝ ℝ).smul_right (f b) - (fst ℝ ℝ ℝ).smul_right (f a)) (a, b) :=
(integral_has_strict_fderiv_at hf ha hb).has_fderiv_at

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f x` has finite
limits `ca` and `cb` almost surely as `x` tends to `a` and `b`, respectively, then `fderiv`
derivative of `(u, v) ↦ ∫ x in u..v, f x` at `(a, b)` equals `(u, v) ↦ v • cb - u • ca`. -/
lemma fderiv_integral_of_tendsto_ae (hf : interval_integrable f volume a b)
  (ha : tendsto f (𝓝 a ⊓ volume.ae) (𝓝 ca)) (hb : tendsto f (𝓝 b ⊓ volume.ae) (𝓝 cb)) :
  fderiv ℝ (λ p : ℝ × ℝ, ∫ x in p.1..p.2, f x) (a, b) =
    (snd ℝ ℝ ℝ).smul_right cb - (fst ℝ ℝ ℝ).smul_right ca :=
(integral_has_fderiv_at_of_tendsto_ae hf ha hb).fderiv

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `a` and `b`, then `fderiv` derivative of `(u, v) ↦ ∫ x in u..v, f x` at `(a, b)` equals `(u, v) ↦
v • cb - u • ca`. -/
lemma fderiv_integral (hf : interval_integrable f volume a b)
  (ha : continuous_at f a) (hb : continuous_at f b) :
  fderiv ℝ (λ p : ℝ × ℝ, ∫ x in p.1..p.2, f x) (a, b) =
    (snd ℝ ℝ ℝ).smul_right (f b) - (fst ℝ ℝ ℝ).smul_right (f a) :=
(integral_has_fderiv_at hf ha hb).fderiv

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely at `b`, then `u ↦ ∫ x in a..u, f x` has derivative `c` at `b`. -/
lemma integral_has_deriv_at_of_tendsto_ae_right (hf : interval_integrable f volume a b)
  (hb : tendsto f (𝓝 b ⊓ volume.ae) (𝓝 c)) : has_deriv_at (λ u, ∫ x in a..u, f x) c b :=
(integral_has_strict_deriv_at_of_tendsto_ae_right hf hb).has_deriv_at

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `b`, then `u ↦ ∫ x in a..u, f x` has derivative `f b` at `b`. -/
lemma integral_has_deriv_at_right (hf : interval_integrable f volume a b)
  (hb : continuous_at f b) : has_deriv_at (λ u, ∫ x in a..u, f x) (f b) b :=
(integral_has_strict_deriv_at_right hf hb).has_deriv_at

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` has a finite
limit `c` almost surely at `b`, then the derivative of `u ↦ ∫ x in a..u, f x` at `b` equals `c`. -/
lemma deriv_integral_of_tendsto_ae_right (hf : interval_integrable f volume a b)
  (hb : tendsto f (𝓝 b ⊓ volume.ae) (𝓝 c)) : deriv (λ u, ∫ x in a..u, f x) b = c :=
(integral_has_deriv_at_of_tendsto_ae_right hf hb).deriv

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `b`, then the derivative of `u ↦ ∫ x in a..u, f x` at `b` equals `f b`. -/
lemma deriv_integral_right (hf : interval_integrable f volume a b) (hb : continuous_at f b) :
  deriv (λ u, ∫ x in a..u, f x) b = f b :=
(integral_has_deriv_at_right hf hb).deriv

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely at `a`, then `u ↦ ∫ x in u..b, f x` has derivative `-c` at `a`. -/
lemma integral_has_deriv_at_of_tendsto_ae_left (hf : interval_integrable f volume a b)
  (ha : tendsto f (𝓝 a ⊓ volume.ae) (𝓝 c)) : has_deriv_at (λ u, ∫ x in u..b, f x) (-c) a :=
(integral_has_strict_deriv_at_of_tendsto_ae_left hf ha).has_deriv_at

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `a`, then `u ↦ ∫ x in u..b, f x` has derivative `-f a` at `a`. -/
lemma integral_has_deriv_at_left (hf : interval_integrable f volume a b) (ha : continuous_at f a) :
  has_deriv_at (λ u, ∫ x in u..b, f x) (-f a) a :=
(integral_has_strict_deriv_at_left hf ha).has_deriv_at

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` has a finite
limit `c` almost surely at `a`, then the derivative of `u ↦ ∫ x in u..b, f x` at `a` equals `-c`. -/
lemma deriv_integral_of_tendsto_ae_left (hf : interval_integrable f volume a b)
  (hb : tendsto f (𝓝 a ⊓ volume.ae) (𝓝 c)) : deriv (λ u, ∫ x in u..b, f x) a = -c :=
(integral_has_deriv_at_of_tendsto_ae_left hf hb).deriv

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `a`, then the derivative of `u ↦ ∫ x in u..b, f x` at `a` equals `-f a`. -/
lemma deriv_integral_left (hf : interval_integrable f volume a b) (hb : continuous_at f a) :
  deriv (λ u, ∫ x in u..b, f x) a = -f a :=
(integral_has_deriv_at_left hf hb).deriv

/-!
#### One-sided derivatives
-/

/-- Let `f` be a measurable function integrable on `a..b`. The function `(u, v) ↦ ∫ x in u..v, f x`
has derivative `(u, v) ↦ v • cb - u • ca` within `s × t` at `(a, b)`, where
`s ∈ {Iic a, {a}, Ici a, univ}` and `t ∈ {Iic b, {b}, Ici b, univ}` provided that `f` tends to `ca`
and `cb` almost surely at the filters `la` and `lb` from the following table.

| `s`     | `la`         | `t`     | `lb`         |
| ------- | ----         | ---     | ----         |
| `Iic a` | `𝓝[Iic a] a` | `Iic b` | `𝓝[Iic b] b` |
| `Ici a` | `𝓝[Ioi a] a` | `Ici b` | `𝓝[Ioi b] b` |
| `{a}`   | `⊥`          | `{b}`   | `⊥`          |
| `univ`  | `𝓝 a`        | `univ`  | `𝓝 b`        |
-/
lemma integral_has_fderiv_within_at_of_tendsto_ae (hf : interval_integrable f volume a b)
  {s t : set ℝ} [FTC_filter a (𝓝[s] a) la] [FTC_filter b (𝓝[t] b) lb]
  (ha : tendsto f (la ⊓ volume.ae) (𝓝 ca)) (hb : tendsto f (lb ⊓ volume.ae) (𝓝 cb)) :
  has_fderiv_within_at (λ p : ℝ × ℝ, ∫ x in p.1..p.2, f x)
    ((snd ℝ ℝ ℝ).smul_right cb - (fst ℝ ℝ ℝ).smul_right ca) (s.prod t) (a, b) :=
begin
  rw [has_fderiv_within_at, nhds_within_prod_eq],
  have := integral_sub_integral_sub_linear_is_o_of_tendsto_ae hf ha hb
    (tendsto_const_pure.mono_right FTC_filter.pure_le : tendsto _ _ (𝓝[s] a)) tendsto_fst
    (tendsto_const_pure.mono_right FTC_filter.pure_le : tendsto _ _ (𝓝[t] b)) tendsto_snd,
  refine (this.congr_left _).trans_is_O _,
  { intro x, simp [sub_smul] },
  { exact is_O_fst_prod.norm_left.add is_O_snd_prod.norm_left }
end

/-- Let `f` be a measurable function integrable on `a..b`. The function `(u, v) ↦ ∫ x in u..v, f x`
has derivative `(u, v) ↦ v • f b - u • f a` within `s × t` at `(a, b)`, where
`s ∈ {Iic a, {a}, Ici a, univ}` and `t ∈ {Iic b, {b}, Ici b, univ}` provided that `f` tends to
`f a` and `f b` at the filters `la` and `lb` from the following table. In most cases this assumption
is definitionally equal `continuous_at f _` or `continuous_within_at f _ _`.

| `s`     | `la`         | `t`     | `lb`         |
| ------- | ----         | ---     | ----         |
| `Iic a` | `𝓝[Iic a] a` | `Iic b` | `𝓝[Iic b] b` |
| `Ici a` | `𝓝[Ioi a] a` | `Ici b` | `𝓝[Ioi b] b` |
| `{a}`   | `⊥`          | `{b}`   | `⊥`          |
| `univ`  | `𝓝 a`        | `univ`  | `𝓝 b`        |
-/
lemma integral_has_fderiv_within_at (hf : interval_integrable f volume a b)
  {s t : set ℝ} [FTC_filter a (𝓝[s] a) la] [FTC_filter b (𝓝[t] b) lb]
  (ha : tendsto f la (𝓝 $ f a)) (hb : tendsto f lb (𝓝 $ f b)) :
  has_fderiv_within_at (λ p : ℝ × ℝ, ∫ x in p.1..p.2, f x)
    ((snd ℝ ℝ ℝ).smul_right (f b) - (fst ℝ ℝ ℝ).smul_right (f a)) (s.prod t) (a, b) :=
integral_has_fderiv_within_at_of_tendsto_ae hf (ha.mono_left inf_le_left)
  (hb.mono_left inf_le_left)

/-- An auxiliary tactic closing goals `unique_diff_within_at ℝ s a` where
`s ∈ {Iic a, Ici a, univ}`. -/
meta def unique_diff_within_at_Ici_Iic_univ : tactic unit :=
`[apply_rules [unique_diff_on.unique_diff_within_at, unique_diff_on_Ici, unique_diff_on_Iic,
  left_mem_Ici, right_mem_Iic, unique_diff_within_at_univ]]

/-- Let `f` be a measurable function integrable on `a..b`. Choose `s ∈ {Iic a, Ici a, univ}`
and `t ∈ {Iic b, Ici b, univ}`. Suppose that `f` tends to `ca` and `cb` almost surely at the filters
`la` and `lb` from the table below. Then `fderiv_within ℝ (λ p, ∫ x in p.1..p.2, f x) (s.prod t)`
is equal to `(u, v) ↦ u • cb - v • ca`.

| `s`     | `la`         | `t`     | `lb`         |
| ------- | ----         | ---     | ----         |
| `Iic a` | `𝓝[Iic a] a` | `Iic b` | `𝓝[Iic b] b` |
| `Ici a` | `𝓝[Ioi a] a` | `Ici b` | `𝓝[Ioi b] b` |
| `univ`  | `𝓝 a`        | `univ`  | `𝓝 b`        |

-/
lemma fderiv_within_integral_of_tendsto_ae (hf : interval_integrable f volume a b)
  {s t : set ℝ} [FTC_filter a (𝓝[s] a) la] [FTC_filter b (𝓝[t] b) lb]
  (ha : tendsto f (la ⊓ volume.ae) (𝓝 ca)) (hb : tendsto f (lb ⊓ volume.ae) (𝓝 cb))
  (hs : unique_diff_within_at ℝ s a . unique_diff_within_at_Ici_Iic_univ)
  (ht : unique_diff_within_at ℝ t b . unique_diff_within_at_Ici_Iic_univ) :
  fderiv_within ℝ (λ p : ℝ × ℝ, ∫ x in p.1..p.2, f x) (s.prod t) (a, b) =
    ((snd ℝ ℝ ℝ).smul_right cb - (fst ℝ ℝ ℝ).smul_right ca) :=
(integral_has_fderiv_within_at_of_tendsto_ae hf ha hb).fderiv_within $ hs.prod ht

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `b` from the right or from the left,
then `u ↦ ∫ x in a..u, f x` has right (resp., left) derivative `c` at `b`. -/
lemma integral_has_deriv_within_at_of_tendsto_ae_right (hf : interval_integrable f volume a b)
  {s t : set ℝ} [FTC_filter b (𝓝[s] b) (𝓝[t] b)] (hb : tendsto f (𝓝[t] b ⊓ volume.ae) (𝓝 c)) :
  has_deriv_within_at (λ u, ∫ x in a..u, f x) c s b :=
integral_sub_integral_sub_linear_is_o_of_tendsto_ae_right hf hb
  (tendsto_const_pure.mono_right FTC_filter.pure_le) tendsto_id

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
from the left or from the right at `b`, then `u ↦ ∫ x in a..u, f x` has left (resp., right)
derivative `f b` at `b`. -/
lemma integral_has_deriv_within_at_right (hf : interval_integrable f volume a b)
  {s t : set ℝ} [FTC_filter b (𝓝[s] b) (𝓝[t] b)] (hb : continuous_within_at f t b) :
  has_deriv_within_at (λ u, ∫ x in a..u, f x) (f b) s b :=
integral_has_deriv_within_at_of_tendsto_ae_right hf (hb.mono_left inf_le_left)

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `b` from the right or from the left, then the right
(resp., left) derivative of `u ↦ ∫ x in a..u, f x` at `b` equals `c`. -/
lemma deriv_within_integral_of_tendsto_ae_right (hf : interval_integrable f volume a b)
  {s t : set ℝ} [FTC_filter b (𝓝[s] b) (𝓝[t] b)] (hb : tendsto f (𝓝[t] b ⊓ volume.ae) (𝓝 c))
  (hs : unique_diff_within_at ℝ s b . unique_diff_within_at_Ici_Iic_univ) :
  deriv_within (λ u, ∫ x in a..u, f x) s b = c :=
(integral_has_deriv_within_at_of_tendsto_ae_right hf hb).deriv_within hs

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
on the right or on the left at `b`, then the right (resp., left) derivative of
`u ↦ ∫ x in a..u, f x` at `b` equals `f b`. -/
lemma deriv_within_integral_right (hf : interval_integrable f volume a b)
  {s t : set ℝ} [FTC_filter b (𝓝[s] b) (𝓝[t] b)] (hb : continuous_within_at f t b)
  (hs : unique_diff_within_at ℝ s b . unique_diff_within_at_Ici_Iic_univ) :
  deriv_within (λ u, ∫ x in a..u, f x) s b = f b :=
(integral_has_deriv_within_at_right hf hb).deriv_within hs

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `a` from the right or from the left,
then `u ↦ ∫ x in u..b, f x` has right (resp., left) derivative `-c` at `a`. -/
lemma integral_has_deriv_within_at_of_tendsto_ae_left (hf : interval_integrable f volume a b)
  {s t : set ℝ} [FTC_filter a (𝓝[s] a) (𝓝[t] a)] (ha : tendsto f (𝓝[t] a ⊓ volume.ae) (𝓝 c)) :
  has_deriv_within_at (λ u, ∫ x in u..b, f x) (-c) s a :=
by { simp only [integral_symm b],
  exact (integral_has_deriv_within_at_of_tendsto_ae_right hf.symm ha).neg }

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
from the left or from the right at `a`, then `u ↦ ∫ x in u..b, f x` has left (resp., right)
derivative `-f a` at `a`. -/
lemma integral_has_deriv_within_at_left (hf : interval_integrable f volume a b)
  {s t : set ℝ} [FTC_filter a (𝓝[s] a) (𝓝[t] a)] (ha : continuous_within_at f t a) :
  has_deriv_within_at (λ u, ∫ x in u..b, f x) (-f a) s a :=
integral_has_deriv_within_at_of_tendsto_ae_left hf (ha.mono_left inf_le_left)

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `a` from the right or from the left, then the right
(resp., left) derivative of `u ↦ ∫ x in u..b, f x` at `a` equals `-c`. -/
lemma deriv_within_integral_of_tendsto_ae_left (hf : interval_integrable f volume a b)
  {s t : set ℝ} [FTC_filter a (𝓝[s] a) (𝓝[t] a)] (ha : tendsto f (𝓝[t] a ⊓ volume.ae) (𝓝 c))
  (hs : unique_diff_within_at ℝ s a . unique_diff_within_at_Ici_Iic_univ) :
  deriv_within (λ u, ∫ x in u..b, f x) s a = -c :=
(integral_has_deriv_within_at_of_tendsto_ae_left hf ha).deriv_within hs

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
on the right or on the left at `a`, then the right (resp., left) derivative of
`u ↦ ∫ x in u..b, f x` at `a` equals `-f a`. -/
lemma deriv_within_integral_left (hf : interval_integrable f volume a b)
  {s t : set ℝ} [FTC_filter a (𝓝[s] a) (𝓝[t] a)] (ha : continuous_within_at f t a)
  (hs : unique_diff_within_at ℝ s a . unique_diff_within_at_Ici_Iic_univ) :
  deriv_within (λ u, ∫ x in u..b, f x) s a = -f a :=
(integral_has_deriv_within_at_left hf ha).deriv_within hs

end interval_integral
