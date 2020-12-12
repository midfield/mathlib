/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Archimedean groups and fields.
-/
import algebra.field_power
import data.rat

variables {α : Type*}

/-- An ordered additive commutative monoid is called `archimedean` if for any two elements `x`, `y`
such that `0 < y` there exists a natural number `n` such that `x ≤ n •ℕ y`. -/
class archimedean (α) [ordered_add_comm_monoid α] : Prop :=
(arch : ∀ (x : α) {y}, 0 < y → ∃ n : ℕ, x ≤ n •ℕ y)

namespace linear_ordered_add_comm_group
variables [linear_ordered_add_comm_group α] [archimedean α]

/-- An archimedean decidable linearly ordered `add_comm_group` has a version of the floor: for
`a > 0`, any `g` in the group lies between some two consecutive multiples of `a`. -/
lemma exists_int_smul_near_of_pos {a : α} (ha : 0 < a) (g : α) :
  ∃ k, k •ℤ a ≤ g ∧ g < (k + 1) •ℤ a :=
begin
  let s : set ℤ := {n : ℤ | n •ℤ a ≤ g},
  obtain ⟨k, hk : -g ≤ k •ℕ a⟩ := archimedean.arch (-g) ha,
  have h_ne : s.nonempty := ⟨-k, by simpa using neg_le_neg hk⟩,
  obtain ⟨k, hk⟩ := archimedean.arch g ha,
  have h_bdd : ∀ n ∈ s, n ≤ (k : ℤ) :=
    λ n hn, (gsmul_le_gsmul_iff ha).mp (le_trans hn hk : n •ℤ a ≤ k •ℤ a),
  obtain ⟨m, hm, hm'⟩ := int.exists_greatest_of_bdd ⟨k, h_bdd⟩ h_ne,
  refine ⟨m, hm, _⟩,
  by_contra H,
  linarith [hm' _ $ not_lt.mp H]
end

lemma exists_int_smul_near_of_pos' {a : α} (ha : 0 < a) (g : α) :
  ∃ k, 0 ≤ g - k •ℤ a ∧ g - k •ℤ a < a :=
begin
  obtain ⟨k, h1, h2⟩ := exists_int_smul_near_of_pos ha g,
  refine ⟨k, sub_nonneg.mpr h1, _⟩,
  have : g < k •ℤ a + 1 •ℤ a, by rwa ← add_gsmul a k 1,
  simpa [sub_lt_iff_lt_add']
end

end linear_ordered_add_comm_group

theorem exists_nat_gt [ordered_semiring α] [nontrivial α] [archimedean α]
  (x : α) : ∃ n : ℕ, x < n :=
let ⟨n, h⟩ := archimedean.arch x zero_lt_one in
⟨n+1, lt_of_le_of_lt (by rwa ← nsmul_one)
  (nat.cast_lt.2 (nat.lt_succ_self _))⟩

theorem exists_nat_ge [ordered_semiring α] [archimedean α] (x : α) :
  ∃ n : ℕ, x ≤ n :=
begin
  nontriviality α,
  exact (exists_nat_gt x).imp (λ n, le_of_lt)
end

lemma add_one_pow_unbounded_of_pos [ordered_semiring α] [nontrivial α] [archimedean α]
  (x : α) {y : α} (hy : 0 < y) :
  ∃ n : ℕ, x < (y + 1) ^ n :=
let ⟨n, h⟩ := archimedean.arch x hy in
⟨n, calc x ≤ n •ℕ y : h
       ... < 1 + n •ℕ y : lt_one_add _
       ... ≤ (1 + y) ^ n : one_add_mul_le_pow' (mul_nonneg (le_of_lt hy) (le_of_lt hy))
                             (le_of_lt $ lt_trans hy (lt_one_add y)) _
       ... = (y + 1) ^ n : by rw [add_comm]⟩

section linear_ordered_ring
variables [linear_ordered_ring α] [archimedean α]

lemma pow_unbounded_of_one_lt (x : α) {y : α} (hy1 : 1 < y) :
  ∃ n : ℕ, x < y ^ n :=
sub_add_cancel y 1 ▸ add_one_pow_unbounded_of_pos _ (sub_pos.2 hy1)

/-- Every x greater than or equal to 1 is between two successive
natural-number powers of every y greater than one. -/
lemma exists_nat_pow_near {x : α} {y : α} (hx : 1 ≤ x) (hy : 1 < y) :
  ∃ n : ℕ, y ^ n ≤ x ∧ x < y ^ (n + 1) :=
have h : ∃ n : ℕ, x < y ^ n, from pow_unbounded_of_one_lt _ hy,
by classical; exact let n := nat.find h in
  have hn  : x < y ^ n, from nat.find_spec h,
  have hnp : 0 < n,     from nat.pos_iff_ne_zero.2 (λ hn0,
    by rw [hn0, pow_zero] at hn; exact (not_le_of_gt hn hx)),
  have hnsp : nat.pred n + 1 = n,     from nat.succ_pred_eq_of_pos hnp,
  have hltn : nat.pred n < n,         from nat.pred_lt (ne_of_gt hnp),
  ⟨nat.pred n, le_of_not_lt (nat.find_min h hltn), by rwa hnsp⟩

theorem exists_int_gt (x : α) : ∃ n : ℤ, x < n :=
let ⟨n, h⟩ := exists_nat_gt x in ⟨n, by rwa ← coe_coe⟩

theorem exists_int_lt (x : α) : ∃ n : ℤ, (n : α) < x :=
let ⟨n, h⟩ := exists_int_gt (-x) in ⟨-n, by rw int.cast_neg; exact neg_lt.1 h⟩

theorem exists_floor (x : α) :
  ∃ (fl : ℤ), ∀ (z : ℤ), z ≤ fl ↔ (z : α) ≤ x :=
begin
  haveI := classical.prop_decidable,
  have : ∃ (ub : ℤ), (ub:α) ≤ x ∧ ∀ (z : ℤ), (z:α) ≤ x → z ≤ ub :=
  int.exists_greatest_of_bdd
    (let ⟨n, hn⟩ := exists_int_gt x in ⟨n, λ z h',
      int.cast_le.1 $ le_trans h' $ le_of_lt hn⟩)
    (let ⟨n, hn⟩ := exists_int_lt x in ⟨n, le_of_lt hn⟩),
  refine this.imp (λ fl h z, _),
  cases h with h₁ h₂,
  exact ⟨λ h, le_trans (int.cast_le.2 h) h₁, h₂ z⟩,
end

end linear_ordered_ring

section linear_ordered_field

variables [linear_ordered_field α]

/-- Every positive `x` is between two successive integer powers of
another `y` greater than one. This is the same as `exists_int_pow_near'`,
but with ≤ and < the other way around. -/
lemma exists_int_pow_near [archimedean α]
  {x : α} {y : α} (hx : 0 < x) (hy : 1 < y) :
  ∃ n : ℤ, y ^ n ≤ x ∧ x < y ^ (n + 1) :=
by classical; exact
let ⟨N, hN⟩ := pow_unbounded_of_one_lt x⁻¹ hy in
  have he: ∃ m : ℤ, y ^ m ≤ x, from
    ⟨-N, le_of_lt (by rw [(fpow_neg y (↑N))];
    exact (inv_lt hx (lt_trans (inv_pos.2 hx) hN)).1 hN)⟩,
let ⟨M, hM⟩ := pow_unbounded_of_one_lt x hy in
  have hb: ∃ b : ℤ, ∀ m, y ^ m ≤ x → m ≤ b, from
    ⟨M, λ m hm, le_of_not_lt (λ hlt, not_lt_of_ge
  (fpow_le_of_le (le_of_lt hy) (le_of_lt hlt)) (lt_of_le_of_lt hm hM))⟩,
let ⟨n, hn₁, hn₂⟩ := int.exists_greatest_of_bdd hb he in
  ⟨n, hn₁, lt_of_not_ge (λ hge, not_le_of_gt (int.lt_succ _) (hn₂ _ hge))⟩

/-- Every positive `x` is between two successive integer powers of
another `y` greater than one. This is the same as `exists_int_pow_near`,
but with ≤ and < the other way around. -/
lemma exists_int_pow_near' [archimedean α]
  {x : α} {y : α} (hx : 0 < x) (hy : 1 < y) :
  ∃ n : ℤ, y ^ n < x ∧ x ≤ y ^ (n + 1) :=
let ⟨m, hle, hlt⟩ := exists_int_pow_near (inv_pos.2 hx) hy in
have hyp : 0 < y, from lt_trans zero_lt_one hy,
⟨-(m+1),
by rwa [fpow_neg, inv_lt (fpow_pos_of_pos hyp _) hx],
by rwa [neg_add, neg_add_cancel_right, fpow_neg,
        le_inv hx (fpow_pos_of_pos hyp _)]⟩

/-- For any `y < 1` and any positive `x`, there exists `n : ℕ` with `y ^ n < x`. -/
lemma exists_pow_lt_of_lt_one [archimedean α] {x y : α} (hx : 0 < x) (hy : y < 1) :
  ∃ n : ℕ, y ^ n < x :=
begin
  by_cases y_pos : y ≤ 0,
  { use 1, simp only [pow_one], linarith, },
  rw [not_le] at y_pos,
  rcases pow_unbounded_of_one_lt (x⁻¹) (one_lt_inv y_pos hy) with ⟨q, hq⟩,
  exact ⟨q, by rwa [inv_pow', inv_lt_inv hx (pow_pos y_pos _)] at hq⟩
end

/-- Given `x` and `y` between `0` and `1`, `x` is between two successive powers of `y`.
This is the same as `exists_nat_pow_near`, but for elements between `0` and `1` -/
lemma exists_nat_pow_near_of_lt_one [archimedean α]
  {x : α} {y : α} (xpos : 0 < x) (hx : x ≤ 1) (ypos : 0 < y) (hy : y < 1) :
  ∃ n : ℕ, y ^ (n + 1) < x ∧ x ≤ y ^ n :=
begin
  rcases exists_nat_pow_near (one_le_inv_iff.2 ⟨xpos, hx⟩) (one_lt_inv_iff.2 ⟨ypos, hy⟩)
    with ⟨n, hn, h'n⟩,
  refine ⟨n, _, _⟩,
  { rwa [inv_pow', inv_lt_inv xpos (pow_pos ypos _)] at h'n },
  { rwa [inv_pow', inv_le_inv (pow_pos ypos _) xpos] at hn }
end

variables [floor_ring α]

lemma sub_floor_div_mul_nonneg (x : α) {y : α} (hy : 0 < y) :
  0 ≤ x - ⌊x / y⌋ * y :=
begin
  conv in x {rw ← div_mul_cancel x (ne_of_lt hy).symm},
  rw ← sub_mul,
  exact mul_nonneg (sub_nonneg.2 (floor_le _)) (le_of_lt hy)
end

lemma sub_floor_div_mul_lt (x : α) {y : α} (hy : 0 < y) :
  x - ⌊x / y⌋ * y < y :=
sub_lt_iff_lt_add.2 begin
  conv in y {rw ← one_mul y},
  conv in x {rw ← div_mul_cancel x (ne_of_lt hy).symm},
  rw ← add_mul,
  exact (mul_lt_mul_right hy).2 (by rw add_comm; exact lt_floor_add_one _),
end

end linear_ordered_field

instance : archimedean ℕ :=
⟨λ n m m0, ⟨n, by simpa only [mul_one, nat.nsmul_eq_mul] using nat.mul_le_mul_left n m0⟩⟩

instance : archimedean ℤ :=
⟨λ n m m0, ⟨n.to_nat, le_trans (int.le_to_nat _) $
by simpa only [nsmul_eq_mul, int.nat_cast_eq_coe_nat, zero_add, mul_one]
  using mul_le_mul_of_nonneg_left (int.add_one_le_iff.2 m0) (int.coe_zero_le n.to_nat)⟩⟩

/-- A linear ordered archimedean ring is a floor ring. This is not an `instance` because in some
cases we have a computable `floor` function. -/
noncomputable def archimedean.floor_ring (α)
  [linear_ordered_ring α] [archimedean α] : floor_ring α :=
{ floor := λ x, classical.some (exists_floor x),
  le_floor := λ z x, classical.some_spec (exists_floor x) z }

section linear_ordered_field
variables [linear_ordered_field α]

theorem archimedean_iff_nat_lt :
  archimedean α ↔ ∀ x : α, ∃ n : ℕ, x < n :=
⟨@exists_nat_gt α _ _, λ H, ⟨λ x y y0,
  (H (x / y)).imp $ λ n h, le_of_lt $
  by rwa [div_lt_iff y0, ← nsmul_eq_mul] at h⟩⟩

theorem archimedean_iff_nat_le :
  archimedean α ↔ ∀ x : α, ∃ n : ℕ, x ≤ n :=
archimedean_iff_nat_lt.trans
⟨λ H x, (H x).imp $ λ _, le_of_lt,
 λ H x, let ⟨n, h⟩ := H x in ⟨n+1,
   lt_of_le_of_lt h (nat.cast_lt.2 (lt_add_one _))⟩⟩

theorem exists_rat_gt [archimedean α] (x : α) : ∃ q : ℚ, x < q :=
let ⟨n, h⟩ := exists_nat_gt x in ⟨n, by rwa rat.cast_coe_nat⟩

theorem archimedean_iff_rat_lt :
  archimedean α ↔ ∀ x : α, ∃ q : ℚ, x < q :=
⟨@exists_rat_gt α _,
  λ H, archimedean_iff_nat_lt.2 $ λ x,
  let ⟨q, h⟩ := H x in
  ⟨nat_ceil q, lt_of_lt_of_le h $
    by simpa only [rat.cast_coe_nat] using (@rat.cast_le α _ _ _).2 (le_nat_ceil _)⟩⟩

theorem archimedean_iff_rat_le :
  archimedean α ↔ ∀ x : α, ∃ q : ℚ, x ≤ q :=
archimedean_iff_rat_lt.trans
⟨λ H x, (H x).imp $ λ _, le_of_lt,
 λ H x, let ⟨n, h⟩ := H x in ⟨n+1,
   lt_of_le_of_lt h (rat.cast_lt.2 (lt_add_one _))⟩⟩

variable [archimedean α]

theorem exists_rat_lt (x : α) : ∃ q : ℚ, (q : α) < x :=
let ⟨n, h⟩ := exists_int_lt x in ⟨n, by rwa rat.cast_coe_int⟩

theorem exists_rat_btwn {x y : α} (h : x < y) : ∃ q : ℚ, x < q ∧ (q:α) < y :=
begin
  cases exists_nat_gt (y - x)⁻¹ with n nh,
  cases exists_floor (x * n) with z zh,
  refine ⟨(z + 1 : ℤ) / n, _⟩,
  have n0' := (inv_pos.2 (sub_pos.2 h)).trans nh,
  have n0 := nat.cast_pos.1 n0',
  rw [rat.cast_div_of_ne_zero, rat.cast_coe_nat, rat.cast_coe_int, div_lt_iff n0'],
  refine ⟨(lt_div_iff n0').2 $
    (lt_iff_lt_of_le_iff_le (zh _)).1 (lt_add_one _), _⟩,
  rw [int.cast_add, int.cast_one],
  refine lt_of_le_of_lt (add_le_add_right ((zh _).1 (le_refl _)) _) _,
  rwa [← lt_sub_iff_add_lt', ← sub_mul,
       ← div_lt_iff' (sub_pos.2 h), one_div],
  { rw [rat.coe_int_denom, nat.cast_one], exact one_ne_zero },
  { intro H, rw [rat.coe_nat_num, ← coe_coe, nat.cast_eq_zero] at H, subst H, cases n0 },
  { rw [rat.coe_nat_denom, nat.cast_one], exact one_ne_zero }
end

theorem exists_nat_one_div_lt {ε : α} (hε : 0 < ε) : ∃ n : ℕ, 1 / (n + 1: α) < ε :=
begin
  cases exists_nat_gt (1/ε) with n hn,
  use n,
  rw [div_lt_iff, ← div_lt_iff' hε],
  { apply hn.trans,
    simp [zero_lt_one] },
  { exact n.cast_add_one_pos }
end

theorem exists_pos_rat_lt {x : α} (x0 : 0 < x) : ∃ q : ℚ, 0 < q ∧ (q : α) < x :=
by simpa only [rat.cast_pos] using exists_rat_btwn x0

include α
@[simp] theorem rat.cast_floor (x : ℚ) :
  by haveI := archimedean.floor_ring α; exact ⌊(x:α)⌋ = ⌊x⌋ :=
begin
  haveI := archimedean.floor_ring α,
  apply le_antisymm,
  { rw [le_floor, ← @rat.cast_le α, rat.cast_coe_int],
    apply floor_le },
  { rw [le_floor, ← rat.cast_coe_int, rat.cast_le],
    apply floor_le }
end

end linear_ordered_field

section
variables [linear_ordered_field α]

/-- `round` rounds a number to the nearest integer. `round (1 / 2) = 1` -/
def round [floor_ring α] (x : α) : ℤ := ⌊x + 1 / 2⌋

lemma abs_sub_round [floor_ring α] (x : α) : abs (x - round x) ≤ 1 / 2 :=
begin
  rw [round, abs_sub_le_iff],
  have := floor_le (x + 1 / 2),
  have := lt_floor_add_one (x + 1 / 2),
  split; linarith
end

variable [archimedean α]

theorem exists_rat_near (x : α) {ε : α} (ε0 : 0 < ε) :
  ∃ q : ℚ, abs (x - q) < ε :=
let ⟨q, h₁, h₂⟩ := exists_rat_btwn $
  lt_trans ((sub_lt_self_iff x).2 ε0) ((lt_add_iff_pos_left x).2 ε0) in
⟨q, abs_sub_lt_iff.2 ⟨sub_lt.1 h₁, sub_lt_iff_lt_add.2 h₂⟩⟩

instance : archimedean ℚ :=
archimedean_iff_rat_le.2 $ λ q, ⟨q, by rw rat.cast_id⟩

@[simp] theorem rat.cast_round (x : ℚ) : by haveI := archimedean.floor_ring α;
  exact round (x:α) = round x :=
have ((x + (1 : ℚ) / (2 : ℚ) : ℚ) : α) = x + 1 / 2, by simp,
by rw [round, round, ← this, rat.cast_floor]

end
variables [archimedean α]
variables {l : filter β} {f : β → α}

/-- If a function tends to infinity along a filter, then this function multiplied by a positive
constant (on the left) also tends to infinity. The archimedean assumption is convenient to get a
statement that works on `ℕ`, `ℤ` and `ℝ`, although not necessary (a version in ordered fields is
given in `tendsto_at_top_mul_left'`). -/
lemma tendsto_at_top_mul_left  {r : α} (hr : 0 < r) (hf : tendsto f l at_top) :
  tendsto (λx, r * f x) l at_top :=
let ⟨n, hn⟩ := archimedean.arch
/-begin
  apply tendsto_at_top.2 (λb, _),
  obtain ⟨n : ℕ, hn : 1 ≤ n •ℕ r⟩ := archimedean.arch 1 hr,
  have hn' : 1 ≤ r * n, by rwa nsmul_eq_mul' at hn,
  filter_upwards [tendsto_at_top.1 hf (n * max b 0)],
  assume x hx,
  calc b ≤ 1 * max b 0 : by { rw [one_mul], exact le_max_left _ _ }
  ... ≤ (r * n) * max b 0 : mul_le_mul_of_nonneg_right hn' (le_max_right _ _)
  ... = r * (n * max b 0) : by rw [mul_assoc]
  ... ≤ r * f x : mul_le_mul_of_nonneg_left hx (le_of_lt hr)
end-/

/-- If a function tends to infinity along a filter, then this function multiplied by a positive
constant (on the right) also tends to infinity. The archimedean assumption is convenient to get a
statement that works on `ℕ`, `ℤ` and `ℝ`, although not necessary (a version in ordered fields is
given in `tendsto_at_top_mul_right'`). -/
lemma tendsto_at_top_mul_right {r : α} (hr : 0 < r) (hf : tendsto f l at_top) :
  tendsto (λx, f x * r) l at_top :=
begin
  apply tendsto_at_top.2 (λb, _),
  obtain ⟨n : ℕ, hn : 1 ≤ n •ℕ r⟩ := archimedean.arch 1 hr,
  have hn' : 1 ≤ (n : α) * r, by rwa nsmul_eq_mul at hn,
  filter_upwards [tendsto_at_top.1 hf (max b 0 * n)],
  assume x hx,
  calc b ≤ max b 0 * 1 : by { rw [mul_one], exact le_max_left _ _ }
  ... ≤ max b 0 * (n * r) : mul_le_mul_of_nonneg_left hn' (le_max_right _ _)
  ... = (max b 0 * n) * r : by rw [mul_assoc]
  ... ≤ f x * r : mul_le_mul_of_nonneg_right hx (le_of_lt hr)
end

