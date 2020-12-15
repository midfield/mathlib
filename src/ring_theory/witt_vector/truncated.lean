/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/

import ring_theory.witt_vector.init_tail
import tactic.equiv_rw

/-!

# Truncated Witt vectors

The ring of truncated Witt vectors (of length `n`) is a quotient of the ring of Witt vectors.
It retains the first `n` coefficients of each Witt vector.
In this file, we set up the basic quotient API for this ring.

The ring of Witt vectors is the projective limit of all the rings of truncated Witt vectors.

## Main declarations

- `truncated_witt_vector`: the underlying type of the ring of truncated Witt vectors
- `truncated_witt_vector.comm_ring`: the ring structure on truncated Witt vectors
- `witt_vector.truncate`: the quotient homomorphism that truncates a Witt vector,
  to obtain a truncated Witt vector
- `truncated_witt_vector.truncate`: the homomorphism that truncates
  a truncated Witt vector of length `n` to one of length `m` (for some `m ≤ n`)
- `witt_vector.lift`: the unique ring homomorphism into the ring of Witt vectors
  that is compatible with a family of ring homomorphisms to the truncated Witt vectors:
  this realizes the ring of Witt vectors as projective limit of the rings of truncated Witt vectors

-/

open function (injective surjective)

noncomputable theory

variables {p : ℕ} [hp : fact p.prime] (n : ℕ) (R : Type*)

local notation `𝕎` := witt_vector p -- type as `\bbW`

/--
A truncated Witt vector over `R` is a vector of elements of `R`,
i.e., the first `n` coefficients of a Witt vector.
We will define operations on this type that are compatible with the (untruncated) Witt
vector operations.

`truncated_witt_vector p n R` takes a parameter `p : ℕ` that is not used in the definition.
In practice, this number `p` is assumed to be a prime number,
and under this assumption we construct a ring structure on `truncated_witt_vector p n R`.
(`truncated_witt_vector p₁ n R` and `truncated_witt_vector p₂ n R` are definitionally
equal as types but will have different ring operations.)
-/
@[nolint unused_arguments]
def truncated_witt_vector (p : ℕ) (n : ℕ) (R : Type*) := fin n → R

instance (p n : ℕ) (R : Type*) [inhabited R] : inhabited (truncated_witt_vector p n R) :=
⟨λ _, default R⟩

variables {n R}

namespace truncated_witt_vector

variables (p)

/-- Create a `truncated_witt_vector` from a vector `x`. -/
def mk (x : fin n → R) : truncated_witt_vector p n R := x

variables {p}

/-- `x.coeff i` is the `i`th entry of `x`. -/
def coeff (i : fin n) (x : truncated_witt_vector p n R) : R := x i

@[ext]
lemma ext {x y : truncated_witt_vector p n R} (h : ∀ i, x.coeff i = y.coeff i) : x = y :=
funext h

lemma ext_iff {x y : truncated_witt_vector p n R} : x = y ↔ ∀ i, x.coeff i = y.coeff i :=
⟨λ h i, by rw h, ext⟩

@[simp] lemma coeff_mk (x : fin n → R) (i : fin n) :
  (mk p x).coeff i = x i := rfl

@[simp] lemma mk_coeff (x : truncated_witt_vector p n R) :
  mk p (λ i, x.coeff i) = x :=
by { ext i, rw [coeff_mk] }

variable [comm_ring R]

/--
We can turn a truncated Witt vector `x` into a Witt vector
by setting all coefficients after `x` to be 0.
-/
def out (x : truncated_witt_vector p n R) : 𝕎 R :=
witt_vector.mk p $ λ i, if h : i < n then x.coeff ⟨i, h⟩ else 0

@[simp]
lemma coeff_out (x : truncated_witt_vector p n R) (i : fin n) :
  x.out.coeff i = x.coeff i :=
by rw [out, witt_vector.coeff_mk, dif_pos i.is_lt, fin.eta]

lemma out_injective : injective (@out p n R _) :=
begin
  intros x y h,
  ext i,
  rw [witt_vector.ext_iff] at h,
  simpa only [coeff_out] using h ↑i
end

end truncated_witt_vector

namespace witt_vector

variables {p} (n)

section

local attribute [semireducible] witt_vector

/-- `truncate_fun n x` uses the first `n` entries of `x` to construct a `truncated_witt_vector`,
which has the same base `p` as `x`.
This function is bundled into a ring homomorphism in `witt_vector.truncate` -/
def truncate_fun (x : 𝕎 R) : truncated_witt_vector p n R :=
truncated_witt_vector.mk p $ λ i, x.coeff i

end

variables {n}

@[simp] lemma coeff_truncate_fun (x : 𝕎 R) (i : fin n) :
  (truncate_fun n x).coeff i = x.coeff i :=
by rw [truncate_fun, truncated_witt_vector.coeff_mk]

variable [comm_ring R]

@[simp] lemma out_truncate_fun (x : 𝕎 R) :
  (truncate_fun n x).out = init n x :=
begin
  ext i,
  dsimp [truncated_witt_vector.out, init, select],
  split_ifs with hi, swap, { refl },
  rw [coeff_truncate_fun, fin.coe_mk],
end

end witt_vector

namespace truncated_witt_vector

variable [comm_ring R]

@[simp] lemma truncate_fun_out (x : truncated_witt_vector p n R) :
  x.out.truncate_fun n = x :=
by simp only [witt_vector.truncate_fun, coeff_out, mk_coeff]

open witt_vector
variables (p n R)

include hp

instance : has_zero (truncated_witt_vector p n R) :=
⟨truncate_fun n 0⟩

instance : has_one (truncated_witt_vector p n R) :=
⟨truncate_fun n 1⟩

instance : has_add (truncated_witt_vector p n R) :=
⟨λ x y, truncate_fun n (x.out + y.out)⟩

instance : has_mul (truncated_witt_vector p n R) :=
⟨λ x y, truncate_fun n (x.out * y.out)⟩

instance : has_neg (truncated_witt_vector p n R) :=
⟨λ x, truncate_fun n (- x.out)⟩

@[simp] lemma coeff_zero (i : fin n) :
  (0 : truncated_witt_vector p n R).coeff i = 0 :=
begin
  show coeff i (truncate_fun _ 0 : truncated_witt_vector p n R) = 0,
  rw [coeff_truncate_fun, witt_vector.zero_coeff],
end

end truncated_witt_vector

/-- A macro tactic used to prove that `truncate_fun` respects ring operations. -/
meta def tactic.interactive.witt_truncate_fun_tac : tactic unit :=
`[show _ = truncate_fun n _,
  apply truncated_witt_vector.out_injective,
  iterate { rw [out_truncate_fun] },
  rw init_add <|> rw init_mul <|> rw init_neg]

namespace witt_vector

variables (p n R)
variable [comm_ring R]

lemma truncate_fun_surjective :
  surjective (@truncate_fun p n R) :=
λ x, ⟨x.out, truncated_witt_vector.truncate_fun_out x⟩

include hp

@[simp]
lemma truncate_fun_zero : truncate_fun n (0 : 𝕎 R) = 0 := rfl

@[simp]
lemma truncate_fun_one : truncate_fun n (1 : 𝕎 R) = 1 := rfl

variables {p R}

@[simp]
lemma truncate_fun_add (x y : 𝕎 R) :
  truncate_fun n (x + y) = truncate_fun n x + truncate_fun n y :=
by witt_truncate_fun_tac

@[simp]
lemma truncate_fun_mul (x y : 𝕎 R) :
  truncate_fun n (x * y) = truncate_fun n x * truncate_fun n y :=
by witt_truncate_fun_tac

lemma truncate_fun_neg (x : 𝕎 R) :
  truncate_fun n (-x) = -truncate_fun n x :=
by witt_truncate_fun_tac

end witt_vector

namespace truncated_witt_vector
open witt_vector
variables (p n R)
variable [comm_ring R]
include hp

instance : comm_ring (truncated_witt_vector p n R) :=
(truncate_fun_surjective p n R).comm_ring _
  (truncate_fun_zero p n R)
  (truncate_fun_one p n R)
  (truncate_fun_add n)
  (truncate_fun_mul n)
  (truncate_fun_neg n)

end truncated_witt_vector

namespace witt_vector
open truncated_witt_vector

variables (n)
variable [comm_ring R]
include hp

/-- `truncate n` is a ring homomorphism that truncates `x` to its first `n` entries
to obtain a `truncated_witt_vector`, which has the same base `p` as `x`. -/
def truncate : 𝕎 R →+* truncated_witt_vector p n R :=
{ to_fun := truncate_fun n,
  map_zero' := truncate_fun_zero p n R,
  map_add' := truncate_fun_add n,
  map_one' := truncate_fun_one p n R,
  map_mul' := truncate_fun_mul n }

variables (p n R)

lemma truncate_surjective : surjective (truncate n : 𝕎 R → truncated_witt_vector p n R) :=
truncate_fun_surjective p n R

variables {p n R}

@[simp] lemma coeff_truncate (x : 𝕎 R) (i : fin n) :
  (truncate n x).coeff i = x.coeff i :=
coeff_truncate_fun _ _

variables (n)

lemma mem_ker_truncate (x : 𝕎 R) :
  x ∈ (@truncate p _ n R _).ker ↔ ∀ i < n, x.coeff i = 0 :=
begin
  simp only [ring_hom.mem_ker, truncate, truncate_fun, ring_hom.coe_mk,
    truncated_witt_vector.ext_iff, truncated_witt_vector.coeff_mk, coeff_zero],
  exact subtype.forall
end

variables (p)

@[simp] lemma truncate_mk (f : ℕ → R) :
  truncate n (mk p f) = truncated_witt_vector.mk _ (λ k, f k) :=
begin
  ext i,
  rw [coeff_truncate, coeff_mk, truncated_witt_vector.coeff_mk],
end

end witt_vector

namespace truncated_witt_vector

variable [comm_ring R]
include hp

/--
A ring homomorphism that truncates a truncated Witt vector of length `m` to
a truncated Witt vector of length `n`, for `n ≤ m`.
-/
def truncate {m : ℕ} (hm : n ≤ m) : truncated_witt_vector p m R →+* truncated_witt_vector p n R :=
ring_hom.lift_of_surjective
  (witt_vector.truncate m)
  (witt_vector.truncate_surjective p m R)
  (witt_vector.truncate n)
  begin
    intro x,
    simp only [witt_vector.mem_ker_truncate],
    intros h i hi,
    exact h i (lt_of_lt_of_le hi hm)
  end

@[simp] lemma truncate_comp_witt_vector_truncate {m : ℕ} (hm : n ≤ m) :
  (@truncate p _ n R _ m hm).comp (witt_vector.truncate m) = witt_vector.truncate n :=
ring_hom.lift_of_surjective_comp _ _ _ _

@[simp] lemma truncate_witt_vector_truncate {m : ℕ} (hm : n ≤ m) (x : 𝕎 R) :
  truncate hm (witt_vector.truncate m x) = witt_vector.truncate n x :=
ring_hom.lift_of_surjective_comp_apply _ _ _ _ _

@[simp] lemma truncate_truncate {n₁ n₂ n₃ : ℕ} (h1 : n₁ ≤ n₂) (h2 : n₂ ≤ n₃)
  (x : truncated_witt_vector p n₃ R) :
  (truncate h1) (truncate h2 x) = truncate (h1.trans h2) x :=
begin
  obtain ⟨x, rfl⟩ := witt_vector.truncate_surjective p n₃ R x,
  simp only [truncate_witt_vector_truncate],
end

@[simp] lemma truncate_comp {n₁ n₂ n₃ : ℕ} (h1 : n₁ ≤ n₂) (h2 : n₂ ≤ n₃) :
  (@truncate p _ _ R _ _ h1).comp (truncate h2) = truncate (h1.trans h2) :=
begin
  ext1 x, simp only [truncate_truncate, function.comp_app, ring_hom.coe_comp]
end

lemma truncate_surjective {m : ℕ} (hm : n ≤ m) : surjective (@truncate p _ _ R _ _ hm) :=
begin
  intro x,
  obtain ⟨x, rfl⟩ := witt_vector.truncate_surjective p _ R x,
  exact ⟨witt_vector.truncate _ x, truncate_witt_vector_truncate _ _⟩
end

@[simp] lemma coeff_truncate {m : ℕ} (hm : n ≤ m) (i : fin n) (x : truncated_witt_vector p m R) :
  (truncate hm x).coeff i = x.coeff (fin.cast_le hm i) :=
begin
  obtain ⟨y, rfl⟩ := witt_vector.truncate_surjective p _ _ x,
  simp only [truncate_witt_vector_truncate, witt_vector.coeff_truncate, fin.coe_cast_le],
end

section fintype
omit hp

instance {R : Type*} [fintype R] : fintype (truncated_witt_vector p n R) := pi.fintype

variables (p n R)

lemma card {R : Type*} [fintype R] :
  fintype.card (truncated_witt_vector p n R) = fintype.card R ^ n :=
by simp only [truncated_witt_vector, fintype.card_fin, fintype.card_fun]

end fintype

lemma infi_ker_truncate : (⨅ i : ℕ, (@witt_vector.truncate p _ i R _).ker) = ⊥ :=
begin
  rw [submodule.eq_bot_iff],
  intros x hx,
  ext,
  simp only [witt_vector.mem_ker_truncate, ideal.mem_infi, witt_vector.zero_coeff] at hx ⊢,
  exact hx _ _ (nat.lt_succ_self _)
end

end truncated_witt_vector

namespace witt_vector
open truncated_witt_vector (hiding truncate coeff)

section lift_fun

variable [comm_ring R]
variables {S : Type*} (f : Π k : ℕ, S → truncated_witt_vector p k R)
variables (hf : ∀ k₁ k₂ (hk : k₁ ≤ k₂) s, (truncated_witt_vector.truncate hk) (f k₂ s) = f k₁ s)
variables {p R}

/--
Given a family `fₖ : S → truncated_witt_vector p k R` and `s : S`, we produce a Witt vector by
defining the `k`th entry to be the final entry of `fₖ s`.
-/
def lift_fun (s : S) : 𝕎 R :=
witt_vector.mk p $ λ k, truncated_witt_vector.coeff (fin.last k) (f (k+1) s)

variables {f}
include hf

@[simp] lemma truncate_lift_fun (s : S) :
  witt_vector.truncate n (lift_fun f s) = f n s :=
begin
  ext i,
  simp only [lift_fun, truncated_witt_vector.coeff_mk, witt_vector.truncate_mk,
    ← hf (↑i + 1) n i.is_lt, truncated_witt_vector.coeff_truncate],
  -- this is a bit unfortunate
  congr' with _,
  simp only [fin.coe_last, fin.coe_cast_le]
end

/-- The uniqueness part of the universal property of `𝕎 R`. -/
lemma lift_fun_unique (g : S → 𝕎 R) (hg : ∀ k s, (witt_vector.truncate k) (g s) = f k s) :
  lift_fun f = g :=
begin
  ext1 x,
  rw [← sub_eq_zero, ← ideal.mem_bot, ← infi_ker_truncate, ideal.mem_infi],
  intro i,
  simp only [ring_hom.mem_ker, ← hg, truncate_lift_fun hf, ring_hom.map_sub, sub_self]
end

omit hf
include hp

/-- The universal property of `𝕎 R` as projective limit of truncated Witt vector rings. -/
@[simps] def lift_fun_equiv : {f : Π k, S → truncated_witt_vector p k R // ∀ k₁ k₂ (hk : k₁ ≤ k₂) s,
  (truncated_witt_vector.truncate hk) (f k₂ s) = f k₁ s} ≃ (S → 𝕎 R) :=
{ to_fun := λ f, lift_fun f.1,
  inv_fun := λ g, ⟨λ k, (truncate k) ∘ g,
    by { intros _ _ h x, rw [← truncate_comp_witt_vector_truncate h], refl }⟩,
  left_inv := by { rintro ⟨f, hf⟩, simp only, ext n s : 2, exact truncate_lift_fun hf s },
  right_inv := λ g, lift_fun_unique
    (by { intros, simp only [truncate_witt_vector_truncate, function.comp_app] })
    _ (λ _ _, rfl) }

lemma fun_ext (g₁ g₂ : S → 𝕎 R) (h : ∀ k, (truncate k) ∘ g₁ = (truncate k) ∘ g₂) :
  g₁ = g₂ :=
lift_fun_equiv.symm.injective $ subtype.ext $ funext h

end lift_fun

section lift_monoid_hom

variable [comm_ring R]
variables {S : Type*} [monoid S] (f : Π k : ℕ, S →* truncated_witt_vector p k R)
variables (hf : ∀ k₁ k₂ (hk : k₁ ≤ k₂) x, (truncated_witt_vector.truncate hk) (f k₂ x) = f k₁ x)
variables {p R}

include hf

/--
Given compatible monoid homs from `M` into `truncated_witt_vector n` for each `n`,
we can lift these to a monoid hom `S → 𝕎 R`.

`lift` defines the universal property of `𝕎 R` as the inverse limit of `truncated_witt_vector n`.
-/
def lift_monoid_hom : S →* 𝕎 R :=
by refine_struct { to_fun := lift_fun (λ k, f k) };
   { intros,
     rw [← sub_eq_zero, ← ideal.mem_bot, ← infi_ker_truncate, ideal.mem_infi],
     simp [hf, ring_hom.mem_ker] }

variable {f}

@[simp] lemma truncate_lift_monoid_hom (s : S) :
  witt_vector.truncate n (lift_monoid_hom _ hf s) = f n s :=
truncate_lift_fun hf _

@[simp] lemma truncate_comp_lift_monoid_hom :
  monoid_hom.comp (↑(@witt_vector.truncate p hp n R _)) (lift_monoid_hom _ hf) = f n :=
by { ext1, exact truncate_lift_monoid_hom _ _ }

/-- The uniqueness part of the universal property of `𝕎 R` for monoid homs. -/
lemma lift_monoid_hom_unique (g : S →* 𝕎 R) (hg : ∀ k s, (witt_vector.truncate k) (g s) = f k s) :
  lift_monoid_hom _ hf = g :=
by { apply monoid_hom.coe_inj, exact lift_fun_unique hf _ hg }

omit hf
include hp

/-- The universal property of `𝕎 R` as projective limit of truncated Witt vector rings. -/
@[simps] def lift_monoid_hom_equiv :
  {f : Π k, S →* truncated_witt_vector p k R // ∀ k₁ k₂ (hk : k₁ ≤ k₂) s,
  (truncated_witt_vector.truncate hk) (f k₂ s) = f k₁ s} ≃ (S →* 𝕎 R) :=
{ to_fun := λ f, lift_monoid_hom f.1 f.2,
  inv_fun := λ g, ⟨λ k, monoid_hom.comp (↑(@truncate p hp k R _)) g,
    by { intros _ _ h x, rw [← truncate_comp_witt_vector_truncate h], refl }⟩,
  left_inv := by { rintro ⟨f, hf⟩, simp only [truncate_comp_lift_monoid_hom] },
  right_inv := λ g, lift_monoid_hom_unique _ _ (λ _ _, rfl) }

lemma monoid_hom_ext (g₁ g₂ : S →* 𝕎 R) (h : ∀ k s, truncate k (g₁ s) = truncate k (g₂ s)) :
  g₁ = g₂ :=
lift_monoid_hom_equiv.symm.injective $ by { ext : 3, apply h }

end lift_monoid_hom

section lift_add_monoid_hom

variable [comm_ring R]
variables {S : Type*} [add_monoid S] (f : Π k : ℕ, S →+ truncated_witt_vector p k R)
variables (hf : ∀ k₁ k₂ (hk : k₁ ≤ k₂) x, (truncated_witt_vector.truncate hk) (f k₂ x) = f k₁ x)
variables {p R}

include hf

/--
Given compatible monoid homs from `M` into `truncated_witt_vector n` for each `n`,
we can lift these to a monoid hom `S → 𝕎 R`.

`lift` defines the universal property of `𝕎 R` as the inverse limit of `truncated_witt_vector n`.
-/
def lift_add_monoid_hom : S →+ 𝕎 R :=
by refine_struct { to_fun := lift_fun (λ k, f k) };
   { intros,
     rw [← sub_eq_zero, ← ideal.mem_bot, ← infi_ker_truncate, ideal.mem_infi],
     simp [hf, ring_hom.mem_ker] }

variable {f}

@[simp] lemma truncate_lift_add_monoid_hom (s : S) :
  witt_vector.truncate n (lift_add_monoid_hom _ hf s) = f n s :=
truncate_lift_fun hf _

@[simp] lemma truncate_comp_lift_add_monoid_hom :
  add_monoid_hom.comp (↑(@witt_vector.truncate p hp n R _)) (lift_add_monoid_hom _ hf) = f n :=
by { ext1, exact truncate_lift_add_monoid_hom _ _ }

/-- The uniqueness part of the universal property of `𝕎 R` for additive monoid homs. -/
lemma lift_add_monoid_hom_unique (g : S →+ 𝕎 R) (hg : ∀ k s, (witt_vector.truncate k) (g s) = f k s) :
  lift_add_monoid_hom _ hf = g :=
by { apply add_monoid_hom.coe_inj, exact lift_fun_unique hf _ hg }

omit hf
include hp

/-- The universal property of `𝕎 R` as projective limit of truncated Witt vector rings. -/
@[simps] def lift_add_monoid_hom_equiv :
  {f : Π k, S →+ truncated_witt_vector p k R // ∀ k₁ k₂ (hk : k₁ ≤ k₂) s,
  (truncated_witt_vector.truncate hk) (f k₂ s) = f k₁ s} ≃ (S →+ 𝕎 R) :=
{ to_fun := λ f, lift_add_monoid_hom f.1 f.2,
  inv_fun := λ g, ⟨λ k, add_monoid_hom.comp (↑(@truncate p hp k R _)) g,
    by { intros _ _ h x, rw [← truncate_comp_witt_vector_truncate h], refl }⟩,
  left_inv := by { rintro ⟨f, hf⟩, simp only [truncate_comp_lift_add_monoid_hom] },
  right_inv := λ g, lift_add_monoid_hom_unique _ _ (λ _ _, rfl) }

lemma add_monoid_hom_ext (g₁ g₂ : S →+ 𝕎 R) (h : ∀ k s, truncate k (g₁ s) = truncate k (g₂ s)) :
  g₁ = g₂ :=
lift_add_monoid_hom_equiv.symm.injective $ by { ext : 3, apply h }

end lift_add_monoid_hom

section lift

variable [comm_ring R]
variables {S : Type*} [semiring S]
variables (f : Π k : ℕ, S →+* truncated_witt_vector p k R)
variables (hf : ∀ k₁ k₂ (hk : k₁ ≤ k₂) s, truncated_witt_vector.truncate hk (f k₂ s) = f k₁ s)
variables {p R}
include hf

/--
Given compatible ring homs from `S` into `truncated_witt_vector n` for each `n`, we can lift these
to a ring hom `S → 𝕎 R`.

`lift` defines the universal property of `𝕎 R` as the inverse limit of `truncated_witt_vector n`.
-/
def lift : S →+* 𝕎 R :=
{ to_fun := lift_fun (λ k, f k),
  map_zero' := by { convert (lift_add_monoid_hom (λ k, ↑(f k)) _).map_zero,
    { funext k, refl } },
  -- map_one' := (lift_monoid_hom _ hf).map_one,
  map_add' := _,
    }

variable {f}

@[simp] lemma truncate_lift (s : S) :
  witt_vector.truncate n (lift _ hf s) = f n s :=
truncate_lift_fun _ hf s

@[simp] lemma truncate_comp_lift :
  (witt_vector.truncate n).comp (lift _ hf) = f n :=
by { ext1, rw [ring_hom.comp_apply, truncate_lift] }

/-- The uniqueness part of the universal property of `𝕎 R`. -/
lemma lift_unique (g : S →+* 𝕎 R) (g_compat : ∀ k, (witt_vector.truncate k).comp g = f k) :
  lift _ hf = g :=
begin
  ext1 x,
  rw [← sub_eq_zero, ← ideal.mem_bot, ← infi_ker_truncate, ideal.mem_infi],
  intro i,
  simp only [ring_hom.mem_ker, g_compat, ←ring_hom.comp_apply,
    truncate_comp_lift, ring_hom.map_sub, sub_self],
end

omit hf
include hp

/-- The universal property of `𝕎 R` as projective limit of truncated Witt vector rings. -/
@[simps] def lift_equiv : {f : Π k, S →+* truncated_witt_vector p k R // ∀ k₁ k₂ (hk : k₁ ≤ k₂),
  (truncated_witt_vector.truncate hk).comp (f k₂) = f k₁} ≃ (S →+* 𝕎 R) :=
{ to_fun := λ f, lift f.1 f.2,
  inv_fun := λ g, ⟨λ k, (truncate k).comp g,
    by { intros _ _ h, simp only [←ring_hom.comp_assoc, truncate_comp_witt_vector_truncate] }⟩,
  left_inv := by { rintro ⟨f, hf⟩, simp only [truncate_comp_lift] },
  right_inv := λ g, lift_unique _ _ $ λ _, rfl }

lemma hom_ext (g₁ g₂ : S →+* 𝕎 R) (h : ∀ k, (truncate k).comp g₁ = (truncate k).comp g₂) :
  g₁ = g₂ :=
lift_equiv.symm.injective $ subtype.ext $ funext h

end lift

end witt_vector
