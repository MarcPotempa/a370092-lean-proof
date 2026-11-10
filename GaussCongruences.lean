/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

open Finset Nat

/--
A370092: $a(0) = 1$,
$$a(n) = (-1)^n + \frac{1}{2} \sum_{j=1}^n (1-(-1)^j-(-2)^j) \binom{n}{j} a(n-j) \quad \text{for } n > 0$$
The sequence is defined in $\mathbb{Q}$ to directly translate the recurrence relation.
The terms are conjectured to be integers.
-/
noncomputable def a (n : ℕ) : ℚ :=
  match n with
  | 0 => 1
  | m_plus_one@(m + 1) =>
    -- The sum is over j from 1 to m_plus_one. k runs from 0 to m.
    let sum_val : ℚ := Finset.sum (Finset.range m_plus_one) (fun k =>
      let j : ℕ := k + 1 -- j is the index for the sum

      let a_term : ℚ := a (m_plus_one - j)
      let coeff_factor : ℚ := 1 - (-1 : ℚ)^j - (-2 : ℚ)^j

      (m_plus_one.choose j : ℚ) * coeff_factor * a_term
    )
    (-1 : ℚ)^m_plus_one + (1 / 2) * sum_val

-- We formally define an eventually periodic sequence.
/-- A sequence `f` is eventually periodic with period `P` if after some index `N`, `f(n + P) = f(n)`. -/
def eventually_periodic {α : Type*} (f : ℕ → α) (P : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → f (n + P) = f n

/--
The reduction of `a n` modulo `k`. Since all terms of `a n` are integers, we take the
numerator of the rational number representation, which is the integer value, and reduce it modulo `k`.
This requires `k > 0`, which is guaranteed by `2 < k`.
-/
noncomputable def a_mod_k (k : ℕ) (n : ℕ) : ZMod k :=
  Int.cast (a n).num

namespace A370092

open Function Polynomial
open fwdDiff

/-- m-th forward difference at 0 of a sequence. -/
def dd {R : Type*} [CommRing R] (m : ℕ) (f : ℕ → R) : R := ((fwdDiff (1:ℕ))^[m] f) 0

section basic
variable {R : Type*} [CommRing R]

lemma dd_zero (f : ℕ → R) : dd 0 f = f 0 := by simp [dd]

lemma dd_eq_sum (m : ℕ) (f : ℕ → R) :
    dd m f = ∑ k ∈ range (m + 1), ((-1 : ℤ) ^ (m - k) * m.choose k) • f k := by
  unfold dd
  rw [fwdDiff_iter_eq_sum_shift]
  simp

lemma dd_add (m : ℕ) (f g : ℕ → R) : dd m (fun s => f s + g s) = dd m f + dd m g := by
  unfold dd
  have : (fun s => f s + g s) = f + g := rfl
  rw [this, fwdDiff_iter_add]; rfl

lemma dd_sub (m : ℕ) (f g : ℕ → R) : dd m (fun s => f s - g s) = dd m f - dd m g := by
  simp only [dd_eq_sum, smul_sub, sum_sub_distrib]

lemma dd_const_mul (m : ℕ) (c : R) (f : ℕ → R) : dd m (fun s => c * f s) = c * dd m f := by
  simp only [dd_eq_sum, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  simp only [zsmul_eq_mul]; ring

lemma dd_sum {ι : Type*} (m : ℕ) (t : Finset ι) (f : ι → ℕ → R) :
    dd m (fun s => ∑ i ∈ t, f i s) = ∑ i ∈ t, dd m (f i) := by
  simp only [dd_eq_sum, smul_sum]
  rw [sum_comm]

lemma dd_shift (m : ℕ) (f : ℕ → R) : dd m (fun s => f (s + 1)) = dd m f + dd (m + 1) f := by
  unfold dd
  rw [fwdDiff_iter_comp_add, iterate_succ_apply']
  simp [fwdDiff]

lemma dd_congr (m : ℕ) {f g : ℕ → R} (h : ∀ s, f s = g s) : dd m f = dd m g := by
  have : f = g := funext h
  rw [this]

/-- polynomial sequences of degree < m are killed -/
lemma dd_poly_eq_zero (P : R[X]) {m : ℕ} (hP : P.natDegree < m) :
    dd m (fun s : ℕ => P.eval (s : R)) = 0 := by
  have h := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hP) (0 : R)
  rw [fwdDiff_iter_eq_sum_shift] at h
  rw [dd_eq_sum]
  simpa using h

lemma dd_mul_id (m : ℕ) (f : ℕ → R) :
    dd (m + 1) (fun s => (s : R) * f s) = (m + 1) * (dd m f + dd (m + 1) f) := by
  have key : ∀ (m : ℕ) (f : ℕ → R),
      ((fwdDiff (1:ℕ))^[m + 1] (fun s : ℕ => (s : R) * f s)) 0 = (m + 1) * ((fwdDiff (1:ℕ))^[m] f) 1 := by
    intro m
    induction m with
    | zero => intro f; simp [fwdDiff]
    | succ m ih =>
      intro f
      have h1 : fwdDiff (1:ℕ) (fun s : ℕ => (s : R) * f s)
          = (fun s : ℕ => (s : R) * (fwdDiff (1:ℕ) f) s) + (fun s => f (s + 1)) := by
        ext s; simp [fwdDiff]; ring
      rw [iterate_succ_apply, h1, fwdDiff_iter_add, Pi.add_apply, ih (fwdDiff (1:ℕ) f),
        fwdDiff_iter_comp_add, ← iterate_succ_apply (fwdDiff (1:ℕ)) (m) f]
      push_cast; ring
  unfold dd
  rw [key, iterate_succ_apply' (fwdDiff (1:ℕ)) m f]
  simp [fwdDiff]

end basic

/-- cast compatibility -/
lemma dd_cast (m : ℕ) (f : ℕ → ℤ) : ((dd m f : ℤ) : ℚ) = dd m (fun s => (f s : ℚ)) := by
  simp only [dd_eq_sum]
  push_cast
  refine sum_congr rfl fun k _ => ?_
  simp [zsmul_eq_mul]

/-- sequences whose m-th difference at 0 is divisible by m! -/
def Good (f : ℕ → ℤ) : Prop := ∀ m, (m ! : ℤ) ∣ dd m f

lemma good_const (c : ℤ) : Good (fun _ => c) := by
  intro m
  rcases m with _ | m
  · simp
  · have : dd (m + 1) (fun _ : ℕ => c) = 0 := by
      have := dd_poly_eq_zero (Polynomial.C c) (m := m + 1) (by simp)
      simpa using this
    rw [this]; exact dvd_zero _

lemma good_add {f g : ℕ → ℤ} (hf : Good f) (hg : Good g) : Good (fun s => f s + g s) := by
  intro m; rw [dd_add]; exact dvd_add (hf m) (hg m)

lemma good_const_mul (c : ℤ) {f : ℕ → ℤ} (hf : Good f) : Good (fun s => c * f s) := by
  intro m; rw [dd_const_mul]; exact Dvd.dvd.mul_left (hf m) c

lemma good_id_mul {f : ℕ → ℤ} (hf : Good f) : Good (fun s => (s : ℤ) * f s) := by
  intro m
  rcases m with _ | m
  · simp
  · rw [dd_mul_id, Nat.factorial_succ]
    push_cast
    apply mul_dvd_mul_left
    exact dvd_add (hf m) (Dvd.dvd.trans (by exact_mod_cast (Nat.factorial_dvd_factorial (Nat.le_succ m))) (hf (m + 1)))

lemma good_poly (P : ℤ[X]) : Good (fun s : ℕ => P.eval (s : ℤ)) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simpa using good_add hp hq
  | monomial n c =>
    induction n with
    | zero => simpa using good_const c
    | succ n ih =>
      have := good_id_mul ih
      refine fun m => ?_
      have h2 : (fun s : ℕ => (Polynomial.monomial (n + 1) c).eval (s : ℤ))
          = (fun s : ℕ => (s : ℤ) * (Polynomial.monomial n c).eval (s : ℤ)) := by
        ext s; simp [pow_succ]; ring
      rw [h2]; exact this m

/- ### coefficient sequences -/

def ch : ℕ → ℤ
  | 0 => 1
  | 1 => -2
  | 2 => 4
  | (m + 3) => -2 * ch (m + 2) + 2 * ch m

def hh : ℕ → ℤ
  | 0 => 1
  | (m + 1) => ch (m + 1) + ch m

def rr : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (m + 2) => ch (m + 1) + 2 * ch m

lemma hh_succ (j : ℕ) : hh (j + 1) = rr j - hh j := by
  rcases j with _ | _ | j
  · simp [hh, rr, ch]
  · simp [hh, rr, ch]
  · simp only [hh, rr, ch]; ring

lemma rr_succ (j : ℕ) : rr (j + 2) = hh (j + 1) + 2 * hh j - rr (j + 1) := by
  rcases j with _ | j
  · simp [hh, rr, ch]
  · simp only [hh, rr]; ring

noncomputable def hq (m : ℕ) : ℚ := (hh m : ℚ) / 2 ^ m
noncomputable def rq (m : ℕ) : ℚ := (rr m : ℚ) / 2 ^ m

lemma hq_succ (j : ℕ) : 2 * hq (j + 1) = rq j - hq j := by
  unfold hq rq
  rw [hh_succ]; push_cast; field_simp; ring

lemma rq_succ (j : ℕ) : 2 * rq (j + 2) = hq (j + 1) + hq j - rq (j + 1) := by
  unfold hq rq
  rw [rr_succ]; push_cast; field_simp; ring

lemma hq_zero : hq 0 = 1 := by simp [hq, hh]
lemma rq_zero : rq 0 = 0 := by simp [rq, rr]
lemma hq_one : hq 1 = -1 / 2 := by norm_num [hq, hh, ch]
lemma rq_one : rq 1 = 1 / 2 := by simp [rq, rr]

/-- the telescoping identity behind `L(Φ g) = 2 g(1)` -/
lemma telescope (u v : ℕ → ℚ) (N : ℕ) :
    ∑ m ∈ range (N + 1), (hq m * (2 * u m + u (m + 1) - v (m + 1) - v (m + 2))
        + rq m * (2 * v m + v (m + 1) - u (m + 1)))
      = 2 * u 0 - 2 * hq (N + 1) * u (N + 1) - 2 * rq (N + 1) * v (N + 1) - hq N * v (N + 2) := by
  induction N with
  | zero =>
    simp only [zero_add, sum_range_one, hq_zero, rq_zero, hq_one, rq_one]; ring
  | succ N ih =>
    rw [sum_range_succ, ih]
    have h1 := hq_succ (N + 1)
    have h2 := rq_succ N
    linear_combination (u (N + 2)) * h1 + (v (N + 2)) * h2

/- ### the sequences `s ↦ (2s+c)^n` -/

noncomputable def pw (n : ℕ) (c : ℚ) : ℕ → ℚ := fun s => (2 * (s : ℚ) + c) ^ n

lemma pw_shift (n : ℕ) (c : ℚ) (s : ℕ) : pw n (c + 2) s = pw n c (s + 1) := by
  unfold pw; push_cast; ring

lemma dd_pw_shift (n m : ℕ) (c : ℚ) :
    dd m (pw n (c + 2)) = dd m (pw n c) + dd (m + 1) (pw n c) := by
  rw [← dd_shift]; exact dd_congr m (pw_shift n c)

lemma dd_pw_eq_zero (n m : ℕ) (c : ℚ) (h : n < m) : dd m (pw n c) = 0 := by
  have hdeg : ((Polynomial.C (2:ℚ) * Polynomial.X + Polynomial.C c) ^ n).natDegree < m := by
    refine lt_of_le_of_lt (Polynomial.natDegree_pow_le) ?_
    have : (Polynomial.C (2:ℚ) * Polynomial.X + Polynomial.C c).natDegree ≤ 1 :=
      Polynomial.natDegree_linear_le
    calc n * _ ≤ n * 1 := Nat.mul_le_mul_left n this
      _ < m := by simpa using h
  have := dd_poly_eq_zero ((Polynomial.C (2:ℚ) * Polynomial.X + Polynomial.C c) ^ n) hdeg
  rw [← this]
  exact dd_congr m (fun s => by simp [pw])

/-- the candidate closed form, truncated at `N` -/
noncomputable def bN (N j : ℕ) : ℚ :=
  ∑ m ∈ range (N + 1), (hq m * dd m (pw j 1) + rq m * dd m (pw j 0))

lemma bN_eq (N j : ℕ) (h : j ≤ N) : bN N j = bN j j := by
  unfold bN
  have hsub : range (j + 1) ⊆ range (N + 1) := range_subset_range.2 (by omega)
  symm
  apply sum_subset hsub
  intro m hm hm'
  have : j < m := by
    simp only [mem_range] at hm hm'; omega
  rw [dd_pw_eq_zero j m 1 this, dd_pw_eq_zero j m 0 this]; ring

/-- binomial identity -/
lemma binom_id (n : ℕ) (x : ℚ) :
    ∑ j ∈ range (n + 1), (n.choose j : ℚ) * (1 - (-1 : ℚ) ^ j - (-2 : ℚ) ^ j) * x ^ (n - j)
      = (x + 1) ^ n - (x - 1) ^ n - (x - 2) ^ n := by
  have e1 : (x + 1) ^ n = ∑ j ∈ range (n + 1), (1:ℚ) ^ j * x ^ (n - j) * (n.choose j : ℚ) := by
    rw [add_comm, add_pow]
  have e2 : (x - 1) ^ n = ∑ j ∈ range (n + 1), (-1:ℚ) ^ j * x ^ (n - j) * (n.choose j : ℚ) := by
    rw [sub_eq_add_neg, add_comm, add_pow]
  have e3 : (x - 2) ^ n = ∑ j ∈ range (n + 1), (-2:ℚ) ^ j * x ^ (n - j) * (n.choose j : ℚ) := by
    rw [sub_eq_add_neg, add_comm, add_pow]
  rw [e1, e2, e3, ← sum_sub_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  ring

lemma a_zero : a 0 = 1 := by
  rw [a]

lemma a_succ (m : ℕ) :
    a (m + 1) = (-1 : ℚ) ^ (m + 1) + (1 / 2) * ∑ k ∈ range (m + 1),
      ((m + 1).choose (k + 1) : ℚ) * (1 - (-1 : ℚ) ^ (k + 1) - (-2 : ℚ) ^ (k + 1))
        * a (m + 1 - (k + 1)) := by
  rw [a]

lemma dd_binom (n m : ℕ) (c : ℚ) :
    ∑ j ∈ range (n + 1), (n.choose j : ℚ) * (1 - (-1 : ℚ) ^ j - (-2 : ℚ) ^ j) * dd m (pw (n - j) c)
      = dd m (pw n (c + 1)) - dd m (pw n (c - 1)) - dd m (pw n (c - 2)) := by
  have h1 : dd m (pw n (c + 1)) - dd m (pw n (c - 1)) - dd m (pw n (c - 2))
      = dd m (fun s => pw n (c + 1) s - pw n (c - 1) s - pw n (c - 2) s) := by
    rw [dd_sub, dd_sub]
  rw [h1]
  have h2 : ∀ s : ℕ, pw n (c + 1) s - pw n (c - 1) s - pw n (c - 2) s
      = ∑ j ∈ range (n + 1), (n.choose j : ℚ) * (1 - (-1 : ℚ) ^ j - (-2 : ℚ) ^ j) * pw (n - j) c s := by
    intro s
    have := binom_id n (2 * (s : ℚ) + c)
    simp only [pw]
    rw [this]; ring
  rw [dd_congr m h2, dd_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [dd_const_mul]

lemma F_eq (n N : ℕ) :
    ∑ j ∈ range (n + 1), (n.choose j : ℚ) * (1 - (-1 : ℚ) ^ j - (-2 : ℚ) ^ j) * bN N (n - j)
      = ∑ m ∈ range (N + 1), (hq m * (dd m (pw n 2) - dd m (pw n 0) - dd m (pw n (-1)))
          + rq m * (dd m (pw n 1) - dd m (pw n (-1)) - dd m (pw n (-2)))) := by
  unfold bN
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun m _ => ?_
  have hA := dd_binom n m 1
  have hB := dd_binom n m 0
  norm_num at hA hB
  rw [← hA, ← hB, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  ring

lemma key_id (n : ℕ) :
    ∑ m ∈ range (n + 1), (hq m * (dd m (pw n 1) - dd m (pw n 2) + dd m (pw n 0) + dd m (pw n (-1)))
          + rq m * (dd m (pw n 0) - dd m (pw n 1) + dd m (pw n (-1)) + dd m (pw n (-2))))
      = 2 * (-1 : ℚ) ^ n := by
  have e0 : ∀ m, dd m (pw n 0) = dd m (pw n (-2)) + dd (m + 1) (pw n (-2)) := by
    intro m; have := dd_pw_shift n m (-2); norm_num at this; exact this
  have e1 : ∀ m, dd m (pw n 1) = dd m (pw n (-1)) + dd (m + 1) (pw n (-1)) := by
    intro m; have := dd_pw_shift n m (-1); norm_num at this; exact this
  have e2 : ∀ m, dd m (pw n 2) = dd m (pw n 0) + dd (m + 1) (pw n 0) := by
    intro m; have := dd_pw_shift n m 0; norm_num at this; exact this
  have ht := telescope (fun m => dd m (pw n (-1))) (fun m => dd m (pw n (-2))) n
  simp only [] at ht
  rw [dd_pw_eq_zero n (n + 1) (-1) (by omega), dd_pw_eq_zero n (n + 1) (-2) (by omega),
    dd_pw_eq_zero n (n + 2) (-2) (by omega)] at ht
  have hu0 : dd 0 (pw n (-1)) = (-1 : ℚ) ^ n := by
    rw [dd_zero]; simp [pw]
  rw [hu0] at ht
  rw [← (by simpa using ht : _ = 2 * (-1 : ℚ) ^ n)]
  refine sum_congr rfl fun m _ => ?_
  rw [e2 m, e1 m, e0 m, e0 (m + 1)]
  ring

theorem a_eq (n : ℕ) : a n = bN n n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | m
    · simp [a_zero, bN, hq_zero, rq_zero, dd_zero, pw]
    · rw [a_succ]
      have hS : ∑ k ∈ range (m + 1),
          ((m + 1).choose (k + 1) : ℚ) * (1 - (-1 : ℚ) ^ (k + 1) - (-2 : ℚ) ^ (k + 1))
            * a (m + 1 - (k + 1))
          = ∑ k ∈ range (m + 1),
          ((m + 1).choose (k + 1) : ℚ) * (1 - (-1 : ℚ) ^ (k + 1) - (-2 : ℚ) ^ (k + 1))
            * bN (m + 1) (m + 1 - (k + 1)) := by
        refine sum_congr rfl fun k hk => ?_
        rw [ih (m + 1 - (k + 1)) (by omega), bN_eq (m + 1) (m + 1 - (k + 1)) (by omega)]
      rw [hS]
      have hF := F_eq (m + 1) (m + 1)
      rw [sum_range_succ'] at hF
      have hK := key_id (m + 1)
      have hsplit : ∑ m_1 ∈ range (m + 1 + 1),
          (hq m_1 * (dd m_1 (pw (m + 1) 1) - dd m_1 (pw (m + 1) 2) + dd m_1 (pw (m + 1) 0) + dd m_1 (pw (m + 1) (-1)))
          + rq m_1 * (dd m_1 (pw (m + 1) 0) - dd m_1 (pw (m + 1) 1) + dd m_1 (pw (m + 1) (-1)) + dd m_1 (pw (m + 1) (-2))))
          = bN (m + 1) (m + 1) - ∑ m_1 ∈ range (m + 1 + 1),
            (hq m_1 * (dd m_1 (pw (m + 1) 2) - dd m_1 (pw (m + 1) 0) - dd m_1 (pw (m + 1) (-1)))
          + rq m_1 * (dd m_1 (pw (m + 1) 1) - dd m_1 (pw (m + 1) (-1)) - dd m_1 (pw (m + 1) (-2)))) := by
        unfold bN
        rw [← sum_sub_distrib]
        refine sum_congr rfl fun j _ => ?_
        ring
      rw [hsplit, ← hF] at hK
      simp only [Nat.choose_zero_right, pow_zero, Nat.sub_zero, Nat.cast_one] at hK
      linarith

/- ### 2-adic invariants of the coefficient sequences -/

lemma K_inv (m : ℕ) :
    (∃ x : ℤ, 2 * ((m ! : ℤ) * ch m) = 2 ^ m * x) ∧
    (Even m → ∃ y : ℤ, (m ! : ℤ) * ch m = 2 ^ m * y) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | _ | _ | m
    · exact ⟨⟨2, by simp [ch]⟩, fun _ => ⟨1, by simp [ch]⟩⟩
    · exact ⟨⟨-2, by simp [ch]⟩, fun h => absurd h (by decide)⟩
    · exact ⟨⟨4, by simp [ch, Nat.factorial]⟩, fun _ => ⟨2, by simp [ch, Nat.factorial]⟩⟩
    · have ih0 := ih m (by omega)
      have ih2 := ih (m + 2) (by omega)
      have hfac : ((m + 3) ! : ℤ) * ch (m + 3)
          = -2 * ((m : ℤ) + 3) * (((m + 2) ! : ℤ) * ch (m + 2))
            + 2 * ((m : ℤ) + 3) * ((m : ℤ) + 2) * ((m : ℤ) + 1) * ((m ! : ℤ) * ch m) := by
        have f3 : ((m + 3) ! : ℤ) = ((m : ℤ) + 3) * ((m + 2) ! : ℤ) := by
          rw [Nat.factorial_succ]; push_cast; ring
        have f2 : ((m + 2) ! : ℤ) = ((m : ℤ) + 2) * (((m : ℤ) + 1) * (m ! : ℤ)) := by
          rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
        have hc : ch (m + 3) = -2 * ch (m + 2) + 2 * ch m := by simp [ch]
        rw [f3, hc]
        have : ((m : ℤ) + 3) * ((m + 2) ! : ℤ) * (-2 * ch (m + 2) + 2 * ch m)
            = -2 * ((m : ℤ) + 3) * (((m + 2) ! : ℤ) * ch (m + 2))
              + 2 * ((m : ℤ) + 3) * (((m + 2) ! : ℤ) * ch m) := by ring
        rw [this, f2]; ring
      rcases Nat.even_or_odd' m with ⟨t, rfl | rfl⟩
      · -- m = 2t
        obtain ⟨y0, hy0⟩ := ih0.2 ⟨t, by ring⟩
        obtain ⟨y2, hy2⟩ := ih2.2 ⟨t + 1, by ring⟩
        refine ⟨⟨-2 * ((2 * t : ℕ) + 3 : ℤ) * y2 + ((2 * t : ℕ) + 3 : ℤ) * ((t : ℤ) + 1) * ((2 * t : ℕ) + 1 : ℤ) * y0, ?_⟩, ?_⟩
        · rw [hfac, hy0, hy2]; push_cast; ring
        · intro h; exfalso
          rw [Nat.even_iff] at h; omega
      · -- m = 2t+1
        obtain ⟨x0, hx0⟩ := ih0.1
        obtain ⟨x2, hx2⟩ := ih2.1
        obtain ⟨w, hw⟩ : ∃ w : ℤ, ((t : ℤ) + 1) * ((t : ℤ) + 2) = 2 * w := by
          have := Int.even_mul_succ_self ((t : ℤ) + 1)
          obtain ⟨w, hw⟩ := this
          exact ⟨w, by rw [show ((t : ℤ) + 2) = (t : ℤ) + 1 + 1 by ring, hw]; ring⟩
        refine ⟨⟨-((2 * t + 1 : ℕ) + 3 : ℤ) * x2 + ((t : ℤ) + 2) * ((2 * t + 1 : ℕ) + 2 : ℤ) * ((t : ℤ) + 1) * x0, ?_⟩, ?_⟩
        · rw [hfac]
          have e1 : -2 * (((2 * t + 1 : ℕ) : ℤ) + 3) * (((2 * t + 1 + 2) ! : ℤ) * ch (2 * t + 1 + 2))
              = -(((2 * t + 1 : ℕ) : ℤ) + 3) * (2 * (((2 * t + 1 + 2) ! : ℤ) * ch (2 * t + 1 + 2))) := by ring
          have e2 : 2 * (((2 * t + 1 : ℕ) : ℤ) + 3) * (((2 * t + 1 : ℕ) : ℤ) + 2) * (((2 * t + 1 : ℕ) : ℤ) + 1) * (((2 * t + 1) ! : ℤ) * ch (2 * t + 1))
              = (((2 * t + 1 : ℕ) : ℤ) + 3) * (((2 * t + 1 : ℕ) : ℤ) + 2) * (((2 * t + 1 : ℕ) : ℤ) + 1) * (2 * (((2 * t + 1) ! : ℤ) * ch (2 * t + 1))) := by ring
          rw [mul_add, e1, e2]
          rw [hx0, hx2]; push_cast; ring
        · intro _
          refine ⟨-((t : ℤ) + 2) * x2 + ((2 * t + 1 : ℕ) + 2 : ℤ) * w * x0, ?_⟩
          rw [hfac]
          have e1 : -2 * (((2 * t + 1 : ℕ) : ℤ) + 3) * (((2 * t + 1 + 2) ! : ℤ) * ch (2 * t + 1 + 2))
              = -(((2 * t + 1 : ℕ) : ℤ) + 3) * (2 * (((2 * t + 1 + 2) ! : ℤ) * ch (2 * t + 1 + 2))) := by ring
          have e2 : 2 * (((2 * t + 1 : ℕ) : ℤ) + 3) * (((2 * t + 1 : ℕ) : ℤ) + 2) * (((2 * t + 1 : ℕ) : ℤ) + 1) * (((2 * t + 1) ! : ℤ) * ch (2 * t + 1))
              = (((2 * t + 1 : ℕ) : ℤ) + 3) * (((2 * t + 1 : ℕ) : ℤ) + 2) * (((2 * t + 1 : ℕ) : ℤ) + 1) * (2 * (((2 * t + 1) ! : ℤ) * ch (2 * t + 1))) := by ring
          rw [e1, e2, hx0, hx2]
          have e3 : (((2 * t + 1 : ℕ) : ℤ) + 3) * (((2 * t + 1 : ℕ) : ℤ) + 2) * (((2 * t + 1 : ℕ) : ℤ) + 1) * (2 ^ (2 * t + 1) * x0)
              = 4 * (((t : ℤ) + 1) * ((t : ℤ) + 2)) * (((2 * t + 1 : ℕ) : ℤ) + 2) * (2 ^ (2 * t + 1) * x0) := by
            push_cast; ring
          rw [e3, hw]; push_cast; ring

lemma hh_div (m : ℕ) : ∃ x : ℤ, 2 * ((m ! : ℤ) * hh m) = 2 ^ m * x := by
  rcases m with _ | j
  · exact ⟨2, by simp [hh]⟩
  · obtain ⟨x1, hx1⟩ := (K_inv (j + 1)).1
    have hexp : 2 * (((j + 1) ! : ℤ) * hh (j + 1))
        = 2 * (((j + 1) ! : ℤ) * ch (j + 1)) + ((j : ℤ) + 1) * (2 * ((j ! : ℤ) * ch j)) := by
      rw [Nat.factorial_succ]; simp only [hh]; push_cast; ring
    rcases Nat.even_or_odd' j with ⟨t, rfl | rfl⟩
    · obtain ⟨y, hy⟩ := (K_inv (2 * t)).2 ⟨t, by ring⟩
      refine ⟨x1 + ((2 * t : ℕ) + 1 : ℤ) * y, ?_⟩
      rw [hexp, hx1, hy]; push_cast; ring
    · obtain ⟨x0, hx0⟩ := (K_inv (2 * t + 1)).1
      refine ⟨x1 + ((t : ℤ) + 1) * x0, ?_⟩
      rw [hexp, hx1, hx0]; push_cast; ring

lemma rr_div (m : ℕ) : ∃ y : ℤ, 4 * ((m ! : ℤ) * rr m) = 2 ^ m * y := by
  rcases m with _ | _ | j
  · exact ⟨0, by simp [rr]⟩
  · exact ⟨2, by simp [rr]⟩
  · obtain ⟨x1, hx1⟩ := (K_inv (j + 1)).1
    obtain ⟨x0, hx0⟩ := (K_inv j).1
    refine ⟨((j : ℤ) + 2) * x1 + ((j : ℤ) + 2) * ((j : ℤ) + 1) * x0, ?_⟩
    have hexp : 4 * (((j + 2) ! : ℤ) * rr (j + 2))
        = 2 * ((j : ℤ) + 2) * (2 * (((j + 1) ! : ℤ) * ch (j + 1)))
          + 4 * ((j : ℤ) + 2) * ((j : ℤ) + 1) * (2 * ((j ! : ℤ) * ch j)) := by
      rw [Nat.factorial_succ (j + 1), Nat.factorial_succ j]; simp only [rr]; push_cast; ring
    rw [hexp, hx1, hx0]; ring

lemma hh_div_small (m : ℕ) (h : m < 3) : ∃ x : ℤ, 2 * hh m = 2 ^ m * x := by
  interval_cases m
  · exact ⟨2, by simp [hh]⟩
  · exact ⟨-1, by simp [hh, ch]⟩
  · exact ⟨1, by simp [hh, ch]⟩

/- ### structure of `(2X+1)^P` modulo high powers of two -/

/-- `Y = 1 + 2^(e+1) (γ X(X+1) + 2R)` -/
def QP (e : ℕ) (Y : ℤ[X]) : Prop :=
  ∃ (γ : ℤ) (R : ℤ[X]), Y = 1 + 2 ^ (e + 1) * (C γ * (X * (X + 1)) + 2 * R)

lemma QP_one (e : ℕ) : QP e 1 := ⟨0, 0, by simp⟩

lemma QP_mul {e : ℕ} {Y Z : ℤ[X]} (hY : QP e Y) (hZ : QP e Z) : QP e (Y * Z) := by
  obtain ⟨γ1, R1, rfl⟩ := hY
  obtain ⟨γ2, R2, rfl⟩ := hZ
  refine ⟨γ1 + γ2, R1 + R2 + 2 ^ e * ((C γ1 * (X * (X + 1)) + 2 * R1) * (C γ2 * (X * (X + 1)) + 2 * R2)), ?_⟩
  rw [C_add]; ring

lemma QP_pow {e : ℕ} {Y : ℤ[X]} (hY : QP e Y) (u : ℕ) : QP e (Y ^ u) := by
  induction u with
  | zero => simpa using QP_one e
  | succ u ih => rw [pow_succ]; exact QP_mul ih hY

lemma QP_sq {e : ℕ} {Y : ℤ[X]} (hY : QP (e + 1) Y) : QP (e + 2) (Y ^ 2) := by
  obtain ⟨γ, R, rfl⟩ := hY
  refine ⟨γ, R + 2 ^ e * (C γ * (X * (X + 1)) + 2 * R) ^ 2, ?_⟩
  ring

lemma QP_base (e : ℕ) : QP (e + 1) ((2 * X + 1 : ℤ[X]) ^ (2 ^ (e + 1))) := by
  induction e with
  | zero => exact ⟨1, 0, by simp; ring⟩
  | succ e ih =>
    have := QP_sq ih
    rw [← pow_mul, ← pow_succ] at this
    exact this

lemma QP_main (e P : ℕ) (h : 2 ^ (e + 1) ∣ P) : QP (e + 1) ((2 * X + 1 : ℤ[X]) ^ P) := by
  obtain ⟨u, rfl⟩ := h
  rw [pow_mul]
  exact QP_pow (QP_base e) u

lemma pow_form (n : ℕ) : ∃ Q : ℤ[X], (2 * X + 1 : ℤ[X]) ^ n = 1 + 2 * X * Q := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨Q, hQ⟩ := ih
    exact ⟨1 + Q * (2 * X + 1), by rw [pow_succ, hQ]; ring⟩

/-- the sequence `s(s+1)` -/
def ss : ℕ → ℤ := fun s => (s : ℤ) * ((s : ℤ) + 1)

lemma dd_ss_zero (m : ℕ) (h : 3 ≤ m) : dd m ss = 0 := by
  have hdeg : (X * (X + 1) : ℤ[X]).natDegree < m := by
    have : (X * (X + 1) : ℤ[X]).natDegree ≤ 2 := by compute_degree
    omega
  have := dd_poly_eq_zero (X * (X + 1) : ℤ[X]) hdeg
  rw [← this]; exact dd_congr m (fun s => by simp [ss])

lemma dd_ss_even (m : ℕ) : ∃ w : ℤ, dd m ss = 2 * w := by
  rcases m with _ | _ | _ | m
  · exact ⟨0, by simp [dd_eq_sum, ss]⟩
  · exact ⟨1, by simp [dd_eq_sum, ss, sum_range_succ]⟩
  · exact ⟨1, by simp [dd_eq_sum, ss, sum_range_succ]⟩
  · exact ⟨0, by rw [dd_ss_zero _ (by omega)]; simp⟩

/-- odd part: the differences `(2s+1)^(n+P) - (2s+1)^n` -/
lemma odd_struct (e P : ℕ) (h : 2 ^ (e + 1) ∣ P) (n m : ℕ) :
    ∃ z : ℤ, dd m (fun s : ℕ => (2 * (s : ℤ) + 1) ^ (n + P) - (2 * (s : ℤ) + 1) ^ n)
      = 2 ^ (e + 3) * ((if 3 ≤ m then (m ! : ℤ) else 1) * z) := by
  obtain ⟨γ, R, hR⟩ := QP_main e P h
  obtain ⟨Q, hQ⟩ := pow_form n
  -- pointwise decomposition
  have hpt : ∀ s : ℕ, (2 * (s : ℤ) + 1) ^ (n + P) - (2 * (s : ℤ) + 1) ^ n
      = 2 ^ (e + 2) * γ * ss s
        + 2 ^ (e + 3) * (C γ * X ^ 2 * (X + 1) * Q + (2 * X + 1) ^ n * R : ℤ[X]).eval (s : ℤ) := by
    intro s
    have h1 := congrArg (Polynomial.eval (s : ℤ)) hR
    have h2 := congrArg (Polynomial.eval (s : ℤ)) hQ
    simp only [eval_pow, eval_add, eval_mul, eval_ofNat, eval_X, eval_one, eval_C] at h1 h2
    simp only [eval_pow, eval_add, eval_mul, eval_ofNat, eval_X, eval_one, eval_C, ss]
    rw [pow_add, h1]
    have h2' := h2
    generalize (2 * (s : ℤ) + 1) ^ n = y at h2 ⊢
    -- y = 1 + 2 s q
    have : y * (1 + 2 ^ (e + 1 + 1) * (γ * ((s : ℤ) * ((s : ℤ) + 1)) + 2 * eval (↑s) R)) - y
        = 2 ^ (e + 2) * γ * ((s : ℤ) * ((s : ℤ) + 1)) * y + 2 ^ (e + 3) * (y * eval (↑s) R) := by ring
    rw [this]
    have : 2 ^ (e + 2) * γ * ((s : ℤ) * ((s : ℤ) + 1)) * y
        = 2 ^ (e + 2) * γ * ((s : ℤ) * ((s : ℤ) + 1)) + 2 ^ (e + 3) * (γ * (s : ℤ) ^ 2 * ((s : ℤ) + 1) * eval (↑s) Q) := by
      rw [h2]; ring
    rw [this]; ring
  rw [dd_congr m hpt, dd_add, dd_const_mul, dd_const_mul]
  obtain ⟨z, hz⟩ := good_poly (C γ * X ^ 2 * (X + 1) * Q + (2 * X + 1) ^ n * R : ℤ[X]) m
  obtain ⟨w, hw⟩ := dd_ss_even m
  have hss : dd m (fun s => ss s) = dd m ss := rfl
  rw [hss, hz]
  by_cases h3 : 3 ≤ m
  · rw [if_pos h3, dd_ss_zero m h3]
    exact ⟨z, by ring⟩
  · rw [if_neg h3, hw]
    exact ⟨γ * w + (m ! : ℤ) * z, by ring⟩

/- ### integer versions of the difference sequences -/

def Uz (n m : ℕ) : ℤ := dd m (fun s : ℕ => (2 * (s : ℤ) + 1) ^ n)
def Vz (n m : ℕ) : ℤ := dd m (fun s : ℕ => (2 * (s : ℤ)) ^ n)

lemma Uz_cast (n m : ℕ) : ((Uz n m : ℤ) : ℚ) = dd m (pw n 1) := by
  unfold Uz; rw [dd_cast]; exact dd_congr m (fun s => by simp [pw])

lemma Vz_cast (n m : ℕ) : ((Vz n m : ℤ) : ℚ) = dd m (pw n 0) := by
  unfold Vz; rw [dd_cast]; exact dd_congr m (fun s => by simp [pw])

/-- integer numerator of the m-th term -/
def Tm (n m : ℕ) : ℤ := hh m * Uz n m + rr m * Vz n m

lemma a_eq_sum (n N : ℕ) (h : n ≤ N) :
    a n = ∑ m ∈ range (N + 1), ((Tm n m : ℤ) : ℚ) / 2 ^ m := by
  rw [a_eq, ← bN_eq N n h]
  unfold bN
  refine sum_congr rfl fun m _ => ?_
  rw [← Uz_cast, ← Vz_cast]
  unfold hq rq Tm
  push_cast; ring

lemma Vz_div (n m : ℕ) : ∃ z : ℤ, Vz n m = 2 ^ n * ((m ! : ℤ) * z) := by
  obtain ⟨z, hz⟩ := good_poly (X ^ n : ℤ[X]) m
  refine ⟨z, ?_⟩
  unfold Vz
  have : ∀ s : ℕ, (2 * (s : ℤ)) ^ n = 2 ^ n * (X ^ n : ℤ[X]).eval (s : ℤ) := by
    intro s; simp [mul_pow]
  rw [dd_congr m this, dd_const_mul, hz]

lemma term_even (a' n m : ℕ) (hn : a' + 2 ≤ n) : ∃ z : ℤ, rr m * Vz n m = 2 ^ (m + a') * z := by
  obtain ⟨y, hy⟩ := rr_div m
  obtain ⟨z, hz⟩ := Vz_div n m
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
  refine ⟨2 ^ t * z * y, ?_⟩
  rw [hz]
  have : rr m * (2 ^ (a' + 2 + t) * ((m ! : ℤ) * z)) = 2 ^ a' * 2 ^ t * z * (4 * ((m ! : ℤ) * rr m)) := by ring
  rw [this, hy]; ring

lemma Uz_sub (n P m : ℕ) : Uz (n + P) m - Uz n m
    = dd m (fun s : ℕ => (2 * (s : ℤ) + 1) ^ (n + P) - (2 * (s : ℤ) + 1) ^ n) := by
  unfold Uz; rw [dd_sub]

lemma odd_struct' (a' P : ℕ) (ha : 1 ≤ a') (hP2 : 2 ∣ P) (hP : 2 ^ (a' - 1) ∣ P) (n m : ℕ) :
    ∃ z : ℤ, Uz (n + P) m - Uz n m = 2 ^ (a' + 1) * ((if 3 ≤ m then (m ! : ℤ) else 1) * z) := by
  rw [Uz_sub]
  rcases a' with _ | _ | a''
  · omega
  · obtain ⟨z, hz⟩ := odd_struct 0 P (by simpa using hP2) n m
    exact ⟨2 * z, by rw [hz]; ring⟩
  · obtain ⟨z, hz⟩ := odd_struct a'' P (by simpa using hP) n m
    exact ⟨z, by rw [hz]⟩

lemma term_odd (a' P : ℕ) (ha : 1 ≤ a') (hP2 : 2 ∣ P) (hP : 2 ^ (a' - 1) ∣ P) (n m : ℕ) :
    ∃ z : ℤ, hh m * (Uz (n + P) m - Uz n m) = 2 ^ (m + a') * z := by
  obtain ⟨z, hz⟩ := odd_struct' a' P ha hP2 hP n m
  rw [hz]
  by_cases h3 : 3 ≤ m
  · rw [if_pos h3]
    obtain ⟨x, hx⟩ := hh_div m
    refine ⟨z * x, ?_⟩
    have : hh m * (2 ^ (a' + 1) * ((m ! : ℤ) * z)) = 2 ^ a' * z * (2 * ((m ! : ℤ) * hh m)) := by ring
    rw [this, hx]; ring
  · rw [if_neg h3]
    obtain ⟨x, hx⟩ := hh_div_small m (by omega)
    refine ⟨z * x, ?_⟩
    have : hh m * (2 ^ (a' + 1) * (1 * z)) = 2 ^ a' * z * (2 * hh m) := by ring
    rw [this, hx]; ring

/-- the 2-part of the congruence -/
lemma two_part (a' P n : ℕ) (ha : 1 ≤ a') (hP2 : 2 ∣ P) (hP : 2 ^ (a' - 1) ∣ P)
    (hn : a' + 2 ≤ n) : ∃ Z : ℤ, a (n + P) - a n = 2 ^ a' * (Z : ℚ) := by
  have hterm : ∀ m : ℕ, ∃ z : ℤ, Tm (n + P) m - Tm n m = 2 ^ (m + a') * z := by
    intro m
    obtain ⟨z1, h1⟩ := term_odd a' P ha hP2 hP n m
    obtain ⟨z2, h2⟩ := term_even a' (n + P) m (by omega)
    obtain ⟨z3, h3⟩ := term_even a' n m hn
    refine ⟨z1 + z2 - z3, ?_⟩
    unfold Tm
    have : hh m * Uz (n + P) m + rr m * Vz (n + P) m - (hh m * Uz n m + rr m * Vz n m)
        = hh m * (Uz (n + P) m - Uz n m) + rr m * Vz (n + P) m - rr m * Vz n m := by ring
    rw [this, h1, h2, h3]; ring
  choose z hz using hterm
  refine ⟨∑ m ∈ range (n + P + 1), z m, ?_⟩
  rw [a_eq_sum (n + P) (n + P) le_rfl, a_eq_sum n (n + P) (by omega), ← sum_sub_distrib]
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun m _ => ?_
  have h := congrArg (fun x : ℤ => (x : ℚ)) (hz m)
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at h
  rw [← sub_div, h, pow_add]
  field_simp

/- ### the odd part -/

lemma pow_per (k' i n P : ℕ) (hk : 0 < k') (hP : φ k' ∣ P) (hn : k' ≤ n) :
    (k' : ℤ) ∣ (i : ℤ) ^ (n + P) - (i : ℤ) ^ n := by
  have hX : (i : ℤ) ^ (n + P) - (i : ℤ) ^ n = (i : ℤ) ^ n * ((i : ℤ) ^ P - 1) := by ring
  rw [hX, Int.natCast_dvd, Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p e hp hpe
  rw [← Int.natCast_dvd]
  by_cases hpi : p ∣ i
  · apply Dvd.dvd.mul_right
    have he : e ≤ n := by
      have h1 : e < p ^ e := Nat.lt_pow_self hp.one_lt
      have h2 : p ^ e ≤ k' := Nat.le_of_dvd hk hpe
      omega
    have : (p ^ e : ℕ) ∣ i ^ n := (pow_dvd_pow_of_dvd hpi e).trans (pow_dvd_pow i he)
    exact_mod_cast this
  · apply Dvd.dvd.mul_left
    have hcop : Nat.Coprime i (p ^ e) :=
      Nat.Coprime.pow_right e ((Nat.Prime.coprime_iff_not_dvd hp).2 hpi).symm
    have h1 := Nat.ModEq.pow_totient hcop
    obtain ⟨t, ht⟩ := (Nat.totient_dvd_of_dvd hpe).trans hP
    have h2 : i ^ P ≡ 1 [MOD p ^ e] := by
      rw [ht, pow_mul]
      simpa using h1.pow t
    have h3 := (Nat.modEq_iff_dvd.1 h2.symm)
    simpa using h3

lemma dvd_dd (c : ℤ) (f : ℕ → ℤ) (h : ∀ s, c ∣ f s) (m : ℕ) : c ∣ dd m f := by
  rw [dd_eq_sum]
  refine Finset.dvd_sum fun k _ => ?_
  rw [zsmul_eq_mul]
  exact Dvd.dvd.mul_left (h k) _

lemma odd_part (k' P n : ℕ) (hk : 0 < k') (hP : φ k' ∣ P) (hn : k' ≤ n) :
    ∃ Z : ℤ, 2 ^ (n + P) * (a (n + P) - a n) = (k' : ℚ) * (Z : ℚ) := by
  have hterm : ∀ m : ℕ, ∃ w : ℤ, Tm (n + P) m - Tm n m = (k' : ℤ) * w := by
    intro m
    have hU : (k' : ℤ) ∣ Uz (n + P) m - Uz n m := by
      rw [Uz_sub]
      refine dvd_dd _ _ (fun s => ?_) m
      have := pow_per k' (2 * s + 1) n P hk hP hn
      push_cast at this; exact this
    have hV : (k' : ℤ) ∣ Vz (n + P) m - Vz n m := by
      unfold Vz; rw [← dd_sub]
      refine dvd_dd _ _ (fun s => ?_) m
      have := pow_per k' (2 * s) n P hk hP hn
      push_cast at this; exact this
    obtain ⟨w1, h1⟩ := hU
    obtain ⟨w2, h2⟩ := hV
    refine ⟨hh m * w1 + rr m * w2, ?_⟩
    unfold Tm
    have : hh m * Uz (n + P) m + rr m * Vz (n + P) m - (hh m * Uz n m + rr m * Vz n m)
        = hh m * (Uz (n + P) m - Uz n m) + rr m * (Vz (n + P) m - Vz n m) := by ring
    rw [this, h1, h2]; ring
  choose w hw using hterm
  refine ⟨∑ m ∈ range (n + P + 1), 2 ^ (n + P - m) * w m, ?_⟩
  rw [a_eq_sum (n + P) (n + P) le_rfl, a_eq_sum n (n + P) (by omega), ← sum_sub_distrib]
  push_cast
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun m hm => ?_
  have hm' : m ≤ n + P := by simp only [mem_range] at hm; omega
  have h := congrArg (fun x : ℤ => (x : ℚ)) (hw m)
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast] at h
  rw [← sub_div, h, pow_sub₀ (2 : ℚ) (by norm_num) hm']
  field_simp

/- ### integrality and the final divisibility -/

lemma a_int (n : ℕ) : a n ∈ (Int.castRingHom ℚ).range := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | m
    · rw [a_zero]; exact Subring.one_mem _
    · rw [a_succ, mul_sum]
      refine Subring.add_mem _ (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)
        (Subring.sum_mem _ fun k hk => ?_)
      have hk' : k < m + 1 := mem_range.1 hk
      have hc : ∃ e : ℤ, (1 - (-1 : ℚ) ^ (k + 1) - (-2 : ℚ) ^ (k + 1)) = 2 * (e : ℚ) := by
        rcases neg_one_pow_eq_or ℚ (k + 1) with h | h
        · exact ⟨(-2) ^ k, by rw [h, pow_succ]; push_cast; ring⟩
        · exact ⟨1 + (-2) ^ k, by rw [h, pow_succ]; push_cast; ring⟩
      obtain ⟨e, he⟩ := hc
      have hrew : 1 / 2 * (((m + 1).choose (k + 1) : ℚ) * (1 - (-1 : ℚ) ^ (k + 1) - (-2 : ℚ) ^ (k + 1))
          * a (m + 1 - (k + 1))) = (((m + 1).choose (k + 1) : ℤ) : ℚ) * (e : ℚ) * a (m + 1 - (k + 1)) := by
        rw [he]; push_cast; ring
      rw [hrew]
      exact Subring.mul_mem _ (Subring.mul_mem _ ⟨_, rfl⟩ ⟨_, rfl⟩) (ih _ (by omega))

lemma a_int' (n : ℕ) : ∃ z : ℤ, a n = (z : ℚ) := by
  obtain ⟨z, hz⟩ := a_int n
  exact ⟨z, by rw [← hz]; rfl⟩

lemma two_pow_ge (a' : ℕ) (h : 2 ≤ a') : a' + 2 ≤ 2 ^ a' := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le h
  induction b with
  | zero => norm_num
  | succ b ih =>
    have ih' := ih (by omega)
    rw [← add_assoc, pow_succ]; omega

theorem main_dvd (k n : ℕ) (hk : 2 < k) (hn : k ≤ n) (z1 z0 : ℤ)
    (h1 : a (n + φ k) = (z1 : ℚ)) (h0 : a n = (z0 : ℚ)) : (k : ℤ) ∣ z1 - z0 := by
  obtain ⟨a', k', hodd, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : k ≠ 0)
  have hk'pos : 0 < k' := hodd.pos
  have hpow : 0 < 2 ^ a' := by positivity
  -- odd part
  have hodd_dvd : (k' : ℤ) ∣ z1 - z0 := by
    obtain ⟨Z, hZ⟩ := odd_part k' (φ (2 ^ a' * k')) n hk'pos
      (Nat.totient_dvd_of_dvd (Dvd.intro_left _ rfl))
      (le_trans (Nat.le_mul_of_pos_left k' hpow) hn)
    rw [h1, h0] at hZ
    have hZ' : (2 : ℤ) ^ (n + φ (2 ^ a' * k')) * (z1 - z0) = (k' : ℤ) * Z := by exact_mod_cast hZ
    have hcop : IsCoprime (k' : ℤ) ((2 : ℤ) ^ (n + φ (2 ^ a' * k'))) := by
      have : Nat.Coprime k' (2 ^ (n + φ (2 ^ a' * k'))) :=
        Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hodd)
      exact_mod_cast Nat.isCoprime_iff_coprime.2 this
    exact hcop.dvd_of_dvd_mul_left ⟨Z, hZ'⟩
  -- 2-part
  have htwo : ((2 : ℤ) ^ a') ∣ z1 - z0 := by
    rcases Nat.eq_zero_or_pos a' with h | h
    · subst h; simp
    · have hP2 : 2 ∣ φ (2 ^ a' * k') := even_iff_two_dvd.1 (Nat.totient_even hk)
      have hP : 2 ^ (a' - 1) ∣ φ (2 ^ a' * k') := by
        have hc : Nat.Coprime (2 ^ a') k' := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hodd)
        rw [Nat.totient_mul hc, Nat.totient_prime_pow Nat.prime_two h]
        exact Dvd.dvd.mul_right (Dvd.intro _ rfl) _
      have hn2 : a' + 2 ≤ n := by
        refine le_trans ?_ hn
        rcases Nat.lt_or_ge a' 2 with h2 | h2
        · have : a' = 1 := by omega
          subst this
          simp only [pow_one] at hk ⊢
          omega
        · exact le_trans (two_pow_ge a' h2) (Nat.le_mul_of_pos_right _ hk'pos)
      obtain ⟨Z, hZ⟩ := two_part a' (φ (2 ^ a' * k')) n h hP2 hP hn2
      rw [h1, h0] at hZ
      exact ⟨Z, by exact_mod_cast hZ⟩
  have hcop : IsCoprime ((2 : ℤ) ^ a') (k' : ℤ) := by
    have : Nat.Coprime (2 ^ a') k' := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hodd)
    exact_mod_cast Nat.isCoprime_iff_coprime.2 this
  have := hcop.mul_dvd htwo hodd_dvd
  push_cast; exact this

end A370092

/--
%C A370092 Conjecture: Let k > 2 be a positive integer. The sequence obtained by reducing a(n) modulo k is eventually periodic with the period dividing phi(k) = A000010(k).
-/
theorem oeis_370092_conjecture_0 (k : ℕ) (hk : 2 < k) :
    ∃ P : ℕ, P ∣ totient k ∧ eventually_periodic (a_mod_k k) P := by
  refine ⟨totient k, dvd_rfl, k, fun n hn => ?_⟩
  obtain ⟨z1, h1⟩ := A370092.a_int' (n + totient k)
  obtain ⟨z0, h0⟩ := A370092.a_int' n
  unfold a_mod_k
  rw [h1, h0, Rat.num_intCast, Rat.num_intCast, ZMod.intCast_eq_intCast_iff_dvd_sub]
  have := A370092.main_dvd k n hk hn z1 z0 h1 h0
  rw [← dvd_neg]; simpa using this


/- ####################################################################
   Gauss congruences for A370092 (sharpened onset of the periodicity)
   #################################################################### -/

namespace A370092

open Function Polynomial
open fwdDiff

/-- sharper 2-adic bound for the weights of the even part -/
lemma rr_div2 (m : ℕ) : ∃ y : ℤ, 2 * ((m ! : ℤ) * rr m) = 2 ^ m * y := by
  rcases m with _ | _ | j
  · exact ⟨0, by simp [rr]⟩
  · exact ⟨1, by simp [rr]⟩
  · have hexp : 2 * (((j + 2) ! : ℤ) * rr (j + 2))
        = ((j : ℤ) + 2) * (2 * (((j + 1) ! : ℤ) * ch (j + 1)))
          + 2 * (((j : ℤ) + 1) * ((j : ℤ) + 2)) * (2 * ((j ! : ℤ) * ch j)) := by
      rw [Nat.factorial_succ (j + 1), Nat.factorial_succ j]; simp only [rr]; push_cast; ring
    obtain ⟨x0, hx0⟩ := (K_inv j).1
    obtain ⟨w, hw⟩ : ∃ w : ℤ, ((j : ℤ) + 1) * ((j : ℤ) + 2) = 2 * w := by
      obtain ⟨w, hw⟩ := Int.even_mul_succ_self ((j : ℤ) + 1)
      exact ⟨w, by rw [show ((j : ℤ) + 2) = (j : ℤ) + 1 + 1 by ring, hw]; ring⟩
    rcases Nat.even_or_odd' j with ⟨t, rfl | rfl⟩
    · -- j even: (j+2) is even
      obtain ⟨x1, hx1⟩ := (K_inv (2 * t + 1)).1
      refine ⟨((t : ℤ) + 1) * x1 + w * x0, ?_⟩
      rw [hexp, hw, hx1, hx0]; push_cast; ring
    · -- j odd: j+1 is even, so the factorial weight is fully divisible
      obtain ⟨y1, hy1⟩ := (K_inv (2 * t + 1 + 1)).2 ⟨t + 1, by ring⟩
      refine ⟨((2 * t + 1 : ℕ) + 2 : ℤ) * y1 + w * x0, ?_⟩
      rw [hexp, hw, hy1, hx0]; push_cast; ring

lemma term_even2 (a' n m : ℕ) (hn : a' + 1 ≤ n) : ∃ z : ℤ, rr m * Vz n m = 2 ^ (m + a') * z := by
  obtain ⟨y, hy⟩ := rr_div2 m
  obtain ⟨z, hz⟩ := Vz_div n m
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
  refine ⟨2 ^ t * z * y, ?_⟩
  rw [hz]
  have : rr m * (2 ^ (a' + 1 + t) * ((m ! : ℤ) * z)) = 2 ^ a' * 2 ^ t * z * (2 * ((m ! : ℤ) * rr m)) := by ring
  rw [this, hy]; ring

/-- the 2-part of the congruence, valid already from `n ≥ a' + 1` -/
lemma two_part2 (a' P n : ℕ) (ha : 1 ≤ a') (hP2 : 2 ∣ P) (hP : 2 ^ (a' - 1) ∣ P)
    (hn : a' + 1 ≤ n) : ∃ Z : ℤ, a (n + P) - a n = 2 ^ a' * (Z : ℚ) := by
  have hterm : ∀ m : ℕ, ∃ z : ℤ, Tm (n + P) m - Tm n m = 2 ^ (m + a') * z := by
    intro m
    obtain ⟨z1, h1⟩ := term_odd a' P ha hP2 hP n m
    obtain ⟨z2, h2⟩ := term_even2 a' (n + P) m (by omega)
    obtain ⟨z3, h3⟩ := term_even2 a' n m hn
    refine ⟨z1 + z2 - z3, ?_⟩
    unfold Tm
    have : hh m * Uz (n + P) m + rr m * Vz (n + P) m - (hh m * Uz n m + rr m * Vz n m)
        = hh m * (Uz (n + P) m - Uz n m) + rr m * Vz (n + P) m - rr m * Vz n m := by ring
    rw [this, h1, h2, h3]; ring
  choose z hz using hterm
  refine ⟨∑ m ∈ range (n + P + 1), z m, ?_⟩
  rw [a_eq_sum (n + P) (n + P) le_rfl, a_eq_sum n (n + P) (by omega), ← sum_sub_distrib]
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun m _ => ?_
  have h := congrArg (fun x : ℤ => (x : ℚ)) (hz m)
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at h
  rw [← sub_div, h, pow_add]
  field_simp

/-- powers are periodic modulo a prime power as soon as the exponent is at least `r` -/
lemma pow_per_pp (p r i n P : ℕ) (hp : p.Prime) (hP : φ (p ^ r) ∣ P) (hn : r ≤ n) :
    ((p ^ r : ℕ) : ℤ) ∣ (i : ℤ) ^ (n + P) - (i : ℤ) ^ n := by
  have hX : (i : ℤ) ^ (n + P) - (i : ℤ) ^ n = (i : ℤ) ^ n * ((i : ℤ) ^ P - 1) := by ring
  rw [hX]
  by_cases hpi : p ∣ i
  · apply Dvd.dvd.mul_right
    have : (p ^ r : ℕ) ∣ i ^ n := (pow_dvd_pow_of_dvd hpi r).trans (pow_dvd_pow i hn)
    exact_mod_cast this
  · apply Dvd.dvd.mul_left
    have hcop : Nat.Coprime i (p ^ r) :=
      Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp).2 hpi).symm
    have h1 := Nat.ModEq.pow_totient hcop
    obtain ⟨t, ht⟩ := hP
    have h2 : i ^ P ≡ 1 [MOD p ^ r] := by
      rw [ht, pow_mul]
      simpa using h1.pow t
    have h3 := (Nat.modEq_iff_dvd.1 h2.symm)
    simpa using h3

/-- the odd part, with the power congruence as a hypothesis -/
lemma odd_part' (k' P n : ℕ) (hpow : ∀ i : ℕ, (k' : ℤ) ∣ (i : ℤ) ^ (n + P) - (i : ℤ) ^ n) :
    ∃ Z : ℤ, 2 ^ (n + P) * (a (n + P) - a n) = (k' : ℚ) * (Z : ℚ) := by
  have hterm : ∀ m : ℕ, ∃ w : ℤ, Tm (n + P) m - Tm n m = (k' : ℤ) * w := by
    intro m
    have hU : (k' : ℤ) ∣ Uz (n + P) m - Uz n m := by
      rw [Uz_sub]
      refine dvd_dd _ _ (fun s => ?_) m
      have := hpow (2 * s + 1)
      push_cast at this; exact this
    have hV : (k' : ℤ) ∣ Vz (n + P) m - Vz n m := by
      unfold Vz; rw [← dd_sub]
      refine dvd_dd _ _ (fun s => ?_) m
      have := hpow (2 * s)
      push_cast at this; exact this
    obtain ⟨w1, h1⟩ := hU
    obtain ⟨w2, h2⟩ := hV
    refine ⟨hh m * w1 + rr m * w2, ?_⟩
    unfold Tm
    have : hh m * Uz (n + P) m + rr m * Vz (n + P) m - (hh m * Uz n m + rr m * Vz n m)
        = hh m * (Uz (n + P) m - Uz n m) + rr m * (Vz (n + P) m - Vz n m) := by ring
    rw [this, h1, h2]; ring
  choose w hw using hterm
  refine ⟨∑ m ∈ range (n + P + 1), 2 ^ (n + P - m) * w m, ?_⟩
  rw [a_eq_sum (n + P) (n + P) le_rfl, a_eq_sum n (n + P) (by omega), ← sum_sub_distrib]
  push_cast
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun m hm => ?_
  have hm' : m ≤ n + P := by simp only [mem_range] at hm; omega
  have h := congrArg (fun x : ℤ => (x : ℚ)) (hw m)
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast] at h
  rw [← sub_div, h, pow_sub₀ (2 : ℚ) (by norm_num) hm']
  field_simp

/-- periodicity modulo an odd prime power, from index `r` on -/
theorem per_odd_pp (p r P N : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hP : φ (p ^ r) ∣ P) (hN : r ≤ N) :
    ∃ z : ℤ, a (N + P) - a N = (p : ℚ) ^ r * (z : ℚ) := by
  obtain ⟨z1, h1⟩ := a_int' (N + P)
  obtain ⟨z0, h0⟩ := a_int' N
  obtain ⟨Z, hZ⟩ := odd_part' (p ^ r) P N (fun i => pow_per_pp p r i N P hp hP hN)
  rw [h1, h0] at hZ
  have hZ' : (2 : ℤ) ^ (N + P) * (z1 - z0) = ((p ^ r : ℕ) : ℤ) * Z := by exact_mod_cast hZ
  have hcop : IsCoprime (((p ^ r : ℕ)) : ℤ) ((2 : ℤ) ^ (N + P)) := by
    have : Nat.Coprime (p ^ r) (2 ^ (N + P)) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    exact_mod_cast Nat.isCoprime_iff_coprime.2 this
  obtain ⟨z, hz⟩ := hcop.dvd_of_dvd_mul_left ⟨Z, hZ'⟩
  refine ⟨z, ?_⟩
  rw [h1, h0]
  have : ((z1 - z0 : ℤ) : ℚ) = (((p ^ r : ℕ) : ℤ) : ℚ) * (z : ℚ) := by exact_mod_cast congrArg (fun x : ℤ => (x : ℚ)) hz
  push_cast at this
  linarith

/-- **Gauss congruences at odd primes**: `a(n p^(r+1) + s) ≡ a(n p^r + s) (mod p^(r+1))`. -/
theorem gauss_odd (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (n r s : ℕ) :
    ∃ z : ℤ, a (n * p ^ (r + 1) + s) - a (n * p ^ r + s) = (p : ℚ) ^ (r + 1) * (z : ℚ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, by simp⟩
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have hidx : n * (q + 1) ^ (r + 1) + s = (n * (q + 1) ^ r + s) + n * (q + 1) ^ r * q := by ring
  have hP : φ ((q + 1) ^ (r + 1)) ∣ n * (q + 1) ^ r * q := by
    rw [Nat.totient_prime_pow_succ hp]
    simp only [Nat.add_sub_cancel]
    exact ⟨n, by ring⟩
  have hN : r + 1 ≤ n * (q + 1) ^ r + s := by
    have h1 : r < (q + 1) ^ r := Nat.lt_pow_self hp.one_lt
    have h2 : (q + 1) ^ r ≤ n * (q + 1) ^ r := Nat.le_mul_of_pos_left _ hn
    omega
  rw [hidx]
  exact per_odd_pp (q + 1) (r + 1) _ _ hp hp2 hP hN

/-- **Gauss congruences at 2**: `a(n 2^(r+1) + s) ≡ a(n 2^r + s) (mod 2^(r+1))` for `r ≥ 1`,
with the single exception `(r, n, s) = (1, 1, 0)`. -/
theorem gauss_two (n r s : ℕ) (hr : 1 ≤ r) (hex : ¬ (r = 1 ∧ n = 1 ∧ s = 0)) :
    ∃ z : ℤ, a (n * 2 ^ (r + 1) + s) - a (n * 2 ^ r + s) = (2 : ℚ) ^ (r + 1) * (z : ℚ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, by simp⟩
  have hidx : n * 2 ^ (r + 1) + s = (n * 2 ^ r + s) + n * 2 ^ r := by ring
  have hN : r + 1 + 1 ≤ n * 2 ^ r + s := by
    rcases Nat.lt_or_ge r 2 with h2 | h2
    · have hr1 : r = 1 := by omega
      subst hr1
      simp only [pow_one]
      by_contra hcon
      apply hex
      refine ⟨rfl, ?_, ?_⟩ <;> omega
    · have h1 : r + 2 ≤ 2 ^ r := two_pow_ge r h2
      have h3 : 2 ^ r ≤ n * 2 ^ r := Nat.le_mul_of_pos_left _ hn
      omega
  have hP2 : 2 ∣ n * 2 ^ r := by
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    exact ⟨n * 2 ^ r', by ring⟩
  have hP : 2 ^ (r + 1 - 1) ∣ n * 2 ^ r := by
    simp only [Nat.add_sub_cancel]; exact Dvd.intro_left n rfl
  rw [hidx]
  exact two_part2 (r + 1) (n * 2 ^ r) (n * 2 ^ r + s) (by omega) hP2 hP hN

/- ### the exceptions are genuine -/

lemma a_one : a 1 = 1 := by
  rw [a_succ]; simp [a_zero]; norm_num

lemma a_two : a 2 = 3 := by
  rw [a_succ]; simp [sum_range_succ, a_zero, a_one, Nat.choose]; norm_num

lemma a_three : a 3 = 16 := by
  rw [a_succ]; simp [sum_range_succ, a_zero, a_one, a_two, Nat.choose]; norm_num

lemma a_four : a 4 = 105 := by
  rw [a_succ]; simp [sum_range_succ, a_zero, a_one, a_two, a_three, Nat.choose]; norm_num

/-- the excluded case `(r, n, s) = (1, 1, 0)`: `a(4) - a(2) = 102` is not divisible by 4 -/
theorem gauss_two_exception : ¬ ∃ z : ℤ, a (1 * 2 ^ (1 + 1) + 0) - a (1 * 2 ^ 1 + 0) = (2 : ℚ) ^ (1 + 1) * (z : ℚ) := by
  rintro ⟨z, hz⟩
  norm_num [a_four, a_two] at hz
  have h : (102 : ℤ) = 4 * z := by exact_mod_cast hz
  omega

/-- modulo 2 the congruence fails: `a(1*2 + 2) - a(1 + 2) = 89` is odd -/
theorem gauss_two_mod_two_fails : ¬ ∃ z : ℤ, a (1 * 2 ^ (0 + 1) + 2) - a (1 * 2 ^ 0 + 2) = (2 : ℚ) ^ (0 + 1) * (z : ℚ) := by
  rintro ⟨z, hz⟩
  norm_num [a_four, a_three] at hz
  have h : (89 : ℤ) = 2 * z := by exact_mod_cast hz
  omega

end A370092

