import tactic.linarith
import data.real.basic
import data.complex.exponential
import data.polynomial
import data.nat.choose

/-

M1F May exam 2018, question 1.

-/

universe u

local attribute [instance, priority 0] classical.prop_decidable

open nat

-- Q1(a)(i)
theorem count (n : ℕ) (hn : n ≥ 1) : finset.sum (finset.range (nat.succ n)) (λ m, choose n m) =
  2 ^ n --answer
  :=
begin
  have H := (add_pow (1 : ℕ) 1 n).symm,
  simpa [nat.one_pow, one_mul, one_add_one_eq_two,
    (finset.sum_nat_cast _ _).symm, nat.cast_id] using H,
end

-- Q1(a)(ii)
theorem countdown (n : ℕ) (hn : n ≥ 1) :
  finset.sum (finset.range (nat.succ n)) (λ m, (-1 : ℤ) ^ m * choose n m) =
  0 -- answer
  := 
begin
  have H := (add_pow (-1 : ℤ) 1 n).symm,
  have H2 := @_root_.zero_pow ℤ _ _ hn,
  simpa [nat.one_pow, one_mul, one_add_one_eq_two, nat.zero_pow hn,
    (finset.sum_nat_cast _ _).symm, nat.cast_id, H2] using H,
end

-- Q1(b) preparation
open real polynomial
noncomputable def chebyshev : ℕ → polynomial ℝ
| 0 := C 1
| 1 := X
| (n + 2) := 2 * X * chebyshev (n + 1) - chebyshev n

def chebyshev' : ℕ → polynomial ℤ
| 0 := C 1
| 1 := X
| (n + 2) := 2 * X * chebyshev' (n + 1) - chebyshev' n

lemma polycos_zero (θ : ℝ) : cos (0 * θ) = polynomial.eval (cos θ) (chebyshev 0) :=
by rw [chebyshev, eval_C, zero_mul, cos_zero]

lemma polycos (n : ℕ) (hn : n ≥ 1) : ∀ θ : ℝ, cos (n * θ) = polynomial.eval (cos θ) (chebyshev n) :=
begin
  intro θ,
  apply nat.strong_induction_on n,
  intros k ih,
  have ih1 : cos (↑(k - 1) * θ) = polynomial.eval (cos θ) (chebyshev (k - 1)),
  { by_cases h : k = 0,
    { rw [h, (show (0 - 1 = 0), by refl)], convert polycos_zero θ},
    -- h : k ≠ 0,
    { exact ih (k - 1) (nat.sub_lt (nat.pos_of_ne_zero h) (by norm_num : 0 < 1)) }
  },
  have ih2 : cos (↑(k - 2) * θ) = polynomial.eval (cos θ) (chebyshev (k - 2)),
  { by_cases h : k = 0,
    { rw [h, (show (0 - 2 = 0), from rfl)], convert polycos_zero θ},--, chebyshev, eval_one],
    -- h : k ≠ 0,
    { exact ih (k - 2) (nat.sub_lt (nat.pos_of_ne_zero h) (by norm_num : 0 < 2)) }
  },
  by_cases h1 : k = 0,
    rw h1, exact polycos_zero θ,
  by_cases h2 : k = 1,
  { rw [h2, chebyshev, eval_X],
    congr', 
    convert one_mul θ,
    simp},
  have hk : k = (k - 2) + 2, rw nat.sub_add_cancel, swap,
   rw [hk, chebyshev, ←hk, nat.succ_eq_add_one, (_ : k - 2 + 1 = k - 1), two_mul,
        polynomial.eval_sub, polynomial.eval_mul, polynomial.eval_add,
         polynomial.eval_X, ←two_mul, ←ih1, ←ih2],
        rw [←complex.of_real_inj, complex.of_real_sub, complex.of_real_mul, complex.of_real_mul,
            complex.of_real_cos, complex.of_real_cos, complex.of_real_cos, complex.of_real_cos,
            complex.cos, complex.cos, complex.cos, complex.cos],
        simp,
        rw [mul_div_cancel', ←mul_div_assoc, ←neg_div, ←add_div, add_mul, mul_add, mul_add,
            ←complex.exp_add, ←complex.exp_add, ←complex.exp_add, ←complex.exp_add,
            mul_assoc, mul_assoc, mul_assoc],
        rw [←one_mul (↑θ * complex.I)] {occs := occurrences.pos [5, 7]},
        rw [←add_mul, ←sub_eq_add_neg, ←sub_mul, ←neg_one_mul (↑θ * complex.I),
            ←add_mul, ←sub_eq_add_neg, ←sub_mul, @nat.cast_sub _ _ _ 1 k, add_sub, nat.cast_one,
            add_sub_cancel', ←sub_add, sub_add_eq_add_sub, one_add_one_eq_two, add_sub,
            ←sub_add_eq_add_sub, ←neg_add', one_add_one_eq_two, ←sub_add, sub_add_eq_add_sub,
            neg_add_self, zero_sub, nat.cast_sub, neg_mul_eq_neg_mul, neg_mul_eq_neg_mul,
            neg_sub, nat.cast_two, neg_add, sub_eq_neg_add, ←add_assoc, ←neg_add,
            ←sub_eq_neg_add, add_sub_add_right_eq_sub, ←add_assoc, sub_add_cancel],
        all_goals {
            try {
            have H : k ≥ 2,
                apply le_of_not_gt, intro,
                have h12 : k = 0 ∨ k = 1,
                    clear ih ih1 ih2 h1 h2, try { clear hk },
                    revert k a, exact dec_trivial,
                apply or.elim h12 (λ h12, h1 h12) (λ h12, h2 h12) },
                try { exact H }, try { exact le_trans (by norm_num : 1 ≤ 2) H } },
        apply two_ne_zero',
        apply @eq_of_add_eq_add_right _ _ _ 1 _,
        rw [add_assoc, one_add_one_eq_two, nat.sub_add_cancel H,
            nat.sub_add_cancel (le_trans (by norm_num : 1 ≤ 2) H)],
    end

-- Q1(b)(i)
theorem exist_polycos (n : ℕ) (hn : n ≥ 1) :
  ∃ Pn : polynomial ℝ, ∀ θ : ℝ, cos (n * θ) = polynomial.eval (cos θ) Pn := ---ans
Exists.intro (chebyshev n) (polycos n hn)


open polynomial

-- Q1(b)(ii)
example : chebyshev' 4 = 8 * X ^ 4 - 8 * X ^ 2 + 1 := dec_trivial

-- Q1(b)(iii) preparation
lemma useful (k : ℕ) : polynomial.degree (chebyshev' k) = k :=
begin
  apply nat.strong_induction_on k,
  intros n ih,
  have ih1 : polynomial.degree (chebyshev' (n - 1)) = ↑(n - 1),
  { by_cases h : n = 0,
    { rw h, apply degree_C, norm_num },--simp [h, chebyshev'], },
    { exact ih _ (nat.sub_lt (nat.pos_of_ne_zero h) (zero_lt_one)) },
  },
  have ih2 : polynomial.degree (chebyshev' (n - 2)) = ↑(n - 2),
  { by_cases h : n ≤ 1,
    { apply or.elim ((dec_trivial : ∀ j : ℕ, j ≤ 1 → j = 0 ∨ j = 1) n h),
      { intro h0, rw h0, apply degree_C, norm_num },
      { intro h1, rw h1, apply degree_C, norm_num },
    },
    { apply ih _, apply nat.sub_lt (lt_of_not_ge (λ w, h (le_trans w zero_le_one))),
      norm_num },
  },
  by_cases h : n ≥ 2,
  { have H : n - 2 + 2 = n := nat.sub_add_cancel h,
    have H' : nat.succ (n - 2) = n - 1, 
    { have W : n ≥ 2,
      { apply le_of_not_gt, intro,
        have h12 : n = 0 ∨ n = 1,
        { clear ih ih1 ih2 H h,
          revert n a, exact dec_trivial },
        apply or.elim h12,
          intro h1, rw h1 at h, revert h, norm_num,
          intro h2, rw h2 at h, revert h, norm_num
      },
      apply @eq_of_add_eq_add_right _ _ _ 1 _,
      show n - 2 + 1 + 1 = n - 1 + 1,
      rw [add_assoc, one_add_one_eq_two, nat.sub_add_cancel W,
        nat.sub_add_cancel (le_of_lt h)]
    },
    rw [←H, chebyshev', H, sub_eq_neg_add, polynomial.degree_add_eq_of_degree_lt,
      polynomial.degree_mul_eq, polynomial.degree_mul_eq, polynomial.degree_X, H', ih1],
    { show (polynomial.degree (polynomial.C 2) + 1 + ↑(n - 1) = ↑n),
      rw [polynomial.degree_C, zero_add, ←with_bot.coe_one, ←with_bot.coe_add,
        add_comm, nat.sub_add_cancel (le_of_lt h)],
      exact two_ne_zero',
    },
    { rw [polynomial.degree_neg, polynomial.degree_mul_eq, polynomial.degree_mul_eq, ih2, H', ih1],
      show (↑(n - 2) < polynomial.degree (polynomial.C 2) + polynomial.degree polynomial.X + ↑(n - 1)),
      rw [polynomial.degree_C, polynomial.degree_X, zero_add, ←with_bot.coe_one, ←with_bot.coe_add,
        add_comm, nat.sub_add_cancel (le_of_lt h), with_bot.coe_lt_coe],
        apply nat.sub_lt (lt_trans zero_lt_one h), norm_num,
      exact two_ne_zero'
    }
  },
  { apply or.elim ((dec_trivial : ∀ j : ℕ, j ≤ 1 → j = 0 ∨ j = 1) n (le_of_not_gt h)),
      intro h0, rw h0, apply degree_C, exact dec_trivial,
      intro h1, rw h1, exact degree_X
  }
end 

lemma useful' (k : ℕ) : polynomial.degree (chebyshev' (k - 2)) < 1 + polynomial.degree (chebyshev' (k - 1)) :=
begin
    rw [useful, useful, ←with_bot.coe_one, ←with_bot.coe_add, with_bot.coe_lt_coe, add_comm],
    by_cases h : k ≤ 1,
        apply or.elim ((dec_trivial : ∀ (j : ℕ), j ≤ 1 → j = 0 ∨ j = 1) k h),
            intro h0, simp [h0], exact zero_lt_one,
            intro h1, simp [h1], exact zero_lt_one,
    rw [nat.sub_add_cancel (le_of_not_le h)],
    apply nat.sub_lt (lt_of_lt_of_le zero_lt_one (le_of_not_le h)), norm_num
end

-- Q1(b)(iii)
theorem leading_coeff (n : ℕ) : polynomial.leading_coeff (chebyshev' n) =
  2 ^ (n - 1) := ---ans
begin
    apply nat.strong_induction_on n, intros k hk,
    have h1 : polynomial.leading_coeff (chebyshev' (k - 1)) = 2 ^ (k - 1 - 1),
        by_cases h : k = 0,
          rw h, show (leading_coeff (C (1 : ℤ)) = 1),exact leading_coeff_C (1 : ℤ),
          exact hk (k - 1) (nat.pred_lt h : k - 1 < k),
    have h2 : polynomial.leading_coeff (chebyshev' (k - 2)) = 2 ^ (k - 2 - 1),
        by_cases h : k ≤ 1,
            apply or.elim ((dec_trivial : ∀ j : ℕ, j ≤ 1 → j = 0 ∨ j = 1) k h),
                intro h0, rw h0, exact leading_coeff_C (1 : ℤ),
                intro h1, rw h1, exact leading_coeff_C (1 : ℤ),
            exact hk (k - 2) (nat.sub_lt (lt_of_not_ge (λ w, h (le_trans w zero_le_one))) (by norm_num)),
    by_cases h : k ≥ 2,
        have H : k - 2 + 2 = k := nat.sub_add_cancel h,
        rw [←H, chebyshev', H, (_ : nat.succ (k - 2) = k - 1), sub_eq_add_neg, add_comm,
            polynomial.leading_coeff_add_of_degree_lt, polynomial.leading_coeff_mul,
            polynomial.leading_coeff_mul, ←one_add_one_eq_two,
            polynomial.leading_coeff_add_of_degree_eq rfl, ←polynomial.C_1,
            polynomial.leading_coeff_C, polynomial.leading_coeff_X, h1,
            one_add_one_eq_two, mul_one, (_root_.pow_succ (2 : ℤ) (k - 1 - 1)).symm, nat.sub_add_cancel],
    change 1 ≤ k - 1,
    rwa [nat.le_sub_left_iff_add_le (le_of_lt h), one_add_one_eq_two],
    rw [←polynomial.C_1, polynomial.leading_coeff_C, one_add_one_eq_two], exact two_ne_zero',
    rw [polynomial.degree_neg, polynomial.degree_mul_eq, polynomial.degree_mul_eq,
        ((one_add_one_eq_two).symm : ((2 : polynomial ℤ) = 1 + 1)), ←polynomial.C_1, ←polynomial.C_add,
        one_add_one_eq_two, polynomial.degree_C, zero_add, polynomial.degree_X],
    exact useful' k,
    exact two_ne_zero',
    rw [nat.succ_eq_add_one, eq_comm, ←nat.sub_eq_iff_eq_add, nat.sub_sub, one_add_one_eq_two],
    rwa [nat.le_sub_left_iff_add_le (le_of_lt h), one_add_one_eq_two],
    rw not_lt at h,
    have h' : k = 0 ∨ k = 1, clear hk h1 h2, revert k h, exact dec_trivial,
    cases h',
    { rw h', exact leading_coeff_C (1 : ℤ)},
    { rw h', exact leading_coeff_C (1 : ℤ)}
end

-- Q1(b)(iv)
theorem cheby1 (n : ℕ) (hn : n ≥ 1) : polynomial.eval 1 (chebyshev n) = 1 := ---ans
begin
    have h := (polycos n hn 0).symm,
    rwa [mul_zero, cos_zero] at h,
end
