import tactic.norm_num
import tactic.linarith
import tactic.ring
import data.nat.basic
import data.real.basic
import data.set.basic
import data.set.lattice
import data.complex.basic
import data.complex.exponential
import data.polynomial
import analysis.polynomial
import analysis.exponential

universe u
local attribute [instance, priority 0] classical.prop_decidable
--QUESTION 1
----part a
------i
theorem count (n : ℕ) (hn : n ≥ 1) : finset.sum (finset.range (nat.succ n)) (λ m, choose n m) = 2 ^ n := ---ans
    begin
        have H := (add_pow (1 : ℕ) 1 n).symm,
        simp [one_pow, one_mul, one_add_one_eq_two, 
            (finset.sum_nat_cast _ _).symm, nat.cast_id] at H,
        simpa
    end

------ii
theorem countdown (n : ℕ) (hn : n ≥ 1) : finset.sum (finset.range (nat.succ n)) (λ m, (-1 : ℤ) ^ m * choose n m) = 0 := ---ans
    begin
        have H := (add_pow (-1 : ℤ) 1 n).symm,
        simp [one_pow, one_mul, one_add_one_eq_two, zero_pow hn,
            (finset.sum_nat_cast _ _).symm, nat.cast_id] at H,
        simpa
    end

----part b
------i
open real

noncomputable def chebyshev : ℕ → polynomial ℝ
| 0 := polynomial.C 1
| 1 := polynomial.X
| (n + 2) := 2 * polynomial.X * chebyshev (n + 1) - chebyshev n

theorem exist_polycos (n : ℕ) (hn : n ≥ 1) : ∃ Pn : polynomial ℝ, ∀ θ : ℝ, cos (n * θ) = polynomial.eval (cos θ) Pn := ---ans
    begin
        existsi chebyshev n, intro θ,
        apply nat.strong_induction_on n,
        intros k ih, 
        have ih1 : cos (↑(k - 1) * θ) = polynomial.eval (cos θ) (chebyshev (k - 1)),
            by_cases h : k = 0,
              simp [h, chebyshev],
          --by_cases h : k ≠ 0,
              exact ih (k - 1) (nat.sub_lt (nat.pos_of_ne_zero h) (by norm_num : 0 < 1)),
        have ih2 : cos (↑(k - 2) * θ) = polynomial.eval (cos θ) (chebyshev (k - 2)),
            by_cases h : k = 0,
              simp [h, chebyshev],
            --by_cases h : k ≠ 0,
              exact ih (k - 2) (nat.sub_lt (nat.pos_of_ne_zero h) (by norm_num : 0 < 2)),
        by_cases h1 : k = 0, simp [h1, chebyshev],
        by_cases h2 : k = 1, simp [h2, chebyshev],
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
            nat.sub_add_cancel (le_trans (by norm_num : 1 ≤ 2) H)]
    end

--QUESTION 2
----part a
------i
def ub (S : set ℝ) (x : ℝ) := ∀ s ∈ S, s ≤ x ---ans

------ii
def iba (S : set ℝ) := ∃ x, ub S x ---ans

------iii
def lub (S : set ℝ) (x : ℝ) := ub S x ∧ ∀ y : ℝ, (ub S y → x ≤ y) ---ans

----part b
theorem lub_duh (S : set ℝ) : (∃ x, lub S x) → S ≠ ∅ ∧ iba S := ---ans
    begin
        intro Hexlub, cases Hexlub with x Hlub,
        split,
            intro Hemp, rw set.empty_def at Hemp, 
            cases Hlub with Hub Hl,
            have Hallub : ∀ y : ℝ, ub S y, 
                unfold ub, rw Hemp, change (∀ (y s : ℝ), false → s ≤ y), 
                intros y s Hf, exfalso, exact Hf,
            have Hneginf : ∀ y : ℝ, x ≤ y,
                intro y, apply Hl, apply Hallub,
            have Hcontr := Hneginf (x - 1),
            revert Hcontr, norm_num,
      --split,
            existsi x, exact Hlub.left,
    end

----part c
------i
def S1 := {x : ℝ | x < 59}

lemma between_bounds (x y : ℝ) (H : x < y) : x < (x + y) / 2 ∧ (x + y) / 2 < y := 
⟨by linarith, by linarith⟩

theorem S1_lub : ∃ x, lub S1 x := ---ans
    begin
        existsi (59 : ℝ),
        split,
            intro, change (s < 59 → s ≤ 59), exact le_of_lt,
      --split,
            intro y, change ((∀ (s : ℝ), s < 59 → s ≤ y) → 59 ≤ y), intro Hbub,
            apply le_of_not_gt, intro Hbadub,
            have Houtofbounds := between_bounds y 59 Hbadub,
            apply not_le_of_gt Houtofbounds.1 (Hbub ((y + 59) / 2) Houtofbounds.2),
    end

------ii

/------------------SORRY--------------------/

----part d
------i
theorem ublub_the_first (S : set ℝ) (b : ℝ) (hub : ub S b) (hin : b ∈ S) : lub S b := ---ans
    begin
        split,
            exact hub,
      --split,
            intros y huby,
            exact huby b hin,
    end

------ii
theorem adlub_the_second (S T : set ℝ) (b c : ℝ) (hlubb : lub S b) (hlubc : lub T c) ---ans
: lub ({x : ℝ | ∃ s t : ℝ, s ∈ S ∧ t ∈ T ∧ x = s + t}) (b + c) :=
    begin
        split,
            unfold ub, simp, intros x s hss t htt hxst, rw hxst,
            apply add_le_add (hlubb.1 s hss) (hlubc.1 t htt),
      --split,
            unfold ub, simp, intros x Hx,
            apply le_of_not_gt, intro Hcontr,
            let ε := b + c - x, 
            have Hcontr' : ε > 0 := (by linarith : b + c - x > 0),
            have rwx : x = (b - ε / 2) + (c - ε / 2) 
            := (by linarith : x = (b - (b + c - x) / 2) + (c - (b + c - x) / 2)),
            have hnbub : ∃ s' ∈ S, b - ε / 2 < s',
                by_contradiction,
                have a' : (¬∃ (s' : ℝ), s' ∈ S ∧ b - ε / 2 < s'), 
                    intro b, apply a, cases b with σ Hσ, existsi σ, existsi Hσ.1, exact Hσ.2,
                have a'' : ∀ (x : ℝ), x ∈ S → ¬(b - ε / 2 < x),
                    intros x Hx Hb, rw not_exists at a', apply a' x, exact ⟨Hx, Hb⟩,
                simp only [not_lt] at a'', rw ←ub at a'',
                have a''' := hlubb.2 _ a'',
                linarith,
            have hnbuc : ∃ t' ∈ T, c - ε / 2 < t',
                by_contradiction,
                have a' : (¬∃ (t' : ℝ), t' ∈ T ∧ c - ε / 2 < t'), 
                    intro b, apply a, cases b with σ Hσ, existsi σ, existsi Hσ.1, exact Hσ.2,
                have a'' : ∀ (x : ℝ), x ∈ T → ¬(c - ε / 2 < x),
                    intros x Hx Hc, rw not_exists at a', apply a' x, exact ⟨Hx, Hc⟩,
                simp only [not_lt] at a'', rw ←ub at a'',
                have a''' := hlubc.2 _ a'',
                linarith,
            cases hnbub with s' hnbub', cases hnbub' with Hs' hnbub'',
            cases hnbuc with t' hnbuc', cases hnbuc' with Ht' hnbuc'',
            have Hx' := Hx (s' + t') s' Hs' t' Ht' rfl,
            have Haha : x < x 
            := lt_of_lt_of_le (by { rw rwx, apply add_lt_add hnbub'' hnbuc'' } : x < s' + t') Hx',
            linarith,            
    end

--QUESTION 3
variable {S : Type u}

----part a
------i
variable (binary_relation : S → S → Prop) ---ans
local infix ` ~ `:1000 := binary_relation

------ii
def reflexivity := ∀ x, x ~ x
def symmetry := ∀ (x y), x ~ y → y ~ x
def transitivity := ∀ (x y z), x ~ y → y ~ z → x ~ z
def is_equivalence := reflexivity binary_relation ∧ symmetry binary_relation ∧ transitivity binary_relation ---ans

------iii
variable {binary_relation}
def cl (h : is_equivalence binary_relation) (a : S) : set S := { x | x ~ a } ---ans

----part b
theorem classes_injective2 (h : is_equivalence binary_relation) (a b : S) : (cl h a = cl h b) ∨ (cl h a ∩ cl h b) = ∅ := ---ans
    begin
        /-duplicate h so we can continue using it as a parameter to cl, then unpack hDupe-/
        have hDupe : is_equivalence binary_relation := h,
        cases hDupe with hR hST, cases hST with hS hT,
        rw reflexivity at hR, rw symmetry at hS, rw transitivity at hT,
        /-if one of them is true (if they exclude) we don't need to bother-/
        cases classical.em (cl h a ∩ cl h b = ∅) with excl intsct,
        --case excl
            right, exact excl,
        --case intsct
            left,
            /-prove that if something isn't empty it must have stuff in it-/
            rw set.eq_empty_iff_forall_not_mem at intsct,
            rw not_forall_not at intsct,
            /-clean stuff up-/
            cases intsct with x intsctX, cases intsctX with intsctXa intsctXb,
            rw cl at intsctXa, rw cl at intsctXb,
            change binary_relation x a at intsctXa, change binary_relation x b at intsctXb,
            rename intsctXa Hrxa, rename intsctXb Hrxb,
            rw cl, rw cl,
            /-now do the actual math-/
            have Hrax : binary_relation a x, apply hS x a, exact Hrxa,
            have Hrab : binary_relation a b, apply hT a x b, exact Hrax, exact Hrxb,
            have Hrba : binary_relation b a, apply hS a b, exact Hrab,
            /-definition of set equivalence-/
            apply set.eq_of_subset_of_subset,
            --split 1
                /-clean things up again-/
                intro y, intro Hrya, change binary_relation y a at Hrya, change binary_relation y b,
                /-do math again-/
                apply hT y a b, exact Hrya, exact Hrab,
            --split 2
                /-clean things up again-/
                intro y, intro Hryb, change binary_relation y b at Hryb, change binary_relation y a,
                /-do math again-/
                have Hrby : binary_relation b y, apply hS y b, exact Hryb,
                apply hT y b a, exact Hryb, exact Hrba,
    end

----part c

inductive double_cosets : ℤ → ℤ → Prop
    | cond1 : ∀ x, double_cosets x (x + 3)
    | cond2 : ∀ x, double_cosets x (x - 5)
    | condT : ∀ x y z, double_cosets x y → double_cosets y z → double_cosets x z
local infix ` ⋆ `:1001 := double_cosets

theorem double_cosets_reflexive : reflexivity double_cosets := ---ans
    begin
        rw reflexivity, intro x,
        /-get some trivial things out of the way-/
        have H0 : x - 5 - 5 - 5 + 3 + 3 + 3 + 3 + 3 = x, norm_num,
        /-start moving-/
        have Hx5x : x ⋆ (x - 5), exact double_cosets.cond2 x,
        have H5x10x : (x - 5) ⋆ (x - 5 - 5), exact double_cosets.cond2 (x - 5),
        have H10x15x : (x - 5 - 5) ⋆ (x - 5 - 5 - 5), exact double_cosets.cond2 (x - 5 - 5),
        /-transitivity is hopper fare-/
        have Hx10x : x ⋆ (x - 5 - 5), apply double_cosets.condT x (x - 5) (x - 5 - 5), exact Hx5x, exact H5x10x,
        have Hx15x : x ⋆ (x - 5 - 5 - 5), apply double_cosets.condT x (x - 5 - 5) (x - 5 - 5 - 5), exact Hx10x, exact H10x15x,
        /-now come back-/
        have H15x12x : (x - 5 - 5 - 5) ⋆ (x - 5 - 5 - 5 + 3), exact double_cosets.cond1 (x - 5 - 5 - 5),
        have H12x9x : (x - 5 - 5 - 5 + 3) ⋆ (x - 5 - 5 - 5 + 3 + 3), exact double_cosets.cond1 (x - 5 - 5 - 5 + 3),
        have H9x6x : (x - 5 - 5 - 5 + 3 + 3) ⋆ (x - 5 - 5 - 5 + 3 + 3 + 3), exact double_cosets.cond1 (x - 5 - 5 - 5 + 3 + 3),
        have H6x3x : (x - 5 - 5 - 5 + 3 + 3 + 3) ⋆ (x - 5 - 5 - 5 + 3 + 3 + 3 + 3), exact double_cosets.cond1 (x - 5 - 5 - 5 + 3 + 3 + 3),
        have H3xx : (x - 5 - 5 - 5 + 3 + 3 + 3 + 3) ⋆ (x - 5 - 5 - 5 + 3 + 3 + 3 + 3 + 3), exact double_cosets.cond1 (x - 5 - 5 - 5 + 3 + 3 + 3 + 3),
        /-are we still within 1 hour?-/
        have H15x9x : (x - 5 - 5 - 5) ⋆ (x - 5 - 5 - 5 + 3 + 3), apply double_cosets.condT (x - 5 - 5 - 5) (x - 5 - 5 - 5 + 3) (x - 5 - 5 - 5 + 3 + 3), exact H15x12x, exact H12x9x,
        have H15x6x : (x - 5 - 5 - 5) ⋆ (x - 5 - 5 - 5 + 3 + 3 + 3), apply double_cosets.condT (x - 5 - 5 - 5) (x - 5 - 5 - 5 + 3 + 3) (x - 5 - 5 - 5 + 3 + 3 + 3), exact H15x9x, exact H9x6x,
        have H15x3x : (x - 5 - 5 - 5) ⋆ (x - 5 - 5 - 5 + 3 + 3 + 3 + 3), apply double_cosets.condT (x - 5 - 5 - 5) (x - 5 - 5 - 5 + 3 + 3 + 3) (x - 5 - 5 - 5 + 3 + 3 + 3 + 3), exact H15x6x, exact H6x3x,
        have H15xx : (x - 5 - 5 - 5) ⋆ (x - 5 - 5 - 5 + 3 + 3 + 3 + 3 + 3), apply double_cosets.condT (x - 5 - 5 - 5) (x - 5 - 5 - 5 + 3 + 3 + 3 + 3) (x - 5 - 5 - 5 + 3 + 3 + 3 + 3 + 3), exact H15x3x, exact H3xx,
        have Hxx : x ⋆ (x - 5 - 5 - 5 + 3 + 3 + 3 + 3 + 3), apply double_cosets.condT x (x - 5 - 5 - 5) (x - 5 - 5 - 5 + 3 + 3 + 3 + 3 + 3), exact Hx15x, exact H15xx,
        /-show that we're back-/
        rw H0 at Hxx, exact Hxx,
    end

----part d

def S' : Type := fin 2

inductive self : fin 2 → fin 2 → Prop
    | condR : ∀ x, self x x
local infix ` ⋆ `:1 := self

theorem self_transitive : transitivity self := ---ans
    begin
        rw transitivity,
        intros x y z,
        --rw S' at z y x,
        have Hxyyzzx : x = y ∨ y = z ∨ z = x,
            cases classical.em (x = y ∨ y = z ∨ z = x) with corr contr,
            --case corr
                exact corr,
            --case contr
                exfalso,
                have contr_rw : ¬ (x = y) ∧ ¬ (y = z) ∧ ¬ (z = x),
                    rw ←not_or_distrib, rw ←not_or_distrib, exact contr,
                cases contr_rw with contr_xy contr_yzzx, cases contr_yzzx with contr_yz contr_zx,
                have H01 : ∀ s : fin 2, s = 0 ∨ s = 1, exact dec_trivial,
                have x01 : x = 0 ∨ x = 1, exact H01 x,
                have y01 : y = 0 ∨ y = 1, exact H01 y,
                have z01 : z = 0 ∨ z = 1, exact H01 z,
                cases x01, cases y01, cases z01,
                    rw ←y01 at x01, apply contr_xy, exact x01,
                    rw ←y01 at x01, apply contr_xy, exact x01,
                  cases z01,
                    rw ←x01 at z01, apply contr_zx, exact z01,
                    rw ←z01 at y01, apply contr_yz, exact y01,
                  cases y01, cases z01,
                    rw ←z01 at y01, apply contr_yz, exact y01,
                    rw ←x01 at z01, apply contr_zx, exact z01,
                  cases z01,
                    rw ←y01 at x01, apply contr_xy, exact x01,
                    rw ←y01 at x01, apply contr_xy, exact x01,
        cases Hxyyzzx with Hxy Hyzzx,
        --case Hxy
            rw Hxy,
            intro Hyy, intro Hyz, exact Hyz,
          cases Hyzzx with Hyz Hxy,
        --case Hyz
            rw Hyz,
            intro Hxz, intro Hzz, exact Hxz,
        --case Hxy
            rw Hxy,
            intro Hxy, intro Hyx, exact self.condR x,
    end

--QUESTION 4
variable {X : Type u}
variable {Y : Type u}
variable {f : X → Y}

----part a
------i
def injectivity (g : X → Y) := ∀ x1 x2 : X, g x1 = g x2 → x1 = x2 ---ans

------ii
def surjectivity (g : X → Y) := ∀ y : Y, ∃ x : X, g x = y ---ans

------iii
def bijectivity (g : X → Y) := injectivity g ∧ surjectivity g ---ans

----part b
------i
def f1 : ℕ → ℕ
    | n := n + 2
theorem injection : ∃ f : ℕ → ℕ, injectivity f ∧ ¬ surjectivity f := ---ans
    begin
        have injectionf1 : injectivity f1 ∧ ¬ surjectivity f1,
            split,
            --split 1
                rw injectivity,
                change ∀ (x1 x2 : ℕ), x1 + 2 = x2 + 2 → x1 = x2,
                intros x1 x2, intro Hinjsame,
                calc x1 = x1 + 2 - 2 : by rw nat.add_sub_cancel
                    ... = x2 + 2 - 2 : by rw Hinjsame
                    ... = x2 : by rw nat.add_sub_cancel,
            --split 2
                rw surjectivity, intro Hsurj,
                change ∀ (y : ℕ), ∃ (x : ℕ), x + 2 = y at Hsurj,
                have Hsurj1 := Hsurj 1,
                cases Hsurj1 with x Hx10',
                have Hx10 : x + 1 = 0 :=
                    calc x + 1 = x + (2 - 1) : by norm_num
                           ... = (x + 2) - 1 : begin rw ←nat.add_sub_assoc, norm_num end
                           ... = 1 - 1 : by rw Hx10'
                           ... = 0 : by rw nat.sub_self,
                have Hnx10 : x + 1 ≠ 0, exact nat.add_one_ne_zero x,
                apply Hnx10, exact Hx10,
        fapply exists.intro, exact f1, exact injectionf1,
    end

------ii
def f2 : ℕ → ℕ
    | n := n / 2

theorem surjection : ∃ f : ℕ → ℕ, surjectivity f ∧ ¬ injectivity f := ---ans
    begin
        have surjectionf2 : surjectivity f2 ∧ ¬ injectivity f2,
            split,
            --split 1
                rw surjectivity,
                change ∀ (y : ℕ), ∃ (x : ℕ), x / 2 = y,
                intro y,
                fapply exists.intro, exact 2 * y,
                    calc 2 * y / 2 = (2 * y + 0) / 2 : by rw nat.add_zero
                               ... = (0 + 2 * y) / 2 : by rw nat.add_comm
                               ... = 0 / 2 + y : begin rw nat.add_mul_div_left 0 y, norm_num, end
                               ... = 0 + y : by norm_num
                               ... = y + 0 : by rw nat.add_comm
                               ... = y : by rw nat.add_zero,
            --split 2
                rw injectivity, intro Hinj,
                change ∀ (x1 x2 : ℕ), x1 / 2 = x2 / 2 → x1 = x2 at Hinj,
                have Hinjsame23 := Hinj 2 3,
                have Hn23 : 2 = 3 → false, norm_num,
                apply Hn23, apply Hinjsame23, norm_num,
        fapply exists.intro, exact f2, exact surjectionf2,
    end

------iii
theorem bijections_are_injections : (∃ f : ℕ → ℕ, bijectivity f ∧ ¬ injectivity f) → false := ---ans
    begin
        intro Hf,
        cases Hf with f Hff,
        rw bijectivity at Hff,
        cases Hff with Hffis Hfffi, cases Hffis with Hffi Hffs,
        apply Hfffi, exact Hffi,
    end

------iv
def setN : set ℕ := set.univ
def powN := set.powerset setN

theorem cantor : ¬ (∃ F : ℕ → set ℕ, bijectivity F) := ---ans
    begin
        intro HE_cantor,
        cases HE_cantor with F HE_cantor_F,
        let Snm : set ℕ := {n : ℕ | ¬ (n ∈ F n)},
        rw bijectivity at HE_cantor_F, cases HE_cantor_F with HE_can_F HE_tor_F, rw surjectivity at HE_tor_F, rw injectivity at HE_can_F,
        have HE_tor_F_S := HE_tor_F Snm,
        cases HE_tor_F_S with x Hx_tor_F_S,
        cases classical.em (x ∈ Snm) with HxS HxnS,
        --case HxS
            have HnxS := HxS,
            change ¬ (x ∈ F x) at HnxS,
            rw Hx_tor_F_S at HnxS,
            apply HnxS, exact HxS,
        --case HxnS
            have HyxS := HxnS,
            change ¬ ¬ (x ∈ F x) at HyxS,
            rw Hx_tor_F_S at HyxS,
            apply HyxS, exact HxnS,
    end

----part c
def G (f : X → Y) : set (X × Y) := { g | g.2 = f (g.1) }
def p1 (g : G f) : X := g.1.1

def injectivity' {X' Y' : Type u} (g : X' → Y') := ∀ x1 x2 : X', g x1 = g x2 → x1 = x2
def surjectivity' {X' Y' : Type u} (g : X' → Y') := ∀ y : Y', ∃ x : X', g x = y
def bijectivity' {X' Y' : Type u} (g : X' → Y') := injectivity' g ∧ surjectivity' g

theorem bij_p1 : @bijectivity' (↥(G f)) X (p1) := ---ans
    begin
        split,
            intros x1 x2 Hpx, rw [p1, p1] at Hpx,
            cases x1, cases x2, cases x1_val, cases x2_val,
            change x1_val_snd = f(x1_val_fst) at x1_property,
            change x2_val_snd = f(x2_val_fst) at x2_property,
            simp, simp at Hpx,
            have Hpfx : x1_val_snd = x2_val_snd, rw [x1_property, x2_property, Hpx],
            split, rw Hpx, rw Hpfx,
      --split,
            intro x,
            let xy : (↥(G f)) := ⟨⟨x,f x⟩, rfl⟩,
            existsi xy, refl,
    end

----part d
def p2 (g : G f) : Y := g.1.2

theorem bij_p2_f : @bijectivity' (↥(G f)) Y (p2) → bijectivity' f := ---ans
    begin
        intro Hp,
        cases Hp with Hpi Hps, rw injectivity' at Hpi, rw surjectivity' at Hps,
        split,
            intros a b Hfx,
            let afa : (↥(G f)) := ⟨⟨a,f a⟩, rfl⟩,
            let bfb : (↥(G f)) := ⟨⟨b,f b⟩, rfl⟩,
            have Hpab : p2 afa = p2 bfb, rw [p2, p2], simp, exact Hfx,
            have Hpiab := Hpi afa bfb Hpab, simp at Hpiab, cases Hpiab with Hab Hfab, 
            exact Hab,
      --split,
            intro y,
            have Hpsy := Hps y, cases Hpsy with xy Hpxy, 
            rw p2 at Hpxy, cases xy, cases xy_val, change xy_val_snd = y at Hpxy,
            change xy_val_snd = f xy_val_fst at xy_property,
            existsi xy_val_fst, rw [←xy_property, Hpxy],
    end
