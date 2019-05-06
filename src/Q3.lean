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
--import analysis.polynomial
--import analysis.exponential
import data.nat.choose

/-

M1F May exam 2018, question 3.

Solutions by Abhimanyu Pallavi Sudhir,
part (d) generalised to all types of size 2 by KMB

-/


universe u
local attribute [instance, priority 0] classical.prop_decidable

--QUESTION 3

variable {S : Type u}

-- Q3(a)(i)
-- answer
variable (binary_relation : S → S → Prop)

local infix ` ~ `:1000 := binary_relation

-- Q3(a)(ii)
def reflexivity := ∀ x, x ~ x
def symmetry := ∀ (x y), x ~ y → y ~ x
def transitivity := ∀ (x y z), x ~ y → y ~ z → x ~ z
-- answer
def is_equivalence := reflexivity binary_relation ∧ symmetry binary_relation ∧ transitivity binary_relation

-- Q3(a)(iii)
variable {binary_relation}
-- answer
def cl (h : is_equivalence binary_relation) (a : S) : set S := { x | x ~ a }

-- Q3(b)
theorem classes_injective2 (h : is_equivalence binary_relation) (a b : S) :
  (cl h a = cl h b) ∨ (cl h a ∩ cl h b) = ∅ :=
-- answer
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

-- Q3(c)

inductive double_cosets : ℤ → ℤ → Prop
    | cond1 : ∀ x, double_cosets x (x + 3)
    | cond2 : ∀ x, double_cosets x (x - 5)
    | condT : ∀ x y z, double_cosets x y → double_cosets y z → double_cosets x z -- transitivity
local infix ` ⋆ `:1001 := double_cosets

theorem double_cosets_reflexive : reflexivity double_cosets :=
---answer
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

-- Q3(d) preparation

-- first prove the result for `bool`, a concrete set with two elements
theorem trans_of_refl_aux (r : bool → bool → Prop) (hr : reflexivity r) : transitivity r :=
begin
  rw transitivity,
  intros x y z,
  have Hxyyzzx : x = y ∨ y = z ∨ z = x,
    cases x; cases y; cases z; simp,
  rcases Hxyyzzx with rfl | rfl | rfl,
  { intros h hxz, exact hxz},
  { intros hxy h, exact hxy},
  { intros h1 h2, exact hr z}
end

-- now deduce it for an arbitrary set with two elements
#check trunc
variable [fintype S]
theorem trans_of_refl (h : fintype.card S = 2) (r : S → S → Prop) (hr : reflexivity r) : transitivity r :=
begin
  have Heq : S ≃ bool,
  { have h1 := trunc.out (fintype.equiv_fin S),
    rw h at h1,
    have h2 := trunc.out (fintype.equiv_fin bool),
    rw fintype.card_bool at h2,
    exact h1.trans h2.symm,
  },
  -- transport
  sorry
end



