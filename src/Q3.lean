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

universe u
local attribute [instance, priority 0] classical.prop_decidable


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
