import tactic.norm_num
/-

M1F May exam 2018, question 4.

Solutions by Abhimanyu Pallavi Sudhir,

-/

universe u
local attribute [instance, priority 0] classical.prop_decidable

--QUESTION 4
variable {X : Type u}
variable {Y : Type u}
variable {f : X → Y}

-- Q4(a)(i)
def injectivity (g : X → Y) := ∀ x1 x2 : X, g x1 = g x2 → x1 = x2

-- Q4(a)(ii)
def surjectivity (g : X → Y) := ∀ y : Y, ∃ x : X, g x = y

-- Q4(a)(iii)
def bijectivity (g : X → Y) := injectivity g ∧ surjectivity g

-- Q4(b)(i) example
def f1 : ℕ → ℕ
    | n := n + 2

-- Q4(b)(i) proof
theorem injection : ∃ f : ℕ → ℕ, injectivity f ∧ ¬ surjectivity f :=
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

-- Q4(b)(ii) example; note that 
def f2 : ℕ → ℕ
    | n := n / 2

-- Q4(b)(ii) proof
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

-- Q4(b)(iii) proof
theorem bijections_are_injections : (∃ f : ℕ → ℕ, bijectivity f ∧ ¬ injectivity f) → false := ---ans
    begin
        intro Hf,
        cases Hf with f Hff,
        rw bijectivity at Hff,
        cases Hff with Hffis Hfffi, cases Hffis with Hffi Hffs,
        apply Hfffi, exact Hffi,
    end

-- Q4(b)(iv) proof
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

-- Q4(c)
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

-- Q4(d)
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
