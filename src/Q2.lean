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
