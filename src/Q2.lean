import data.real.basic

import for_mathlib.decimal_expansions
import zero_point_seven_one -- "obvious" proof that 0.71 has no 8's in decimal expansion!
/-

M1F May exam 2018, question 2.

-/

universe u
local attribute [instance, priority 0] classical.prop_decidable

-- Q2(a)(i)
def ub (S : set ℝ) (x : ℝ) := ∀ s ∈ S, s ≤ x ---ans

-- Q2(a)(ii)
-- iba: is bounded above
def iba (S : set ℝ) := ∃ x, ub S x ---ans

-- Q2(a)(iii)
def lub (S : set ℝ) (b : ℝ) := ub S b ∧ ∀ y : ℝ, (ub S y → b ≤ y) ---ans

-- Q2(b)
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
            existsi x, exact Hlub.left,
    end

-- Q2(c)(i) preparation
def S1 := {x : ℝ | x < 59}

lemma between_bounds (x y : ℝ) (H : x < y) : x < (x + y) / 2 ∧ (x + y) / 2 < y := 
⟨by linarith, by linarith⟩

-- Q2(c)(i)
theorem S1_lub : lub S1 59 := ---ans
    begin
        split,
            intro, change (s < 59 → s ≤ 59), exact le_of_lt,
        intro y, change ((∀ (s : ℝ), s < 59 → s ≤ y) → 59 ≤ y), intro Hbub,
        apply le_of_not_gt, intro Hbadub,
        have Houtofbounds := between_bounds y 59 Hbadub,
        apply not_le_of_gt Houtofbounds.1 (Hbub ((y + 59) / 2) Houtofbounds.2),
    end

-- Q2(c)(ii) preparations

definition S2 : set ℝ := {x | 7/10 < x ∧ x < 9/10 ∧ 
  ∀ n : ℕ, decimal.expansion_nonneg x n ≠ 8}

lemma S2_nonempty_and_bounded : (∃ s : ℝ, s ∈ S2) ∧ ∀ (s : ℝ), s ∈ S2 → s ≤ 9/10 :=
begin
  split,
  { -- 0.71 ∈ S
    use (71 / 100 : ℝ),
    split, norm_num, split, norm_num,
    exact no_eights_in_0_point_71
  },
  rintro s ⟨hs1, hs2, h⟩,
  exact le_of_lt hs2 
end

-- Q2(c)(ii)
theorem S2_has_lub : ∃ b : ℝ, lub S2 b :=
begin
  cases S2_nonempty_and_bounded with Hne Hbd,
  have H := real.exists_sup S2 Hne ⟨(9/10 : ℝ), Hbd⟩,
  cases H with b Hb,
  use b,
  split,
  { intros s2 Hs2,
    exact (Hb b).mp (le_refl _) s2 Hs2, 
  },
  { intros y Hy,
    exact (Hb y).mpr Hy,
  }
end 

-- Q2(d)(i)
theorem ublub_the_first (S : set ℝ) (b : ℝ) (hub : ub S b) (hin : b ∈ S) : lub S b := ---ans
    begin
        split,
            exact hub,
            intros y huby,
            exact huby b hin,
    end

-- Q2(d)(ii)
theorem adlub_the_second (S T : set ℝ) (b c : ℝ) (hlubb : lub S b) (hlubc : lub T c) ---ans
: lub ({x : ℝ | ∃ s t : ℝ, s ∈ S ∧ t ∈ T ∧ x = s + t}) (b + c) :=
    begin
        split,
            unfold ub, simp, intros x s hss t htt hxst, rw hxst,
            apply add_le_add (hlubb.1 s hss) (hlubc.1 t htt),
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
