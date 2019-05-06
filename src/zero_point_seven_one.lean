import for_mathlib.decimal_expansions

open decimal

noncomputable definition s : ℝ := (71/100 : ℝ)

theorem sQ : s = ((71/100:ℚ):ℝ) := by unfold s;norm_num 

theorem floor_s : floor s = 0 := 
by rw [← floor_of_bounds, s, int.cast_zero]; norm_num

theorem floor_10s : floor (71/10 : ℝ) = 7 :=
begin 
rw [← floor_of_bounds],
split; norm_num
end 

lemma expansion_auxing_s : expansion_aux s 2 = 0 :=
begin
unfold expansion_aux,
rw floor_s,
unfold s,
norm_num,
rw floor_10s,
norm_num,
end 


theorem expansion_auxed (n : ℕ) : expansion_aux s (n + 2) = 0 :=
begin
induction n with d Hd,exact expansion_auxing_s,
rw expansion_aux.equations._eqn_2,
rw Hd,
simp,
end

-- recall s = 71/100 
theorem no_eights_in_0_point_71 (n : ℕ) : decimal.expansion_nonneg s n ≠ 8 :=
begin
cases n,unfold expansion_nonneg,rw floor_s,show 0 ≠ 8,by cc,
cases n,unfold expansion_nonneg expansion_aux,rw floor_s,unfold s,
  rw int.cast_zero,
  have this : ((71 / 100 : ℝ) - 0) * 10 = 71 / 10 := by norm_num,
  rw this,rw floor_10s,show 7 ≠ 8,by cc,
cases n,unfold expansion_nonneg expansion_aux,rw floor_s,unfold s,
  rw int.cast_zero,
  norm_num,
  rw floor_10s,
  norm_num,
  show 1 ≠ 8,
  by cc,
unfold expansion_nonneg,
rw [expansion_auxed,floor_zero],
show 0 ≠ 8,
by cc,
end 

