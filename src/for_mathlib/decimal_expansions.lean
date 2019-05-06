import data.real.basic
import algebra.archimedean
import tactic.norm_num 

variables {β : Type} [linear_ordered_ring β] [floor_ring β]

namespace decimal 

section 
parameters {α : Type} [linear_ordered_ring α] [floor_ring α]
-- ⌊(real.sqrt 2 : ℝ)⌋

definition expansion_aux (r : α) : ℕ → α
| 0 := (r - floor r) * 10
| (n + 1) := (expansion_aux n - floor (expansion_aux n)) * 10

definition expansion_nonneg (r : α) : ℕ → ℕ
| 0 := int.to_nat (floor r)
| (n + 1) := int.to_nat (floor (expansion_aux r n))

lemma expansion_aux_is_zero (n : ℕ) (r : α) : expansion_aux r n = 0 → ∀ m, expansion_aux r (n + m) = 0 :=
begin
intros H m,induction m with d Hd,assumption,
show expansion_aux r (nat.succ (n + d)) = 0,
unfold expansion_aux,rw Hd,simp,
end

lemma int.succ_le_of_lt (a b : ℤ) : a < b → int.succ a ≤ b := id

@[simp] theorem rat.cast_floor
  {α} [linear_ordered_field α] [archimedean α] (x : ℚ) :
  by haveI := archimedean.floor_ring α; exact ⌊(x:α)⌋ = ⌊x⌋ :=
begin
  haveI := archimedean.floor_ring α,
  apply le_antisymm,
  { rw [le_floor, ← @rat.cast_le α, rat.cast_coe_int],
    apply floor_le },
  { rw [le_floor, ← rat.cast_coe_int, rat.cast_le],
    apply floor_le }
end

lemma floor_of_bounds (r : α) (z : ℤ) :
  ↑z ≤ r ∧ r < (z + 1) ↔ ⌊ r ⌋ = z :=
by rw [← le_floor, ← int.cast_one, ← int.cast_add, ← floor_lt,
  int.lt_add_one_iff, le_antisymm_iff, and.comm]

end

end decimal
