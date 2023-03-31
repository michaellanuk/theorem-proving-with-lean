-- The program below proves that the closed-form equation for the sum of the first 
-- n natural numbers is given by:
--
-- (n * (n + 1))/2

import tactic

def sum_of_first_n_nat : ℕ → ℕ
| 0 := 0
| (nat.succ n) := (nat.succ n) + sum_of_first_n_nat n

theorem closed_eq_sum_of_first_n_nat (n : ℕ) :
    2 * (sum_of_first_n_nat n) = n * (nat.succ n) :=

begin
  induction n with d hd,

  -- rewrite base case
  rw sum_of_first_n_nat,

  -- basic theorems nat.mul_zero for n * 0 = 0, and nat.zero_mul for 0 * n = 0:
  rw nat.mul_zero,
  rw nat.zero_mul,
  -- base case is proved

  -- generalise
  rw sum_of_first_n_nat,

  rw nat.left_distrib,

  rw hd,

  -- ring tactic to equate both sides
  ring
end