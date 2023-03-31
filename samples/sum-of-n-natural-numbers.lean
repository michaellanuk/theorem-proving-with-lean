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
	-- the below directive indicates that by induction we have 2 goals:
	-- 1 for the base case when n = 0, and 1 for the general case for n > 0
  induction n with d hd,

  -- the rewrite tactic modifies our proof goal according to an existing
	-- definition or equation. Here, we can rewrite sum_of_first_n_nat 0 to
	-- its value by definition (0):
  rw sum_of_first_n_nat,

  -- basic theorems nat.mul_zero for n * 0 = 0, and nat.zero_mul for 0 * n = 0:
  rw nat.mul_zero,
  rw nat.zero_mul,
  -- base case is proved

  -- generalise
  rw sum_of_first_n_nat,

	-- multiply out left side
  rw nat.left_distrib,

	-- rewrite our inductive hypothesis to acquire a correct equation
	-- but one that still needs extra algebraic manipulation.
  rw hd,

  -- ring tactic can be used in-place of line-by-line multiplications.
	-- This tells Lean to intelligently search through basic equalities
	-- underpinning the natural numbers in an attempt to make both sides
	-- of the equation equal.
  ring
end