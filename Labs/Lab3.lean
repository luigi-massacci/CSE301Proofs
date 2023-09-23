import Std.Data.List.Basic
import Mathlib.Tactic

-- Note: placing the vertical bar before a tactic will display the proof state
--       before the tactic is executed

namespace Lab3
section Lab3

-- Assume that the list elements come from some type with monoid structure
variable {α : Type _} [Monoid α]

-- calling the monoid operation and unit f and v to have the same notation
def f : α → α → α  := (· * · )
def v := (1 : α)


-- these are just for comfort so that the simplifier will reduce identities
-- involving f and v as well as unfolding computations
@[simp]
lemma left_unit : ∀ e : α, f v e = e := by
  intro e
  unfold f v
  rw [one_mul] -- the name of the theorem that in a monoid 1*m = m

@[simp]
lemma right_unit : ∀ e : α, f e v = e := by
  intro e
  unfold f v
  rw [mul_one]

lemma f_assoc : ∀ a b c : α, f (f a b) c  = f a (f b c):= by
  intro a b c
  unfold f
  rw [mul_assoc] -- monoid associativity

open List


-- The definitions of foldr and foldr for clarity.
-- def List.foldl {α : Type u} {β : Type v} (f : α → β → α) : (init : α) → List β → α
--   | a, nil      => a
--   | a, cons b l => foldl f (f a b) l

-- def foldr (f : α → β → β) (init : β) : List α → β
--   | []     => init
--   | a :: l => f a (foldr f init l)

-- The technical lemma for the proof: the key is to quantify over the seed
-- so it is free in the first induction hypothesis, followed by a second
-- induction over the tail of the initial list to get a second element
-- for associativity.
theorem foldl_unit (as : List α) : ∀a : α, foldl f a as = f a (foldl f v as) := by
  --naming the various variables resulting from the induction
  induction' as with a₁ tail IHp
  · intro a
    -- the case of the empty list is just unfolding definitions
    simp only [foldl, right_unit]
  · intro a
    simp only [foldl, left_unit]
    induction' tail with a₂ tail IHp₂
    · simp only [foldl]
    · simp only [foldl]
      simp only [foldl, left_unit] at IHp
      --first use of the induction hp to rewrite the LHS of our desired equation
      rw [IHp (f a a₁)] -- specialize IHp so that it matches the goal
      -- now the RHS
      rw [f_assoc, IHp a₁]

theorem foldl_eq_foldr (l : List α) : foldl f v l = foldr f v l := by
  induction' l with h tail IHp
  · simp only [foldl, foldr] -- empty list is just unfolding definitions
  · simp only [foldl, left_unit, foldr] -- more unfolding of definitions
  -- the arrow means to try to match the goal with the RHS of IHp (default is LHS)
    rw [← IHp]
    apply foldl_unit


end Lab3
end Lab3