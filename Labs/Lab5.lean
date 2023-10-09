import Mathlib.Tactic 

namespace Lab5


-- All proofs are essentially the same: the base case is true definitionally,
-- and for the inductive case, perform one step of definitional simplification,
-- then rewrite the induction hypothesis (there is usually some meaningless 
-- unfolding of wrappers to be done at this stage, since I have stuff defined 
-- as theorems over some function f, which is in turn defined as f = g for some g)
-- and then again what follows is true reflexively

inductive BinTree (α : Type _) where
| leaf (a : α)
| node (left : BinTree α) (right : BinTree α) 
deriving Repr, BEq


open BinTree

-- Exercise 2a

def mapBin {α β : Type _} (f : α → β) (t : BinTree α) : BinTree β :=
  match t with
  | (leaf a) => leaf (f a)
  | (node tL tR) => node (mapBin f tL) (mapBin f tR)

instance : Functor BinTree where
  map := mapBin

theorem mapId {α : Type _}: mapBin (id : α → α) = id := by
  ext t
  induction' t with val nL nR IHpL IHpR
  · --simp only [mapBin, id]
    rfl
  · rw [mapBin]
    rw [IHpL, IHpR]
    simp only [id]

theorem mapComp {α β γ : Type _}  {f : β → γ} {g : α → β} : 
  ∀ t : BinTree α,mapBin (f ∘ g) t = mapBin f (mapBin g t) := by
  intro t
  induction' t with val nL nR IHpL IHpR
  · --simp only [mapBin]
    rfl
  · simp only [mapBin]
    rw [IHpL, IHpR]

-- Exercise 2.c

def bindBinTree  {α β : Type _} (t : BinTree α) (f : α → BinTree β): BinTree β :=
match t with
  | (leaf a) => f a
  | node tL tR => node (bindBinTree tL f) (bindBinTree tR f)

instance : Monad BinTree where
  pure := leaf
  bind := bindBinTree


theorem left_id {α β : Type _} {h : α → BinTree β} : ∀a : α, (pure a) >>= h = h a := by
  intro a
  -- simp only [pure]
  -- simp only [bind, bindBinTree]
  rfl

theorem right_id {α : Type _} : ∀m : BinTree α, m >>= pure = m := by
  intro m
  induction' m with val nL nR IHpL IHpR
  · rfl
  · simp only [bind, bindBinTree]
    simp only [bind, bindBinTree] at IHpL IHpR
    rw [IHpR, IHpL]

theorem assoc {α β : Type _} {g : α → BinTree β}{h : β → BinTree γ} : ∀ m : BinTree α, ((m >>= g) >>= h) = (m >>= (fun x ↦ g x >>= h)) := by 
  intro m
  induction' m with val nL nR IHpL IHpR
  · rfl
  · simp only [bind, bindBinTree]
    simp only [bind, bindBinTree] at IHpL IHpR
    rw [IHpR, IHpL]






end Lab5