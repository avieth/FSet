module Elem

||| TODO explain.
data Elem : Type -> List Type -> Type where
  Here : Elem t (t :: ts)
  There : Elem t ts -> Elem t (r :: ts)

||| Third list is the concatenation of the first list infront of the second
||| list.
data Append : List ts -> List rs -> List ss -> Type where
  EmptyAppend : Append [] rs rs
  NonEmptyAppend : Append ts rs ss -> Append (t :: ts) rs (t :: ss)

elemConsLemma : Elem t ss -> Elem t (s :: ss)
elemConsLemma Here = There Here
elemConsLemma (There x) = There (There x)

elemAppendLemma : Elem t ts -> Append rs ts ss -> Elem t ss
elemAppendLemma Here EmptyAppend = Here
elemAppendLemma (There x) EmptyAppend = There x
elemAppendLemma Here (NonEmptyAppend x) = There (elemAppendLemma Here x)
elemAppendLemma (There x) (NonEmptyAppend y) = There (elemAppendLemma (There x) y)

||| Ins x xs ys means ys is obtained from xs by inserting x somewhere (in ys).
data Ins : t -> List t -> List t -> Type where
  InsHead : Ins t ts (t :: ts)
  InsTail : Ins t ts ts' -> Ins t (x :: ts) (x :: ts')

prop1 : (n = m) -> ((S n) = (S m))
prop1 Refl = Refl

||| A lemma to get familiar with Ins: ys is always 1 longer than xs.
lemma1 : Ins x xs ys -> ((1 + length xs) = length ys)
lemma1 InsHead = Refl
lemma1 (InsTail t) = prop1 (lemma1 t)

||| If x is inserted into xs to obtain ys, then surely x is in ys.
||| The proof is simple enough: either ys = (x :: xs) in the InsHead case,
||| in which case Here is the proof; otherwise ys = (z :: xs') where x is
||| somewhere in xs', so we use There and recurse.
lemma2 : Ins x xs ys -> Elem x ys
lemma2 InsHead = Here
lemma2 (InsTail y) = There (lemma2 y)

||| Inserting x into xs does not remove any elements of xs.
lemma3 : Ins x xs ys -> Elem t xs -> Elem t ys
lemma3 InsHead Here = There Here
lemma3 InsHead (There elem) = There (There elem)
-- ^ If we find an InsHead then we know that the inserted element x is
--   placed before the already-present element t, so we add a There in front.
lemma3 (InsTail ins) Here = Here
-- ^ If we encounter an InsTail and a Here then we know that the inserted
--   element x is placed behind the element t (closer to the tail), so the
--   Elem proof remains the same.
lemma3 (InsTail ins) (There elem) = There (lemma3 ins elem)
-- ^ The recursive case: we have encountered neither the end of the Elem
--   proof, nor the end of the Ins proof. ins and elem are each proofs about
--   the tail of xs, so throwing a There in front of the recursive call is
--   just what we need.

data Perm : List t -> List t -> Type where
  PNil : Perm [] []
  PCons : Ins t ss ss' -> Perm ts ss -> Perm (t :: ts) ss'
  -- ^ If ts is a permutation of ss, and ss' is obtained from ss by inserting
  --   t somewhere, then (t :: ts) is a permutation of ss'
  --   Read it like this: we build up the first list, at each step inserting
  --   the new head somewhere into the second list.

||| A very useful fact: permuting a list does not change membership!
theorem1 : Perm ts ss -> Elem t ts -> Elem t ss
theorem1 (PCons ins perm) Here = lemma2 ins
-- ^ In this case we have  ins : Ins t ss ss' so lemma2 proves
--   Elem t ss' and we're done!
theorem1 (PCons ins perm) (There elem) = lemma3 ins (theorem1 perm elem)
-- ^ TODO so difficult to give an intuitive explanation of this proof.
--   Must study it some more.

permComm : Perm ts ss -> Perm ss ts
permComm PNil = PNil
permComm (PCons InsHead perm) = PCons InsHead (permComm perm)
permComm (PCons (InsTail ins) perm) = ?permComm_rhs_2
