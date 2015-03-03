import Elem

||| Proof that every element in the second list is an element of the
||| first list! There may be things in the first list not in the second
||| list.
data WeakRepresentative : List ts -> List rs -> Type where
  WeakRepEmpty : WeakRepresentative ts []
  WeakRepCons : Elem x ts -> WeakRepresentative ts rs -> WeakRepresentative ts (x :: rs)

||| Proof that every element in the second list is an element of the
||| first list! The first list map not be longer than the second list, but it
||| could nevertheless contain duplicates.
data StrongRepresentative : List ts -> List rs -> Type where
  StrongRepEmpty : StrongRepresentative [] []
  StrongRepIns : Ins x rs rs' -> StrongRepresentative ts rs -> StrongRepresentative (x :: ts) rs'
  StrongRepElem : Elem x rs -> StrongRepresentative ts rs -> StrongRepresentative ts (x :: rs)

weakRepElemTheorem : WeakRepresentative ts ss -> Elem t ss -> Elem t ts
weakRepElemTheorem (WeakRepCons elem weakRep) Here = elem
weakRepElemTheorem (WeakRepCons elem weakRep) (There x) = weakRepElemTheorem weakRep x

strongRepElemTheorem : StrongRepresentative ts ss -> Elem t ss -> Elem t ts
strongRepElemTheorem (StrongRepIns ins strongRep) Here = ?dunno1
strongRepElemTheorem (StrongRepIns ins strongRep) (There x) = ?dunno2
strongRepElemTheorem (StrongRepElem elem strongRep) Here = ?dunno3
strongRepElemTheorem (StrongRepElem elem strongRep) (There x) = ?dunno4
