data Vectt : Type -> Nat -> Type where
  NilVectt : Vectt t Z
  ConsVectt : t -> Vectt t n -> Vectt t (S n)

listToVectt : List t -> (n : Nat) -> Maybe (Vectt t n)
listToVectt [] Z = Just (NilVectt)
listToVectt (x :: xs) Z = Nothing
listToVectt (x :: xs) (S n) = case listToVectt xs n of
  Just v => Just (ConsVectt x v)
  Nothing => Nothing

data TVect : List Type -> Type where
  NilTVect : TVect []
  ConsTVect : t -> TVect ts -> TVect (t :: ts)

data Elem : Type -> List Type -> Type where
  Here : Elem t (t :: ts)
  There : Elem t ts -> Elem t (r :: ts)

findTVect' : Elem t ts -> TVect ts -> t
findTVect' Here (ConsTVect s _) = s
findTVect' (There there) (ConsTVect _ tvect) = findTVect' there tvect

findTVect : {auto el : Elem t ts} -> TVect ts -> t
findTVect {el} tvect = findTVect' el tvect
-- NB this one wouldn't work.
--findTVect {el} tvect = findTVect' (proof { intros; trivial }) tvect

exampleTVect : TVect [Bool, (), Int]
exampleTVect = ConsTVect True (ConsTVect () (ConsTVect 1 NilTVect))

getBool : Bool
getBool = findTVect exampleTVect

getByTypeT : (ty : Type) -> {auto el : Elem ty ts} -> TVect ts -> ty
getByTypeT t {el} tvect = findTVect' el tvect

data FVect : List Type -> Type -> Type where
  NilFVect : FVect [] r
  ConsFVect : (t -> r) -> FVect ts r -> FVect (t :: ts) r

findFVect' : Elem t ts -> FVect ts r -> (t -> r)
findFVect' Here (ConsFVect f _) = f
findFVect' (There there) (ConsFVect _ fvect) = findFVect' there fvect

getByTypeF : (ty : Type) -> {auto el : Elem ty ts} -> FVect ts r -> (ty -> r)
getByTypeF t {el} fvect = findFVect' el fvect

exampleFVect : FVect [Bool, (), Int] Int
exampleFVect = ConsFVect ifBool (ConsFVect ifUnit (ConsFVect ifInt NilFVect))

  where

    ifBool : Bool -> Int
    ifBool True = 0
    ifBool False = 1

    ifUnit : () -> Int
    ifUnit _ = 2

    ifInt : Int -> Int
    ifInt = (+) 1

data OneOf : List Type -> Type where
  ThisOne : Elem t ts -> t -> OneOf ts

exampleOneOf : OneOf [Bool, (), Int]
exampleOneOf = ThisOne Here True

handle : FVect ts r -> OneOf ts -> r
handle fvect (ThisOne el x) = findFVect' el fvect $ x

-- There we have it!
-- Improvements:
--   Would be cool if we didn't have to have the same order of ts.
--     handle : FVect ts r -> OneOf (Perm ts ts') -> r

||| Ins x xs ys means ys is obtained from xs by inserting x somewhere (in ys).
data Ins : t -> List t -> List t -> Type where
  InsHead : Ins t ts (t :: ts)
  InsTail : Ins t ts ts' -> Ins t (x :: ts) (x :: ts')

prop1 : (n = m) -> ((S n) = (S m))
prop1 Refl = Refl

--prop2 : ((S (Prelude.List.length xs)) = (Prelude.List.length ys)) -> ((S (S (Prelude.List.length xs))) = (S (Prelude.List.length ys)))
--prop2 = prop1

||| A lemma to get familiar with Ins: ys is always 1 longer than xs.
lemma1 : Ins x xs ys -> ((1 + length xs) = length ys)
lemma1 InsHead = Refl
lemma1 (InsTail t) = prop1 (lemma1 t)

||| If (y :: ys) is obtained from xs by inserting x, then (x :: xs) is
||| obtained from ys by inserting y
insComm : Ins x xs (y :: ys) -> Ins y ys (x :: xs)
insComm InsHead = InsHead
-- ^ This works because if InsHead, ys = xs and x = y
insComm (InsTail t) = ?dunno --InsTail (insComm t)
-- ^ For InsTail, how can we show it? In this case we know that
--     t            ~> x
--     (x :: ts)    ~> xs
--     (x :: ts')   ~> (y :: ys)
--     t : t ts ts' ~> t : x (tail xs) ys
--
--     insComm t : Ins (head ys) 

data Perm : List t -> List t -> Type where
  PNil : Perm [] []
  PCons : Ins t ss ss' -> Perm ts ss -> Perm (t :: ts) ss'
  -- ^ If ts is a permutation of ss, and ss' is obtained from ss by inserting
  --   t somewhere, then (t :: ts) is a permutation of ss'
  --   Read it like this: we build up the first list, at each step inserting
  --   the new head somewhere into the second list.

permX_X : Perm [x] [x]
permX_X = PCons InsHead PNil

perm12_21 : Perm [1,2] [2,1]
perm12_21 = PCons (InsTail InsHead) permX_X

foo : (xs : List t) -> (ys : List t) -> {auto pe : Perm xs ys} -> ()
foo xs ys {pe} = ()

foo' : ()
foo' =
  foo
    [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28]
    [28,27,26,25,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1]

--perm123_231 : Perm [1,2,3] [2,3,1]
--perm123_231 = PCons (InsTail (InsTail InsHead)) (PCons InsHead (PCons InsHead PNil))

||| Theorem: Perm is commutative.
permComm : Perm ts ss -> Perm ss ts
permComm PNil = PNil
{-
permComm (PCons perm ins) = case ins of
  InsHead => PCons (permComm perm) ( )
  InsTail ins' => PCons (permComm perm) ( )
-}

--theorem1 : Perm ts ss -> (Elem t ts -> Elem t ss)