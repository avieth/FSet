{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances #-}
-- Incoherent instances used for IxEither... is this ok?
-- Maybe! I think the issue is that a t can appear more than once in a list
-- ts, and so there really isn't a way to disambiguate the CElem choice.
-- But that should be fine... we don't care where in the list the thing is
-- found, so long as it's found.
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RebindableSyntax #-}

import Prelude hiding (return, (>>=), (>>))
import Data.Proxy
import Data.Type.Equality
import Data.TypeNat.Nat

class CElem (t :: k) (ts :: [k]) where
  celemFind
    :: (forall r rs . b (r ': rs) -> a t rs -> a t (r ': rs))
    -> (forall rs . b (t ': rs) -> a t (t ': rs))
    -> (forall r rs . b (r ': rs) -> b rs)
    -- ^ Decompose some indexed value.
    -> b ts
    -- ^ Initial value indexed by the type list.
    -> a t ts

-- The following two instances overlap for 
--
--   t (t ': ts)
--
-- I think using OverlappingInstances is OK though, since I believe
-- this is more specific than
--
--   t (r ': ts)
--
-- and so the former will be chosen!
instance CElem t (t ': ts) where
  celemFind ifThere ifHere simplify x = ifHere x

instance (CElem t ts) => CElem t (r ': ts) where
  celemFind ifThere ifHere simplify x =
    ifThere x (celemFind ifThere ifHere simplify (simplify x))

data TList :: [*] -> * where
  EmptyTList :: TList '[]
  ConsTList :: t -> TList ts -> TList (t ': ts)

tailTList :: TList (t ': ts) -> TList ts
tailTList tlist = case tlist of
  ConsTList _ rest -> rest

-- How come skolem ain't escaping here?
headTList :: TList (t ': ts) -> t
headTList tlist = case tlist of
  ConsTList x _ -> x

-- Skolem ain't escaping here either...
findTList :: TList (t ': ts) -> FindT t (t ': ts)
findTList tlist = case tlist of
  ConsTList x _ -> FindT x

data FindT t ts = FindT t

unFindT :: FindT t ts -> t
unFindT (FindT x) = x

findT' :: forall t ts . CElem t ts => TList ts -> FindT t ts
findT' tlist = celemFind ifThere ifHere tailTList tlist
  where
    ifHere = findTList
    {-
     - Why can't we do this?!? instead of using findTList????
     - BUG???
    ifHere tlist = case tlist of
      ConsTList x _ -> undefined -- FindT x
    -}
    ifThere _ (FindT x) = (FindT x)

findT :: forall t ts . CElem t ts => TList ts -> t
findT tlist = unFindT (findT' tlist)

test = ConsTList True (ConsTList () (ConsTList "Hello" EmptyTList))

q :: ()
q = findT test

-- Trouble with skolem type variables, untouchables, etc. What if we store
-- the type of the head of the list?
-- Nope, resolved that; this is an abandonned attempt
{-
data HTList :: * -> [*] -> * where
  EmptyHTList :: HTList t '[]
  ConsHTList :: t -> HTList s ts -> HTList t (t ': ts)

tailHTList :: HTList t (t ': s ': ts) -> HTList s (s ': ts)
tailHTList tlist = case tlist of
  ConsHTList _ rest -> rest


findHT :: CElem t ts => HTList t' ts -> FindT t ts
findHT htlist = celemFind ifThere ifHere tailHTList htlist
  where
    ifHere htlist = case htlist of
      ConsHTList _ _ -> FindT undefined
    ifThere _ (FindT x) = (FindT x)
-}

-- Order is important if we wish to use celemFind ! Must place the list as
-- the last argument.
data FList :: * -> [*] -> * where
  EmptyFList :: FList r '[]
  -- TODO False ~ Elem t ts constraint to make it a set.
  ConsFList :: (t -> r) -> FList r ts -> FList r (t ': ts)

tailFList :: forall r t ts . FList r (t ': ts) -> FList r ts
tailFList flist = case flist of
  ConsFList _ rest -> rest

data FindF r t ts = FindF (t -> r)

unFindF :: FindF r t ts -> (t -> r)
unFindF findf = case findf of
  FindF f -> f

findFList :: FList r (t ': ts) -> FindF r t (t ': ts)
findFList flist = case flist of
  ConsFList f _ -> FindF f

findF' :: forall r t ts . CElem t ts => FList r ts -> FindF r t ts
findF' flist = celemFind ifThere ifHere tailFList flist
  where
    ifHere = findFList
    ifThere _ (FindF f) = (FindF f)

findF :: forall r t ts . CElem t ts => FList r ts -> (t -> r)
findF = unFindF . findF'

exampleFList = ConsFList f1 (ConsFList f2 (ConsFList f3 EmptyFList))
  where
    f1 :: Int -> String
    f1 = show
    f2 :: Bool -> String
    f2 = show
    f3 :: String -> String
    f3 = (++) "It works! "

data OneOf :: [*] -> * where
  ThisOne :: CElem t ts => t -> OneOf ts

applyFList :: FList r ts -> OneOf ts -> r
applyFList flist oneof = case oneof of
  ThisOne x -> findF flist $ x

exampleOneOf1 :: OneOf '[Int, Bool, String]
exampleOneOf1 = ThisOne True

exampleOneOf2 :: OneOf '[Int, Bool, String]
exampleOneOf2 = ThisOne "foobar"

-- NEW IDEA: Append datatype.
data MyList a = MyNil | MySingle a | MyAppend (MyList a) (MyList a)

class MyElem (a :: k) (b :: MyList k)
instance MyElem x (MySingle x)
-- How to avoid these _duplicate_ instances???
--instance MyElem x xs => MyElem x (MyAppend xs ys)
--instance MyElem x xs => MyElem x (MyAppend ys xs)
--instance MyElem x xs => MyElem x (MyAppend xs ys)
--instance MyElem y ys => MyElem y (MyAppend xs ys)

class Representative (rs :: [k]) (ts :: [k])
instance Representative '[] '[]
instance Representative rs ts => Representative (r ': rs) (r ': ts)
instance (Representative rs ts, CElem t ts) => Representative rs (t ': ts)

want :: (Representative rs ts, CElem t ts) => FList r rs -> (t -> r)
want = undefined

--instance (CElem x ss, Representative ts ss) => CElem x ts

{- Indexed Either Section -}

data IxEither ts a where
  IxLeft :: OneOf ts -> IxEither ts a
  IxRight :: a -> IxEither ts a

-- TODO Should be able to give just a representative set.
-- But how to code that to GHC?
runIxEither :: FList r ts -> (a -> r) -> IxEither ts a -> r
runIxEither flist f ixe = case ixe of
  IxRight x -> f x
  IxLeft oneof -> applyFList flist oneof

data IxEitherS t a where
  IxLeftS :: t -> IxEitherS t a
  IxRightS :: a -> IxEitherS t a

ixEitherSLift :: IxEitherS t a -> IxEither '[t] a
ixEitherSLift ixes = case ixes of
  IxRightS x -> IxRight x
  IxLeftS y -> IxLeft (ThisOne y)

ixMap :: (a -> b) -> IxEither ts a -> IxEither ts b
ixMap f ixe = case ixe of
  IxRight x -> IxRight (f x)
  IxLeft y -> IxLeft y

ixPure :: a -> IxEither ts a
ixPure x = IxRight x

ixAp :: IxEither ts (a -> b) -> IxEitherS t a -> IxEither (t ': ts) b
ixAp ixe ixes = case ixe of
  IxRight f -> case ixes of
    IxRightS x -> IxRight (f x)
    IxLeftS y -> IxLeft (ThisOne y)
  IxLeft oneof -> case oneof of
    ThisOne y -> IxLeft (ThisOne y)

ixBind :: IxEitherS t a -> (a -> IxEither ts b) -> IxEither (t ': ts) b
ixBind ixes k = case ixes of
  IxLeftS y -> IxLeft (ThisOne y)
  IxRightS x -> case k x of
    IxRight x' -> IxRight x'
    IxLeft (ThisOne y') -> IxLeft (ThisOne y')

ixNext :: IxEither ts a -> IxEitherS t b -> IxEither (t ': ts) b
ixNext ixe = ixAp (ixMap (flip const) ixe)

(>>=) = ixBind
(>>) = ixNext
return = ixPure

data SillyError = Kaboom
data SeriousError = Blast

exampleIx1 :: IxEitherS SillyError (Int -> Int -> Int)
exampleIx1 = IxLeftS Kaboom

exampleIx2 :: IxEitherS SeriousError Int
exampleIx2 = IxLeftS Blast

exampleIx3 :: Int -> IxEither ts Int
exampleIx3 i = ixPure (i + 1)

exampleIx4 :: IxEitherS SillyError Bool
exampleIx4 = IxRightS True

exampleIx = (ixEitherSLift exampleIx1) `ixAp` exampleIx2 `ixAp` exampleIx2

exampleIx' = exampleIx2 `ixBind` exampleIx3

exampleIx'' = do
  x <- exampleIx2
  exampleIx3 x
  exampleIx4
