import Elem
import Representative

data TVect : List Type -> Type where
  NilTVect : TVect []
  ConsTVect : t -> TVect ts -> TVect (t :: ts)

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

oneOfAppendLemmaRight : OneOf ts -> Append rs ts ss -> OneOf ss
oneOfAppendLemmaRight (ThisOne elem x) app = ThisOne (elemAppendLemmaRight elem app) x

oneOfAppendLemmaLeft : OneOf ts -> Append ts rs ss -> OneOf ss
oneOfAppendLemmaLeft (ThisOne elem x) app = ThisOne (elemAppendLemmaLeft elem app) x

exampleOneOf1 : OneOf [Bool, (), Int]
exampleOneOf1 = ThisOne Here True

exampleOneOf2 : OneOf [(), Int, Bool]
exampleOneOf2 = ThisOne (There (There Here)) True

exampleOneOf3 : OneOf [(), Int, (), Bool]
exampleOneOf3 = ThisOne (There (There (There Here))) True

handleOrdered : FVect ts r -> OneOf ts -> r
handleOrdered fvect (ThisOne el x) = findFVect' el fvect $ x

handleUnordered : FVect ts r -> OneOf ss -> Perm ss ts -> r
handleUnordered fvect (ThisOne el x) perm = findFVect' (theorem1 perm el) fvect $ x

handle : FVect ts r -> OneOf ss -> {auto pe : Perm ss ts} -> r
handle fvect oneOf {pe} = handleUnordered fvect oneOf pe

doesItWork : Int
doesItWork = handle exampleFVect exampleOneOf2

handleWeakRepresentative : FVect ts r -> OneOf ss -> WeakRepresentative ts ss -> r
handleWeakRepresentative fvect (ThisOne el x) weakRep = findFVect' (weakRepElemTheorem weakRep el) fvect $ x

handleWR : FVect ts r -> OneOf ss -> {auto wr : WeakRepresentative ts ss} -> r
handleWR fvect oneOf {wr} = handleWeakRepresentative fvect oneOf wr

doesItWork' : Int
doesItWork' = handleWR exampleFVect exampleOneOf3
