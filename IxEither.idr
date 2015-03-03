import Elem
import FSet

data IxEither : List Type -> Type -> Type where
  IxLeft : OneOf ts -> IxEither ts a
  IxRight : a -> IxEither ts a

runIxEither : IxEither ts a -> Either (OneOf ts) a
runIxEither (IxLeft x) = Left x
runIxEither (IxRight x) = Right x

ixeMap : (a -> b) -> IxEither ts a -> IxEither ts b
ixeMap _ (IxLeft x) = IxLeft x
ixeMap f (IxRight x) = IxRight (f x)

ixePure : (x : a) -> IxEither ts a
ixePure = IxRight

ixeAp : Append ts rs ss -> IxEither ts (a -> b) -> IxEither rs a -> IxEither ss b
ixeAp app (IxLeft oneOf) _ = IxLeft (oneOfAppendLemmaLeft oneOf app)
ixeAp app _ (IxLeft oneOf) = IxLeft (oneOfAppendLemmaRight oneOf app)
ixeAp app (IxRight f) (IxRight x) = IxRight (f x)

ixeBind : Append ts rs ss -> IxEither ts a -> (a -> IxEither rs b) -> IxEither ss b
ixeBind app (IxLeft oneOf) f = IxLeft (oneOfAppendLemmaLeft oneOf app)
ixeBind app (IxRight x) f = case f x of
  IxLeft oneOf => IxLeft (oneOfAppendLemmaRight oneOf app)
  IxRight y => IxRight y
