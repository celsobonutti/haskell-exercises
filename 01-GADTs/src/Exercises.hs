{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}
module Exercises where





{- ONE -}

-- | Let's introduce a new class, 'Countable', and some instances to match.
class Countable a where count :: a -> Int
instance Countable Int  where count   = id
instance Countable [a]  where count   = length
instance Countable Bool where count x = if x then 1 else 0

-- | a. Build a GADT, 'CountableList', that can hold a list of 'Countable'
-- things.

data CountableList where
  CountableNil :: CountableList
  CountableCons :: Countable a => a -> CountableList -> CountableList


-- | b. Write a function that takes the sum of all members of a 'CountableList'
-- once they have been 'count'ed.

countList :: CountableList -> Int
countList CountableNil = 0
countList (CountableCons x xs) = count x + countList xs


-- | c. Write a function that removes all elements whose count is 0.

dropZero :: CountableList -> CountableList
dropZero CountableNil = CountableNil
dropZero (CountableCons x xs)
  | count x == 0 = dropZero xs
  | otherwise = CountableCons x (dropZero xs)


-- | d. Can we write a function that removes all the things in the list of type
-- 'Int'? If not, why not?
-- We can't remove things of type `Int` because we can't know the type of `a`

filterInts :: CountableList -> CountableList
filterInts = error "Contemplate me!"



{- TWO -}

-- | a. Write a list that can take /any/ type, without any constraints.

data AnyList where
  AnyNil :: AnyList
  AnyCons :: a -> AnyList -> AnyList

-- | b. How many of the following functions can we implement for an 'AnyList'?

concatAnyList :: AnyList -> AnyList -> AnyList
concatAnyList AnyNil ys = ys
concatAnyList (AnyCons x xs) ys = AnyCons x (concatAnyList xs ys)

reverseAnyList :: AnyList -> AnyList
reverseAnyList AnyNil = AnyNil
reverseAnyList (AnyCons x xs) = concatAnyList xs (AnyCons x AnyNil)

-- Can't be implemented because we can't access `a`
filterAnyList :: (a -> Bool) -> AnyList -> AnyList
filterAnyList = undefined

lengthAnyList :: AnyList -> Int
lengthAnyList AnyNil = 0
lengthAnyList (AnyCons _ xs) = 1 + lengthAnyList xs

-- That's not really a `fold`, but...

foldAnyList :: Monoid m => AnyList -> m
foldAnyList = mempty

isEmptyAnyList :: AnyList -> Bool
isEmptyAnyList AnyNil = True
isEmptyAnyList _ = False

-- Can't be implemented because we don't enforce that `a` is Show
instance Show AnyList where
  show = error "What about me?"


{- THREE -}

-- | Consider the following GADT:

data TransformableTo output where
  TransformWith
    :: (input -> output)
    ->  input
    -> TransformableTo output

-- | ... and the following values of this GADT:

transformable1 :: TransformableTo String
transformable1 = TransformWith show 2.5

transformable2 :: TransformableTo String
transformable2 = TransformWith (uncurry (++)) ("Hello,", " world!")

-- | a. Which type variable is existential inside 'TransformableTo'? What is
-- the only thing we can do to it?
-- `input` is existential inside TransformableTo
-- We can only apply values of type the function `input -> output`
-- is expecting

-- | b. Could we write an 'Eq' instance for 'TransformableTo'? What would we be
-- able to check?
instance Eq a => Eq (TransformableTo a) where
  TransformWith f x == TransformWith g y = f x == g y

-- As it's shown above: we can. We would only be able to check if the resulting
-- value is the same, thogh, so there are no guarantees that neither the types
-- or values of `f` and `g`, and `x` and `y` are the same.

-- | c. Could we write a 'Functor' instance for 'TransformableTo'? If so, write
-- it. If not, why not?

instance Functor TransformableTo where
  fmap g (TransformWith f x) = TransformWith (g . f) x




{- FOUR -}

-- | Here's another GADT:

data EqPair where
  EqPair :: Eq a => a -> a -> EqPair

-- | a. There's one (maybe two) useful function to write for 'EqPair'; what is
-- it?
areEqual :: EqPair -> Bool
areEqual (EqPair a b) = a == b

areDifferent :: EqPair -> Bool
areDifferent = not . areEqual

-- | b. How could we change the type so that @a@ is not existential? (Don't
-- overthink it!)

data EqPair' a where
  EqPair' :: Eq a => a -> a -> EqPair' a

-- | c. If we made the change that was suggested in (b), would we still need a
-- GADT? Or could we now represent our type as an ADT?
-- We could write it as a simple ADT

data EqPair'' a = EqPair'' a a

-- But there would be no way to know if `a` has an instance of `Eq`


{- FIVE -}

-- | Perhaps a slightly less intuitive feature of GADTs is that we can set our
-- type parameters (in this case @a@) to different types depending on the
-- constructor.

data MysteryBox a where
  EmptyBox  ::                                MysteryBox ()
  IntBox    :: Int    -> MysteryBox ()     -> MysteryBox Int
  StringBox :: String -> MysteryBox Int    -> MysteryBox String
  BoolBox   :: Bool   -> MysteryBox String -> MysteryBox Bool

-- | When we pattern-match, the type-checker is clever enough to
-- restrict the branches we have to check to the ones that could produce
-- something of the given type.

getInt :: MysteryBox Int -> Int
getInt (IntBox int _) = int

-- | a. Implement the following function by returning a value directly from a
-- pattern-match:

getInt' :: MysteryBox String -> Int
getInt' (StringBox _ (IntBox i _)) = i

-- | b. Write the following function. Again, don't overthink it!

countLayers :: MysteryBox a -> Int
countLayers EmptyBox = 0
countLayers (IntBox _ box) = 1 + countLayers box
countLayers (StringBox _ box) = 1 + countLayers box
countLayers (BoolBox _ box) = 1 + countLayers box

-- | c. Try to implement a function that removes one layer of "Box". For
-- example, this should turn a BoolBox into a StringBox, and so on. What gets
-- in our way? What would its type be?
-- This can't be impolemented because we can't know the type of the underlying Box


{- SIX -}

-- | We can even use our type parameters to keep track of the types inside an
-- 'HList'!  For example, this heterogeneous list contains no existentials:

data HList a where
  HNil  :: HList ()
  HCons :: head -> HList tail -> HList (head, tail)

exampleHList :: HList (String, (Int, (Bool, ())))
exampleHList = HCons "Tom" (HCons 25 (HCons True HNil))

-- | a. Write a 'head' function for this 'HList' type. This head function
-- should be /safe/: you can use the type signature to tell GHC that you won't
-- need to pattern-match on HNil, and therefore the return type shouldn't be
-- wrapped in a 'Maybe'!

hHead :: HList (a, b) -> a
hHead (HCons hd _) = hd

-- | b. Currently, the tuples are nested. Can you pattern-match on something of
-- type @HList (Int, String, Bool, ())@? Which constructor would work?

-- It's not possible to pattern match on this because it would need a 4-item tuple,
-- but our constructor only has 2-item tuples

patternMatchMe :: HList (Int, String, Bool, ()) -> Int
patternMatchMe = undefined

-- | c. Can you write a function that appends one 'HList' to the end of
-- another? What problems do you run into?
-- Not, because we can't combine two big tuples into one at the type level.




{- SEVEN -}

-- | Here are two data types that may help:

data Empty
data Branch left centre right

-- | a. Using these, and the outline for 'HList' above, build a heterogeneous
-- /tree/. None of the variables should be existential.

data HTree a where
  HEmpty :: HTree Empty
  HBranch :: HTree a -> b -> HTree c -> HTree (Branch a b c)

-- | b. Implement a function that deletes the left subtree. The type should be
-- strong enough that GHC will do most of the work for you. Once you have it,
-- try breaking the implementation - does it type-check? If not, why not?

removeLeft :: HTree (Branch left center right) -> HTree (Branch Empty center right)
removeLeft (HBranch _ center right) = HBranch HEmpty center right

-- | c. Implement 'Eq' for 'HTree's. Note that you might have to write more
-- than one to cover all possible HTrees. You might also need an extension or
-- two, so look out for something... flexible... in the error messages!
-- Recursion is your friend here - you shouldn't need to add a constraint to
-- the GADT!

instance Eq (HTree Empty) where
  HEmpty == HEmpty = True

instance (Eq (HTree left), Eq center, Eq (HTree right)) => Eq (HTree (Branch left center right)) where
  (HBranch left center right) == (HBranch left' center' right') = left == left' && center == center' && right == right'



{- EIGHT -}

-- | a. Implement the following GADT such that values of this type are lists of
-- values alternating between the two types. For example:
--
-- @
--   f :: AlternatingList Bool Int
--   f = ACons True (ACons 1 (ACons False (ACons 2 ANil)))
-- @

data AlternatingList a b where
  ANil :: AlternatingList a b
  ACons :: a -> AlternatingList b a -> AlternatingList a b

-- | b. Implement the following functions.

getFirsts :: AlternatingList a b -> [a]
getFirsts ANil = []
getFirsts (ACons a (ACons _ as)) = a : getFirsts as
getFirsts (ACons a ANil) = [a]

getSeconds :: AlternatingList a b -> [b]
getSeconds ANil = []
getSeconds (ACons _ b) = getFirsts b

-- | c. One more for luck: write this one using the above two functions, and
-- then write it such that it only does a single pass over the list.

foldValuesFirstSecond :: (Monoid a, Monoid b) => AlternatingList a b -> (a, b)
foldValuesFirstSecond alternating = (mconcat as, mconcat bs)
  where
    as = getFirsts alternating
    bs = getSeconds alternating

foldValues :: (Monoid a, Monoid b) => AlternatingList a b -> (a, b)
foldValues ANil = (mempty, mempty)
foldValues (ACons x xs) = let (b, a) = foldValues xs in (x <> a, b)




{- NINE -}

-- | Here's the "classic" example of a GADT, in which we build a simple
-- expression language. Note that we use the type parameter to make sure that
-- our expression is well-formed.

data Expr a where
  Equals    :: Expr Int  -> Expr Int             -> Expr Bool
  Add       :: Expr Int  -> Expr Int             -> Expr Int
  If        :: Expr Bool -> Expr a   -> Expr a   -> Expr a
  IntValue  :: Int                               -> Expr Int
  BoolValue :: Bool                              -> Expr Bool

-- | a. Implement the following function and marvel at the typechecker:

eval :: Expr a -> a
eval (IntValue x) = x
eval (BoolValue y) = y
eval (Equals x y) = eval x == eval y
eval (Add x y) = eval x + eval y
eval (If predicate consequent alternative) = if eval predicate then eval consequent else eval alternative

-- | b. Here's an "untyped" expression language. Implement a parser from this
-- into our well-typed language. Note that (until we cover higher-rank
-- polymorphism) we have to fix the return type. Why do you think this is?

data DirtyExpr
  = DirtyEquals    DirtyExpr DirtyExpr
  | DirtyAdd       DirtyExpr DirtyExpr
  | DirtyIf        DirtyExpr DirtyExpr DirtyExpr
  | DirtyIntValue  Int
  | DirtyBoolValue Bool

data Typed where
  IntType :: Expr Int -> Typed
  BoolType :: Expr Bool -> Typed

parse :: DirtyExpr -> Maybe Typed
parse (DirtyBoolValue bool) = Just . BoolType . BoolValue $ bool
parse (DirtyIntValue int) = Just . IntType . IntValue $ int
parse (DirtyEquals (parse -> Just (IntType x)) (parse -> Just (IntType y))) = Just . BoolType $ Equals x y
parse (DirtyAdd (parse -> Just (IntType x)) (parse -> Just (IntType y))) = Just . IntType $ Add  x y
parse (DirtyIf
       (parse -> Just (BoolType predicate))
       (parse -> Just consequent)
       (parse -> Just alternative)) = case (consequent, alternative) of
                                        (IntType c, IntType a) -> Just . IntType $ If predicate c a
                                        (BoolType c, BoolType a) -> Just . BoolType $ If predicate c a
                                        _ -> Nothing
parse _ = Nothing

-- | c. Can we add functions to our 'Expr' language? If not, why not? What
-- other constructs would we need to add? Could we still avoid 'Maybe' in the
-- 'eval' function?





{- TEN -}

-- | Back in the glory days when I wrote JavaScript, I could make a composition
-- list like @pipe([f, g, h, i, j])@, and it would pass a value from the left
-- side of the list to the right. In Haskell, I can't do that, because the
-- functions all have to have the same type :(

-- | a. Fix that for me - write a list that allows me to hold any functions as
-- long as the input of one lines up with the output of the next.

data TypeAlignedList a b where
  Id :: TypeAlignedList a a
  Cons :: (a -> b) -> TypeAlignedList b c -> TypeAlignedList a c

infixr 9 :>

pattern (:>) :: (a -> b) -> TypeAlignedList b c -> TypeAlignedList a c
pattern f :> fs <- Cons f fs where
  f :> fs = Cons f fs

{-# COMPLETE (:>), Id #-}

test :: TypeAlignedList Int Bool
test = (+ 5) :> show :> (== "10") :> Id

-- | b. Which types are existential?
-- Every type besides the input of the first function
-- and the output of the last one

-- | c. Write a function to append type-aligned lists. This is almost certainly
-- not as difficult as you'd initially think.

composeTALs :: TypeAlignedList b c -> TypeAlignedList a b -> TypeAlignedList a c
composeTALs tal Id = tal
composeTALs tal (hd :> tl) = hd :> composeTALs tal tl
