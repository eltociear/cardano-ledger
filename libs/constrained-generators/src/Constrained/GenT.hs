{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Constrained.GenT where

import Control.Applicative
import Control.Monad
import Data.Foldable
import Data.List.NonEmpty qualified as NE
import GHC.Stack
import System.Random
import Test.QuickCheck hiding (Args, Fun)
import Test.QuickCheck.Gen
import Test.QuickCheck.Random

------------------------------------------------------------------------
-- The Gen Error monad
------------------------------------------------------------------------

-- | A class for different types of errors with a stack of `explain` calls to
-- narrow down problems. The (NE.NonEmpty String) means one cannot cause an
-- Error without at least 1 string to explain it.
class Monad m => MonadGenError m where
  genError :: HasCallStack => NE.NonEmpty String -> m a
  fatalError :: HasCallStack => NE.NonEmpty String -> m a
  explain :: HasCallStack => NE.NonEmpty String -> m a -> m a

-- | genError with one line of explanation
genError1 :: MonadGenError m => String -> m a
genError1 s = genError (pure s)

-- | fatalError with one line of explanation
fatalError1 :: MonadGenError m => String -> m a
fatalError1 s = fatalError (pure s)

-- | explain with one line of explanation
explain1 :: MonadGenError m => String -> m a -> m a
explain1 s = explain (pure s)

-- | The Gen Error monad, distinguishes between fatal errors
-- and non-fatal errors.
data GE a
  = FatalError [NE.NonEmpty String] (NE.NonEmpty String)
  | GenError [NE.NonEmpty String] (NE.NonEmpty String)
  | Result [NE.NonEmpty String] a
  deriving (Ord, Eq, Show, Functor)

instance Applicative GE where
  pure = Result []
  (<*>) = ap

instance Monad GE where
  FatalError es err >>= _ = FatalError es err
  GenError es err >>= _ = GenError es err
  Result _ a >>= k = k a

instance Alternative GE where
  empty = GenError [] (pure "Not a real error. makes GE have Alternative instance")
  m@FatalError {} <|> _ = m
  GenError {} <|> m = m
  Result es x <|> _ = Result es x

instance MonadGenError GE where
  genError neStr = GenError [] neStr
  fatalError neStr = FatalError [] neStr
  explain nes (GenError es' err) = GenError (nes : es') err
  explain nes (FatalError es' err) = FatalError (nes : es') err
  explain nes (Result es' a) = Result (nes : es') a

instance MonadGenError m => MonadGenError (GenT m) where
  genError es = GenT $ \_ -> pure $ genError es
  fatalError es = GenT $ \_ -> pure $ fatalError es
  explain es gen = GenT $ \mode -> fmap (explain es) (runGenT gen mode)

instance MonadGenError m => MonadFail (GenT m) where
  fail s = genError (pure s)

catGEs :: MonadGenError m => [GE a] -> m [a]
catGEs [] = pure []
catGEs (Result _ a : ges) = (a :) <$> catGEs ges
catGEs (GenError {} : ges) = catGEs ges
catGEs (FatalError es e : _) =
  runGE $ FatalError es e

fromGE :: (NE.NonEmpty String -> a) -> GE a -> a
fromGE _ (Result _ a) = a
fromGE a (GenError [] e) = a e
fromGE a (GenError es e) = a $ foldr1 (<>) es <> e
fromGE _ (FatalError es e) =
  error . unlines $ concat (map NE.toList es) ++ (NE.toList e)

errorGE :: GE a -> a
errorGE = fromGE (error . unlines . NE.toList)

isOk :: GE a -> Bool
isOk GenError {} = False
isOk FatalError {} = False
isOk Result {} = True

runGE :: MonadGenError m => GE r -> m r
runGE (GenError es err) = foldr explain (genError err) es
runGE (FatalError es err) = foldr explain (fatalError err) es
runGE (Result es a) = foldr explain (pure a) es

fromGEProp :: Testable p => GE p -> Property
fromGEProp (GenError es err) =
  foldr (counterexample . unlines) (counterexample (unlines (NE.toList err)) False) (map NE.toList es)
fromGEProp (FatalError es err) =
  foldr (counterexample . unlines) (counterexample (unlines (NE.toList err)) False) (map NE.toList es)
fromGEProp (Result es p) = foldr (counterexample . unlines) (property p) (map NE.toList es)

fromGEDiscard :: Testable p => GE p -> Property
fromGEDiscard (Result es p) = foldr (counterexample . unlines . NE.toList) (property p) es
fromGEDiscard _ = discard

headGE :: Foldable t => t a -> GE a
headGE t
  | x : _ <- toList t = pure x
  | otherwise = fatalError (pure "head of empty structure")

------------------------------------------------------------------------
-- GenT
------------------------------------------------------------------------

-- | Generation mode - how strict are we about requiring the generator to
-- succeed. This is necessary because sometimes failing to find a value means
-- there is an actual problem (a generator _should_ be satisfiable but for
-- whatever buggy reason it isn't) and sometimes failing to find a value just
-- means there are no values. The latter case is very relevant when you're
-- generating e.g. lists or sets of values that can be empty.
data GenMode
  = Loose
  | Strict
  deriving (Ord, Eq, Show)

-- TODO: put a global suchThat fuel parameter in here? To avoid exponential blowup of nested such
-- thats?
newtype GenT m a = GenT {runGenT :: GenMode -> Gen (m a)}
  deriving (Functor)

instance Monad m => Applicative (GenT m) where
  pure x = GenT $ \_ -> pure (pure x)
  (<*>) = ap

instance Monad m => Monad (GenT m) where
  GenT m >>= k = GenT $ \mode -> MkGen $ \r n -> do
    a <- unGen (m mode) (left r) n
    unGen (runGenT (k a) mode) (right r) n

strictGen :: GenT m a -> Gen (m a)
strictGen gen = runGenT gen Strict

genFromGenT :: GenT GE a -> Gen a
genFromGenT genT = errorGE <$> runGenT genT Strict

resizeT :: (Int -> Int) -> GenT m a -> GenT m a
resizeT f (GenT gm) = GenT $ \mode -> sized $ \sz -> resize (f sz) (gm mode)

pureGen :: Applicative m => Gen a -> GenT m a
pureGen gen = GenT $ \_ -> pure <$> gen

listOfT :: MonadGenError m => GenT GE a -> GenT m [a]
listOfT gen = do
  lst <- pureGen . listOf $ runGenT gen Loose
  catGEs lst

-- | Generate a list of elements of length at most `goalLen`, but accepting failure
-- to get that many elements so long as `validLen` is true.
-- TODO: possibly one could return "more, fewer, ok" in the `validLen` instead
-- of `Bool`
listOfUntilLenT :: MonadGenError m => GenT GE a -> Int -> (Int -> Bool) -> GenT m [a]
listOfUntilLenT gen goalLen validLen =
  genList `suchThatT` validLen . length
  where
    genList = do
      res <- pureGen . vectorOf goalLen $ runGenT gen Loose
      catGEs res

vectorOfT :: MonadGenError m => Int -> GenT GE a -> GenT m [a]
vectorOfT i gen = GenT $ \mode -> do
  res <- fmap sequence . vectorOf i $ runGenT gen Strict
  case mode of
    Strict -> pure $ runGE res
    Loose -> case res of
      FatalError es e -> pure $ runGE (GenError es e)
      _ -> pure $ runGE res

infixl 2 `suchThatT`
suchThatT :: MonadGenError m => GenT m a -> (a -> Bool) -> GenT m a
suchThatT g p = suchThatWithTryT 100 g p

suchThatWithTryT :: MonadGenError m => Int -> GenT m a -> (a -> Bool) -> GenT m a
suchThatWithTryT tries g p = do
  mode <- getMode
  let (n, cont) = case mode of
        Strict -> (tries, fatalError)
        Loose -> (1 :: Int, genError) -- TODO: Maybe 1 is not the right number here!
  go n cont
  where
    go 0 cont = cont (pure ("Ran out of tries (" ++ show tries ++ ") on suchThatWithTryT"))
    go n cont = do
      a <- g
      if p a then pure a else scaleT (+ 1) $ go (n - 1) cont

scaleT :: (Int -> Int) -> GenT m a -> GenT m a
scaleT sc (GenT gen) = GenT $ \mode -> scale sc $ gen mode

getMode :: Applicative m => GenT m GenMode
getMode = GenT $ \mode -> pure (pure mode)

withMode :: GenMode -> GenT m a -> GenT m a
withMode mode gen = GenT $ \_ -> runGenT gen mode

oneofT :: MonadGenError m => [GenT GE a] -> GenT m a
oneofT gs = do
  mode <- getMode
  r <-
    explain (pure "suchThatT in oneofT") $
      pureGen (oneof [runGenT g mode | g <- gs]) `suchThatT` isOk
  runGE r

frequencyT :: MonadGenError m => [(Int, GenT GE a)] -> GenT m a
frequencyT gs = do
  mode <- getMode
  r <-
    explain (pure "suchThatT in oneofT") $
      pureGen (frequency [(f, runGenT g mode) | (f, g) <- gs]) `suchThatT` isOk
  runGE r

chooseT :: (Random a, Ord a, Show a, MonadGenError m) => (a, a) -> GenT m a
chooseT (a, b)
  | b < a = genError (pure ("chooseT (" ++ show a ++ ", " ++ show b ++ ")"))
  | otherwise = pureGen $ choose (a, b)

sizeT :: Monad m => GenT m Int
sizeT = GenT $ \mode -> sized $ \n -> runGenT (pure n) mode

tryGen :: MonadGenError m => GenT GE a -> GenT m (Maybe a)
tryGen g = do
  r <- pureGen $ runGenT g Loose
  case r of
    FatalError es err -> foldr explain (fatalError err) es
    GenError _ _ -> pure Nothing
    Result _ a -> pure $ Just a

tryGen' :: MonadGenError m => GenT GE a -> GenT m (Maybe a)
tryGen' g = do
  r <- pureGen $ runGenT g Strict
  case r of
    FatalError es err -> foldr explain (fatalError err) es
    GenError _ _ -> pure Nothing
    Result _ a -> pure $ Just a

catchGenT :: GenT GE a -> Gen (Either [String] a)
catchGenT g = genFromGenT $ do
  r <- pureGen $ runGenT g Loose
  case r of
    FatalError es e -> pure $ Left (NE.toList $ foldr1 (<>) es <> e)
    GenError es e -> pure $ Left (NE.toList $ foldr1 (<>) es <> e)
    Result _ a -> pure $ Right a
