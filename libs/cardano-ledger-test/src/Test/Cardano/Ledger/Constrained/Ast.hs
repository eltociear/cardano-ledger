{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- | The type that make up the Absract Syntax Tree of the Language
module Test.Cardano.Ledger.Constrained.Ast where

import Cardano.Ledger.Pretty
import Data.Char (toLower)
import qualified Data.List as List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text, pack)
import Data.Universe (Any (..))
import Data.Word (Word64)
import Test.Cardano.Ledger.Constrained.Classes (Adds (..), Sizeable (..), Sums (..))
import Test.Cardano.Ledger.Constrained.Env (Dyn (..), Env, Name (..), V (..), findVar, storeVar)
import Test.Cardano.Ledger.Constrained.Monad (HasCond (..), Typed (..), explain, failT, hasOrd, sameRep)
import Test.Cardano.Ledger.Constrained.TypeRep (Rep (..), synopsis, testEql, (:~:) (Refl))

-- ================================================

data Literal t where
  Lit :: Rep t -> t -> Literal t

data Term s t where
  Fixed :: Literal t -> Term s t
  Var :: V s t -> Term s t
  Dom :: Ord a => Term s (Map a b) -> Term s (Set a)
  Rng :: (Ord a, Ord b) => Term s (Map a b) -> Term s (Set b)

infix 4 :=:

infix 4 :<=:

data Pred where
  Sized :: Sizeable t => Term Word64 -> Term t -> Pred era
  (:=:) :: Eq a => Term a -> Term a -> Pred era
  (:<=:) :: Ord a => Term (Set a) -> Term (Set a) -> Pred era
  Disjoint :: Ord a => Term (Set a) -> Term (Set a) -> Pred era
  SumsTo :: Adds c => Term c -> [Sum c] -> Pred era
  Random :: Term t -> Pred era
  HasDom :: Ord d => Term (Map d r) -> Term (Set d) -> Pred era

data Sum c where
  SumMap :: Adds c => Term (Map a c) -> Sum c
  SumSet :: Adds c => Term (Set c) -> Sum c
  SumList :: Adds c => Term [c] -> Sum c
  One :: Term c -> Sum c
  Extract :: forall c x era. Sums x c => Sum x -> Sum c

infixl 0 :$

data Target t where
  Simple :: Term t -> Target t
  (:$) :: Target (a -> b) -> Target a -> Target b
  Constr :: String -> (a -> b) -> Target (a -> b)

infixl 0 $>

-- | Version of (:$) That takes a Term on the left, rather than a Target
($>) :: Target (a -> t) -> Term a -> Target t
($>) f x = f :$ (Simple x)

-- ===================================

showL :: (t -> String) -> [Char] -> [t] -> [Char]
showL _f _sep [] = ""
showL f _sep [t] = f t
showL f sep (t : ts) = f t ++ sep ++ showL f sep ts

instance Show (Literal t) where
  show (Lit r k) = synopsis r k

instance Show (Term t) where
  -- show (Fixed k) = "(Fixed " ++ show k ++ ")"
  show (Fixed k) = show k
  show (Var (V nm _rep _)) = nm -- ++ "::" ++ show _rep
  show (Dom x) = "(dom " ++ show x ++ ")"
  show (Rng x) = "(rng " ++ show x ++ ")"
  showList xs ans = unlines (ans : (map show xs))

instance Show (Sum c) where
  show (SumMap t) = "sum " ++ show t
  show (SumSet t) = "sum " ++ show t
  show (SumList t) = "sum " ++ show t
  show (One t) = show t
  show (Extract _) = "Extract"

instance Show (Pred era) where
  show (Sized n t) = "Sized " ++ show n ++ " " ++ show t
  show (x :=: y) = show x ++ " = " ++ show y
  show (x :<=: y) = show x ++ " ⊆  " ++ show y
  show (Disjoint x y) = "Disjoint " ++ show x ++ " " ++ show y
  show (SumsTo c m) = show c ++ " =∑= " ++ showL show " + " m
  show (Random x) = "Random " ++ show x
  show (HasDom m s) = "HasDomain " ++ show m ++ " " ++ show s
  showList xs ans = unlines (ans : (map show xs))

instance Show (Target t) where
  show (Constr nm _f) = nm
  show (Simple x) = show x
  show (f :$ x) = "(" ++ show f ++ " :$ " ++ showL pp " :$ " (args x) ++ ")"
    where
      pp :: Any (Target era) -> String
      pp (Any spec) = show spec

args :: Target t -> [Any (Target era)]
args (x :$ xs) = (Any x) : args xs
args other = [Any other]

-- | Print a Target as a record showing the struture and names of all
--   the variables involved. This documents what is in scope where
--   the Target value was defined.
ppTarget :: Target t -> PDoc
ppTarget x = targetRecord x []

targetRecord :: Target t -> [(Text, PDoc)] -> PDoc
targetRecord (Constr n _) xs = ppRecord (pack n) xs
targetRecord (ts :$ t) xs = targetRecord ts (targetPair t : xs)
targetRecord (Simple e) [] = ppString (show e)
targetRecord other xs = ppRecord (nameOf other) xs

nameOf :: Target t -> Text
nameOf (Constr cs _) = pack (map toLower cs ++ "T")
nameOf (Simple (Var (V n _ _))) = pack n
nameOf (Simple term) = pack (show term)
nameOf (x :$ _) = nameOf x

targetPair :: Target t -> (Text, PDoc)
targetPair (Simple (Var (V n rep _))) = (pack n, ppString (show rep))
targetPair x = (nameOf x, targetRecord x [])

-- ===================================================
-- Computing the variables (V t) in a Term, Pred, Target
-- Their are no binders in any of these, so this is not so difficult
-- But (V t) may have different 't', so we hide 't' in 'Name'

varsOfTerm :: Set (Name era) -> Term t -> Set (Name era)
varsOfTerm ans s = case s of
  Fixed _ -> ans
  Var v@(V _ _ _) -> Set.insert (Name v) ans
  Dom x -> varsOfTerm ans x
  Rng x -> varsOfTerm ans x

vars :: Term t -> Set (Name era)
vars x = varsOfTerm Set.empty x

varsOfTarget :: Set (Name era) -> Target t -> Set (Name era)
varsOfTarget ans s = case s of
  (a :$ b) -> varsOfTarget (varsOfTarget ans a) b
  (Simple x) -> varsOfTerm ans x
  (Constr _ _) -> ans

varsOfPred :: Set (Name era) -> Pred -> Set (Name era)
varsOfPred ans s = case s of
  Sized a b -> varsOfTerm (varsOfTerm ans a) b
  (a :=: b) -> varsOfTerm (varsOfTerm ans a) b
  (a :<=: b) -> varsOfTerm (varsOfTerm ans a) b
  (Disjoint a b) -> varsOfTerm (varsOfTerm ans a) b
  SumsTo x xs -> List.foldl' varsOfSum (varsOfTerm ans x) xs
  Random x -> varsOfTerm ans x
  HasDom a b -> varsOfTerm (varsOfTerm ans a) b

varsOfSum :: Set (Name era) -> Sum r -> Set (Name era)
varsOfSum ans (SumMap y) = varsOfTerm ans y
varsOfSum ans (SumSet y) = varsOfTerm ans y
varsOfSum ans (SumList y) = varsOfTerm ans y
varsOfSum ans (One y) = varsOfTerm ans y
varsOfSum ans (Extract x) = varsOfSum ans x

-- =====================================================
-- Subtitution of (V t) inside of (Spec t)

substToEnv :: [SubItem era] -> Env -> Env era
substToEnv [] ans = ans
substToEnv ((SubItem v (Fixed (Lit _ t))) : more) ans =
  substToEnv more (storeVar v t ans)
substToEnv ((SubItem _ e) : _) _ = error ("Not Literal expr in substToEnv: " ++ show e)

data SubItem where SubItem :: V t -> Term t -> SubItem era

instance Show (SubItem era) where
  show (SubItem (V nm _rep _) expr) = pad 14 nm ++ " = " ++ show expr

pad :: Int -> String -> String
pad n x = x ++ replicate (n - length x) ' '

type Subst = [SubItem]

extend :: V t -> Term t -> Subst -> Subst era
extend v k xs = (SubItem v k) : xs

findV :: Subst -> V t -> Term t
findV [] (V n rep1 lens) = Var (V n rep1 lens) -- If its not in the Subst, return the Var
findV (SubItem (V n2 rep2 _) kn : more) v@(V n1 rep1 _) =
  if not (n1 == n2)
    then findV more v
    else case testEql rep1 rep2 of
      Just Refl -> kn
      Nothing ->
        error
          ( "In findV, we found: "
              ++ n1
              ++ ", but the types did not match. "
              ++ show rep1
              ++ " =/= "
              ++ show rep2
          )

substTerm :: Subst -> Term t -> Term t
substTerm sub (Var v) = findV sub v
substTerm _ (Fixed k) = Fixed k
substTerm sub (Dom x) = Dom (substTerm sub x)
substTerm sub (Rng x) = Rng (substTerm sub x)

substPred :: Subst -> Pred -> Pred era
substPred sub (Sized a b) = Sized (substTerm sub a) (substTerm sub b)
substPred sub (a :=: b) = (substTerm sub a) :=: (substTerm sub b)
substPred sub (a :<=: b) = (substTerm sub a) :<=: (substTerm sub b)
substPred sub (Disjoint a b) = Disjoint (substTerm sub a) (substTerm sub b)
substPred sub (SumsTo a b) = SumsTo (substTerm sub a) (map (substSum sub) b)
substPred sub (Random x) = Random (substTerm sub x)
substPred sub (HasDom a b) = HasDom (substTerm sub a) (substTerm sub b)

substSum :: Subst -> Sum t -> Sum t
substSum sub (SumMap x) = SumMap (substTerm sub x)
substSum sub (SumSet x) = SumSet (substTerm sub x)
substSum sub (SumList x) = SumList (substTerm sub x)
substSum sub (One x) = One (substTerm sub x)
substSum sub (Extract x) = Extract (substSum sub x)

substTarget :: Subst -> Target t -> Target t
substTarget sub (Simple e) = Simple (substTerm sub e)
substTarget sub (a :$ b) = substTarget sub a :$ substTarget sub b
substTarget _ (Constr n f) = Constr n f

-- ======================================================
-- Evaluators

-- | Symbolic evaluation with free variables, that cause failures
eval :: Term t -> Typed (Dyn era)
eval (Fixed (Lit r x)) = pure (Dyn r x)
eval (Dom x) = case eval x of
  Typed (Right (Dyn (MapR d _) m)) -> pure (Dyn (SetR d) (Map.keysSet m))
  Typed _other -> failT ["In " ++ show (Dom x) ++ ", " ++ show x ++ " does not eval to a Map type"]
eval (Rng (Var (V nm _ _))) = failT ["Can't eval variable: " ++ nm]
eval (Rng (Fixed (Lit (MapR _ r) m))) = pure (Dyn (SetR r) (Set.fromList (Map.elems m)))
eval (Rng (Fixed _)) = failT ["Rng applied to a value that is not a map"]
eval (Var (V nm _ _)) = failT ["Can't eval unbound variable: " ++ nm]

-- | Evidence that 'expr' has type 'r1'
evalWith :: Rep t -> Term s -> Typed t
evalWith r1 expr = explain ("(evalWith " ++ show r1 ++ " " ++ show expr ++ ") fails") $ do
  (Dyn r2 x) <- eval expr
  Refl <- sameRep r1 r2
  pure x

-- | Evaluate an arbitrary expression, if it actually has type (s rng) and (Ord rng) then
--   return evidence of these facts (HasCond Ord (s rng))
evalWithOrd :: Rep (s rng) -> Term k -> Rep rng -> Typed (HasCond Ord (s rng))
evalWithOrd r expr rng = explain ("(evalWithOrd " ++ show r ++ " " ++ show expr ++ " " ++ show rng ++ ") fails") $ do
  m <- evalWith r expr
  hasOrd rng m

-- | Fully evaluate an Term, looking up the variables in the Env.
runTerm :: Env -> Term t -> Typed t
runTerm _ (Fixed (Lit _ x)) = pure x
runTerm env (Dom x) = do
  m <- runTerm env x
  pure (Map.keysSet m)
runTerm env (Rng x) = do
  m <- runTerm env x
  pure (Set.fromList (Map.elems m))
runTerm env (Var v) = findVar v env

runPred :: Env -> Pred -> Typed Bool
runPred env (Sized w x) = do
  word <- runTerm env w
  item <- runTerm env x
  pure (getsize item == word)
runPred env (x :=: y) = do
  x2 <- runTerm env x
  y2 <- runTerm env y
  pure (x2 == y2)
runPred env (Disjoint x y) = do
  x2 <- runTerm env x
  y2 <- runTerm env y
  pure (Set.disjoint x2 y2)
runPred env (x :<=: y) = do
  x2 <- runTerm env x
  y2 <- runTerm env y
  pure (Set.isSubsetOf x2 y2)
runPred env (SumsTo x ys) = do
  x2 <- runTerm env x
  is <- mapM (runSum env) ys
  let y2 = List.foldl' add zero is
  pure (x2 == y2)
runPred _ (Random _) = pure True
runPred env (HasDom m s) = do
  m2 <- runTerm env m
  s2 <- runTerm env s
  pure (Set.isSubsetOf (Map.keysSet m2) s2)

runSum :: Env -> Sum c -> Typed c
runSum env (SumMap t) = Map.foldl' add zero <$> runTerm env t
runSum env (SumSet t) = Set.foldl' add zero <$> runTerm env t
runSum env (SumList t) = List.foldl' add zero <$> runTerm env t
runSum env (One t) = runTerm env t
runSum env (Extract x) = getsum <$> runSum env x

makeTest :: Env -> Pred -> Typed String
makeTest env c = do
  b <- runPred env c
  pure (show c ++ " => " ++ show b)
