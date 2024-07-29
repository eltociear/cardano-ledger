{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Test.Cardano.Ledger.Conformance.ExecSpecRule.Core2
where

import Cardano.Ledger.BaseTypes (Inject (..), ShelleyBase)
import Cardano.Ledger.Core (EraRule)
import qualified Constrained as CV2
import Constrained.Base (shrinkWithSpec, simplifySpec)
import Control.State.Transition.Extended (STS (..))
import Data.Bifunctor (Bifunctor (..))
import Data.Bitraversable (bimapM)
import Data.Functor (($>))
import qualified Data.Text as T
import Data.Typeable (Proxy (..), Typeable, typeRep)
import GHC.Base (Constraint, NonEmpty, Symbol, Type)
import GHC.TypeLits (KnownSymbol)
import qualified Lib as Agda
import Test.Cardano.Ledger.Binary.TreeDiff (Pretty (..), ansiWlPretty, ediff, ppEditExpr)
import Test.Cardano.Ledger.Conformance.SpecTranslate.Core (
  FixupSpecRep (..),
  SpecTranslate (..),
  runSpecTransM,
  toTestRep,
 )
import Test.Cardano.Ledger.Imp.Common
import Test.Cardano.Ledger.Shelley.ImpTest (
  ImpTestM,
  ShelleyEraImp,
  impAnn,
  logEntry,
  tryRunImpRule,
 )
import UnliftIO (evaluateDeep)

type ForAllSTSTypes (c :: Type -> Constraint) rule era =
  ( c (Environment (EraRule rule era))
  , c (State (EraRule rule era))
  , c (Signal (EraRule rule era))
  )

type ForAllSTSSpecRepTypes (c :: Type -> Constraint) rule era =
  ( c (SpecRep (Environment (EraRule rule era)))
  , c (SpecRep (State (EraRule rule era)))
  , c (SpecRep (Signal (EraRule rule era)))
  )

class
  ( ForAllSTSTypes ToExpr rule era
  , ForAllSTSTypes NFData rule era
  , KnownSymbol rule
  , STS (EraRule rule era)
  , BaseM (EraRule rule era) ~ ShelleyBase
  ) =>
  AgdaRunnable (fn :: [Type] -> Type -> Type) (rule :: Symbol) era
  where
  type STSContext fn rule era

  genSTSContext :: Gen (STSContext fn rule era)
  default genSTSContext ::
    Arbitrary (STSContext fn rule era) =>
    Gen (STSContext fn rule era)
  genSTSContext = arbitrary

  runAgdaRule ::
    SpecRep (Environment (EraRule rule era)) ->
    SpecRep (State (EraRule rule era)) ->
    SpecRep (Signal (EraRule rule era)) ->
    Either
      (NonEmpty (SpecRep (PredicateFailure (EraRule rule era))))
      (SpecRep (State (EraRule rule era)))

  extraInfo ::
    STSContext fn rule era ->
    Environment (EraRule rule era) ->
    State (EraRule rule era) ->
    Signal (EraRule rule era) ->
    String
  extraInfo _ _ __ _ = ""

conformsToImpl ::
  forall (rule :: Symbol) fn era.
  ( ShelleyEraImp era
  , AgdaRunnable fn rule era
  , ForAllSTSSpecRepTypes ToExpr rule era
  , SpecTranslate (STSContext fn rule era) (Environment (EraRule rule era))
  , SpecTranslate (STSContext fn rule era) (State (EraRule rule era))
  , SpecTranslate (STSContext fn rule era) (Signal (EraRule rule era))
  , SpecTranslate (STSContext fn rule era) (PredicateFailure (EraRule rule era))
  , NFData (SpecRep (PredicateFailure (EraRule rule era)))
  , NFData (SpecRep (State (EraRule rule era)))
  , ToExpr (STSContext fn rule era)
  , Eq (SpecRep (PredicateFailure (EraRule rule era)))
  , Eq (SpecRep (State (EraRule rule era)))
  , FixupSpecRep (SpecRep (PredicateFailure (EraRule rule era)))
  , FixupSpecRep (SpecRep (State (EraRule rule era)))
  , GenSTSTypes fn rule era
  ) =>
  Property
conformsToImpl =
  forAllShow genCtx showExpr $ \ctx -> do
    let (envSpec, stateSpec, signalSpec) = genSTSTypes @fn @rule @era ctx
    forAllSpec (CV2.simplifySpec envSpec) $ \env ->
      forAllSpec (CV2.simplifySpec stateSpec) $ \state ->
        forAllSpec (CV2.simplifySpec signalSpec) $ \signal ->
          counterexample (extraInfo @fn @rule @era ctx env state signal) $ do
            _ <- impAnn @_ @era "Deep evaluating env" $ evaluateDeep env
            _ <- impAnn "Deep evaluating st" $ evaluateDeep state
            _ <- impAnn "Deep evaluating sig" $ evaluateDeep signal

            -- translate inputs
            specEnv <- translateAndLog env ctx "agdaEnv:\n"
            specSt <- translateAndLog state ctx "agdaSt:\n"
            specSig <- translateAndLog signal ctx "agdaSig:\n"

            agdaResTest <-
              fmap (bimap (fixup <$>) fixup) $
                impAnn "Deep evaluating Agda output" $
                  evaluateDeep $
                    runAgdaRule @fn @rule @era specEnv specSt specSig
            implRes <- tryRunImpRule @rule @era env state signal
            implResTest <-
              impAnn "Translating implementation values to SpecRep" $
                expectRightExpr $
                  runSpecTransM ctx $
                    bimapM (traverse toTestRep) (toTestRep . fst) implRes
            unless (implResTest == agdaResTest) $ expectationFailure failMsg
  where
    genCtx = genSTSContext @fn @rule @era
    translateAndLog x ctx msg = do
      res <- expectRight' . runSpecTransM ctx $ toSpecRep x
      logEntry $ msg <> showExpr res
      pure res
    expectRight' (Right x) = pure x
    expectRight' (Left e) = assertFailure (T.unpack e)
    forAllSpec spec = forAllShrinkShow (CV2.genFromSpec spec) (shrinkWithSpec spec) showExpr
    failMsg = "FAIL"

class
  ForAllSTSTypes (CV2.HasSpec fn) rule era =>
  GenSTSTypes (fn :: [Type] -> Type -> Type) (rule :: Symbol) era
  where
  genSTSTypes ::
    STSContext fn rule era ->
    ( CV2.Specification fn (Environment (EraRule rule era))
    , CV2.Specification fn (State (EraRule rule era))
    , CV2.Specification fn (Signal (EraRule rule era))
    )
