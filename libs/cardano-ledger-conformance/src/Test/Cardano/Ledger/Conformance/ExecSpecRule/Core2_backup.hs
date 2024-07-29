{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Test.Cardano.Ledger.Conformance.ExecSpecRule.Core2 (
-- AgdaRunnable (..),
-- conformsToImpl,
-- computationResultToEither,
-- generatesWithin,
-- runConformance,
-- checkConformance,

) where

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
  , Inject (STSContext fn rule era) (Gen (Environment (EraRule rule era)))
  , Inject (STSContext fn rule era) (SpecRep (Environment (EraRule rule era)))
  , Inject (STSContext fn rule era) (Gen (State (EraRule rule era)))
  , Inject (STSContext fn rule era) (SpecRep (State (EraRule rule era)))
  , Inject (STSContext fn rule era) (Gen (Signal (EraRule rule era)))
  , Inject (STSContext fn rule era) (SpecRep (Signal (EraRule rule era)))
  , Inject (STSContext fn rule era) (PredicateFailure (EraRule rule era))
  ) =>
  AgdaRunnable fn (rule :: Symbol) era
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
  extraInfo _ _ _ _ = ""

conformsToImpl ::
  forall (rule :: Symbol) fn era.
  ( ShelleyEraImp era
  , AgdaRunnable fn rule era
  , ForAllSTSTypes NFData rule era
  , ForAllSTSSpecRepTypes ToExpr rule era
  , NFData (SpecRep (PredicateFailure (EraRule rule era)))
  , ToExpr (SpecRep (PredicateFailure (EraRule rule era)))
  , ToExpr (STSContext fn rule era)
  , Eq (SpecRep (PredicateFailure (EraRule rule era)))
  , FixupSpecRep (SpecRep (PredicateFailure (EraRule rule era)))
  , Inject (STSContext fn rule era) (Environment (EraRule rule era))
  , Inject (STSContext fn rule era) (SpecRep (Environment (EraRule rule era)))
  , Inject (STSContext fn rule era) (State (EraRule rule era))
  , Inject (STSContext fn rule era) (SpecRep (State (EraRule rule era)))
  , Inject (STSContext fn rule era) (Signal (EraRule rule era))
  , Inject (STSContext fn rule era) (SpecRep (Signal (EraRule rule era)))
  ) =>
  Property
conformsToImpl = forAllShow genCtx showExpr $ \ctx -> do
  let genEnv = inject @(STSContext fn rule era) @(Gen (Environment (EraRule rule era))) ctx
      genState = inject @(STSContext fn rule era) @(Gen (State (EraRule rule era))) ctx
      genSignal = inject @(STSContext fn rule era) @(Gen (Signal (EraRule rule era))) ctx
  forAllShow genEnv showExpr $ \env ->
    forAllShow genState showExpr $ \state ->
      forAllShow genSignal showExpr $ \signal ->
        counterexample (extraInfo @fn @rule @era ctx env state signal) $ do
          _ <- impAnn @_ @era "Deep evaluating env" $ evaluateDeep env
          _ <- impAnn "Deep evaluating st" $ evaluateDeep state
          _ <- impAnn "Deep evaluating sig" $ evaluateDeep signal

          pure ()
  where
    genCtx = genSTSContext @fn @rule @era

computationResultToEither :: Agda.ComputationResult e a -> Either e a
computationResultToEither (Agda.Success x) = Right x
computationResultToEither (Agda.Failure e) = Left e

data STSTypes rule era
  = STSTypes
      (Environment (EraRule rule era))
      (State (EraRule rule era))
      (Signal (EraRule rule era))

class GenSTSTypes fn rule era where
  genSTSTypes :: STSContext fn rule era -> Gen (STSTypes rule era)
