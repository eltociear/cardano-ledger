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

module Test.Cardano.Ledger.Conformance.ExecSpecRule.Core (
  ExecSpecRule (..),
  conformsToImpl,
  generatesWithin,
  runConformance,
  checkConformance,
  defaultTestConformance,
  translateWithContext,
) where

import Cardano.Ledger.BaseTypes (Inject (..), ShelleyBase)
import Cardano.Ledger.Core (EraRule)
import qualified Constrained as CV2
import Constrained.Base (shrinkWithSpec, simplifySpec)
import Constrained.GenT (GE (..), GenMode (..))
import Control.Monad.Cont (ContT (..))
import Control.Monad.Trans (MonadTrans (..))
import Control.State.Transition.Extended (STS (..))
import Data.Bifunctor (Bifunctor (..))
import Data.Bitraversable (bimapM)
import Data.Functor (($>))
import qualified Data.Text as T
import Data.Typeable (Proxy (..), Typeable, typeRep)
import GHC.Base (Constraint, NonEmpty, Symbol, Type)
import GHC.TypeLits (KnownSymbol)
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
import UnliftIO (MonadIO (..), evaluateDeep)

type ForAllExecTypes (c :: Type -> Constraint) fn rule era =
  ( c (ExecEnvironment fn rule era)
  , c (ExecState fn rule era)
  , c (ExecSignal fn rule era)
  )

type ForAllExecSpecRep (c :: Type -> Constraint) fn rule era =
  ( c (SpecRep (ExecEnvironment fn rule era))
  , c (SpecRep (ExecState fn rule era))
  , c (SpecRep (ExecSignal fn rule era))
  )

class
  ( ForAllExecTypes (CV2.HasSpec fn) fn rule era
  , ForAllExecTypes ToExpr fn rule era
  , ForAllExecTypes NFData fn rule era
  , KnownSymbol rule
  , STS (EraRule rule era)
  , BaseM (EraRule rule era) ~ ShelleyBase
  , SpecTranslate (ExecContext fn rule era) (PredicateFailure (EraRule rule era))
  , Inject (ExecEnvironment fn rule era) (Environment (EraRule rule era))
  , Inject (ExecState fn rule era) (State (EraRule rule era))
  , Inject (ExecSignal fn rule era) (Signal (EraRule rule era))
  ) =>
  ExecSpecRule fn (rule :: Symbol) era
  where
  type ExecContext fn rule era
  type ExecContext fn rule era = ()

  type ExecEnvironment fn rule era
  type ExecEnvironment fn rule era = Environment (EraRule rule era)

  type ExecState fn rule era
  type ExecState fn rule era = State (EraRule rule era)

  type ExecSignal fn rule era
  type ExecSignal fn rule era = Signal (EraRule rule era)

  environmentSpec ::
    ExecContext fn rule era ->
    CV2.Specification fn (ExecEnvironment fn rule era)

  stateSpec ::
    ExecContext fn rule era ->
    ExecEnvironment fn rule era ->
    CV2.Specification fn (ExecState fn rule era)

  signalSpec ::
    ExecContext fn rule era ->
    ExecEnvironment fn rule era ->
    ExecState fn rule era ->
    CV2.Specification fn (ExecSignal fn rule era)

  classOf :: ExecSignal fn rule era -> Maybe String
  classOf _ = Nothing

  genExecContext :: Gen (ExecContext fn rule era)
  default genExecContext ::
    Arbitrary (ExecContext fn rule era) =>
    Gen (ExecContext fn rule era)
  genExecContext = arbitrary

  runAgdaRule ::
    SpecRep (ExecEnvironment fn rule era) ->
    SpecRep (ExecState fn rule era) ->
    SpecRep (ExecSignal fn rule era) ->
    Either
      (NonEmpty (SpecRep (PredicateFailure (EraRule rule era))))
      (SpecRep (ExecState fn rule era))

  translateInputs ::
    ExecEnvironment fn rule era ->
    ExecState fn rule era ->
    ExecSignal fn rule era ->
    ExecContext fn rule era ->
    ImpTestM
      era
      ( SpecRep (ExecEnvironment fn rule era)
      , SpecRep (ExecState fn rule era)
      , SpecRep (ExecSignal fn rule era)
      )
  default translateInputs ::
    ( ForAllExecTypes (SpecTranslate (ExecContext fn rule era)) fn rule era
    , ForAllExecSpecRep ToExpr fn rule era
    ) =>
    ExecEnvironment fn rule era ->
    ExecState fn rule era ->
    ExecSignal fn rule era ->
    ExecContext fn rule era ->
    ImpTestM
      era
      ( SpecRep (ExecEnvironment fn rule era)
      , SpecRep (ExecState fn rule era)
      , SpecRep (ExecSignal fn rule era)
      )
  translateInputs env st sig ctx = do
    let
      expectRight' (Right x) = pure x
      expectRight' (Left e) = assertFailure (T.unpack e)
    agdaEnv <- expectRight' . runSpecTransM ctx $ toSpecRep env
    logEntry $ "\n==========\nagdaENV:\n" <> showExpr agdaEnv
    agdaSt <- expectRight' . runSpecTransM ctx $ toSpecRep st
    logEntry $ "\n==========\nagdaSTATE:\n" <> showExpr agdaSt
    agdaSig <- expectRight' . runSpecTransM ctx $ toSpecRep sig
    logEntry $ "\n==========\nagdaSIGNAL:\n" <> showExpr agdaSig
    pure (agdaEnv, agdaSt, agdaSig)

  testConformance ::
    ( ShelleyEraImp era
    , SpecTranslate (ExecContext fn rule era) (State (EraRule rule era))
    , ForAllExecSpecRep NFData fn rule era
    , ForAllExecSpecRep ToExpr fn rule era
    , NFData (SpecRep (PredicateFailure (EraRule rule era)))
    , ToExpr (SpecRep (PredicateFailure (EraRule rule era)))
    , Eq (SpecRep (PredicateFailure (EraRule rule era)))
    , Eq (SpecRep (ExecState fn rule era))
    , Inject
        (State (EraRule rule era))
        (ExecState fn rule era)
    , SpecTranslate (ExecContext fn rule era) (ExecState fn rule era)
    , FixupSpecRep (SpecRep (PredicateFailure (EraRule rule era)))
    , FixupSpecRep (SpecRep (ExecState fn rule era))
    ) =>
    ExecContext fn rule era ->
    ExecEnvironment fn rule era ->
    ExecState fn rule era ->
    ExecSignal fn rule era ->
    Property
  testConformance = defaultTestConformance @fn @era @rule

  extraInfo ::
    ExecContext fn rule era ->
    Environment (EraRule rule era) ->
    State (EraRule rule era) ->
    Signal (EraRule rule era) ->
    String
  extraInfo _ _ _ _ = ""

checkConformance ::
  ( ToExpr (SpecRep (PredicateFailure (EraRule rule era)))
  , ToExpr (SpecRep (ExecState fn rule era))
  , Eq (SpecRep (PredicateFailure (EraRule rule era)))
  , Eq (SpecRep (ExecState fn rule era))
  ) =>
  Either
    (NonEmpty (SpecRep (PredicateFailure (EraRule rule era))))
    (SpecRep (ExecState fn rule era)) ->
  Either
    (NonEmpty (SpecRep (PredicateFailure (EraRule rule era))))
    (SpecRep (ExecState fn rule era)) ->
  ImpTestM era ()
checkConformance implResTest agdaResTest = do
  let
    conformancePretty =
      ansiWlPretty
        { ppDel = \d ->
            mconcat
              [ "\ESC[91m(Impl: "
              , d
              , ")\ESC[39m"
              ]
        , ppIns = \d ->
            mconcat
              [ "\ESC[92m(Agda: "
              , d
              , ")\ESC[39m"
              ]
        }
    failMsg =
      unlines
        [ ""
        , "===== DIFF ====="
        , show (ppEditExpr conformancePretty (ediff implResTest agdaResTest))
        , ""
        , "Legend:"
        , "\t\ESC[91m-Implementation"
        , "\t\ESC[92m+Specification\ESC[39m"
        ]
  unless (implResTest == agdaResTest) $ expectationFailure failMsg

defaultTestConformance ::
  forall fn era rule.
  ( ShelleyEraImp era
  , ExecSpecRule fn rule era
  , ForAllExecSpecRep NFData fn rule era
  , ForAllExecSpecRep ToExpr fn rule era
  , NFData (SpecRep (PredicateFailure (EraRule rule era)))
  , ToExpr (SpecRep (PredicateFailure (EraRule rule era)))
  , Eq (SpecRep (PredicateFailure (EraRule rule era)))
  , Eq (SpecRep (ExecState fn rule era))
  , Inject (State (EraRule rule era)) (ExecState fn rule era)
  , SpecTranslate (ExecContext fn rule era) (ExecState fn rule era)
  , FixupSpecRep (SpecRep (PredicateFailure (EraRule rule era)))
  , FixupSpecRep (SpecRep (ExecState fn rule era))
  ) =>
  ExecContext fn rule era ->
  ExecEnvironment fn rule era ->
  ExecState fn rule era ->
  ExecSignal fn rule era ->
  Property
defaultTestConformance ctx env st sig = property $ do
  (implResTest, agdaResTest) <- runConformance @rule @fn @era ctx env st sig
  checkConformance @rule @_ @fn implResTest agdaResTest

runConformance ::
  forall (rule :: Symbol) (fn :: [Type] -> Type -> Type) era.
  ( ExecSpecRule fn rule era
  , NFData (SpecRep (PredicateFailure (EraRule rule era)))
  , ForAllExecSpecRep NFData fn rule era
  , ForAllExecSpecRep ToExpr fn rule era
  , FixupSpecRep (SpecRep (PredicateFailure (EraRule rule era)))
  , FixupSpecRep (SpecRep (ExecState fn rule era))
  , Inject (State (EraRule rule era)) (ExecState fn rule era)
  , SpecTranslate (ExecContext fn rule era) (ExecState fn rule era)
  ) =>
  ExecContext fn rule era ->
  ExecEnvironment fn rule era ->
  ExecState fn rule era ->
  ExecSignal fn rule era ->
  ImpTestM
    era
    ( Either
        (NonEmpty (SpecRep (PredicateFailure (EraRule rule era))))
        (SpecRep (ExecState fn rule era))
    , Either
        (NonEmpty (SpecRep (PredicateFailure (EraRule rule era))))
        (SpecRep (ExecState fn rule era))
    )
runConformance execContext env st sig = do
  (specEnv, specSt, specSig) <-
    impAnn "Translating the inputs" $
      translateInputs @fn @rule @era env st sig execContext
  logEntry $ "\n=============\nspecENV:\n" <> showExpr specEnv
  logEntry $ "\n=============\nspecSTATE:\n" <> showExpr specSt
  logEntry $ "\n=============\nspecSIGNAL:\n" <> showExpr specSig

  let extra = extraInfo @fn @rule @era execContext (inject env) (inject st) (inject sig)
  logEntry ("\n=============\nEXTRA\n" ++ extra)

  agdaResTest <-
    fmap (bimap (fixup <$>) fixup) $
      impAnn "Deep evaluating Agda output" $
        evaluateDeep $
          runAgdaRule @fn @rule @era specEnv specSt specSig
  implRes <- tryRunImpRule @rule @era (inject env) (inject st) (inject sig)
  implResTest <-
    impAnn "Translating implementation values to SpecRep" $
      expectRightExpr $
        runSpecTransM execContext $
          bimapM (traverse toTestRep) (toTestRep . inject @_ @(ExecState fn rule era) . fst) implRes
  pure (implResTest, agdaResTest)

conformsToImpl ::
  forall (rule :: Symbol) fn era.
  ( ShelleyEraImp era
  , ExecSpecRule fn rule era
  , ForAllExecSpecRep NFData fn rule era
  , ForAllExecSpecRep ToExpr fn rule era
  , NFData (SpecRep (PredicateFailure (EraRule rule era)))
  , NFData (ExecContext fn rule era)
  , ToExpr (SpecRep (PredicateFailure (EraRule rule era)))
  , ToExpr (ExecContext fn rule era)
  , SpecTranslate (ExecContext fn rule era) (State (EraRule rule era))
  , Eq (SpecRep (PredicateFailure (EraRule rule era)))
  , Inject (State (EraRule rule era)) (ExecState fn rule era)
  , Eq (SpecRep (ExecState fn rule era))
  , SpecTranslate (ExecContext fn rule era) (ExecState fn rule era)
  , FixupSpecRep (SpecRep (PredicateFailure (EraRule rule era)))
  , FixupSpecRep (SpecRep (ExecState fn rule era))
  ) =>
  Property
conformsToImpl = property @(ImpTestM era Property) . (`runContT` pure) $ do
  let
    deepEvalAnn s = "Deep evaluating " <> s
    deepEval x s = do
      _ <- lift $ impAnn (deepEvalAnn s) (liftIO (evaluateDeep x))
      pure ()
  ctx <- ContT $ \c ->
    pure $ forAllShow (genExecContext @fn @rule @era) showExpr c
  deepEval ctx "context"
  let
    forAllSpec spec = do
      let
        simplifiedSpec = simplifySpec spec
        generator = CV2.runGenT (CV2.genFromSpecT simplifiedSpec) Loose
        shrinker (Result _ x) = pure <$> shrinkWithSpec simplifiedSpec x
        shrinker _ = []
        shower (Result _ x) = showExpr x
        shower e = show e
      res :: GE a <- ContT $ \c ->
        pure $ forAllShrinkShow generator shrinker shower c
      case res of
        Result _ x -> pure x
        _ -> ContT . const . pure $ property Discard
  env <- forAllSpec $ environmentSpec @fn @rule @era ctx
  deepEval env "environment"
  st <- forAllSpec $ stateSpec @fn @rule @era ctx env
  deepEval st "state"
  sig <- forAllSpec $ signalSpec @fn @rule @era ctx env st
  deepEval sig "signal"
  let extra = extraInfo @fn @rule @era ctx (inject env) (inject st) (inject sig)
  let classification =
        case classOf @fn @rule @era sig of
          Nothing -> classify False "None"
          Just c -> classify True c
  lift $ logEntry ("\n=============EXTRA\n" ++ extra)
  pure . classification $
    testConformance @fn @rule @era ctx env st sig

generatesWithin ::
  forall a.
  ( NFData a
  , ToExpr a
  , Typeable a
  ) =>
  Gen a ->
  Int ->
  Spec
generatesWithin gen timeout =
  prop (aName <> " generates in reasonable time")
    . forAllShow gen showExpr
    $ \x -> within timeout $ ioProperty (evaluateDeep x $> ())
  where
    aName = show (typeRep $ Proxy @a)

-- | Translate a Haskell type 'a' whose translation context is 'ctx' into its Agda type, in the ImpTest monad.
translateWithContext :: SpecTranslate ctx a => ctx -> a -> ImpTestM era (SpecRep a)
translateWithContext ctx x = do
  let
    expectRight' (Right y) = pure y
    expectRight' (Left e) = assertFailure (T.unpack e)
  ans <- expectRight' . runSpecTransM ctx $ toSpecRep x
  pure ans
