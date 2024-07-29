{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Test.Cardano.Ledger.Conformance.Spec.Conway (spec) where

import Cardano.Ledger.Conway (Conway)
import qualified Constrained as CV2
import Data.Functor (($>))
import Data.Typeable (Proxy (..), Typeable, typeRep)
import Test.Cardano.Ledger.Conformance (ExecSpecRule (..), conformsToImpl)
import Test.Cardano.Ledger.Conformance.ExecSpecRule.Conway ()
import qualified Test.Cardano.Ledger.Conformance.ExecSpecRule.MiniTrace as MiniTrace
import Test.Cardano.Ledger.Constrained.Conway
import Test.Cardano.Ledger.Conway.ImpTest ()
import Test.Cardano.Ledger.Imp.Common
import UnliftIO (evaluateDeep)

spec :: Spec
spec = do
  describe "MiniTrace" MiniTrace.spec
  describe "Generators" $ do
    let
      genEnv = do
        ctx <- genExecContext @ConwayFn @"GOV" @Conway
        CV2.genFromSpec $ environmentSpec @ConwayFn @"GOV" @Conway ctx
      genSt = do
        ctx <- genExecContext @ConwayFn @"GOV" @Conway
        env <- genEnv
        CV2.genFromSpec $ stateSpec @ConwayFn @"GOV" @Conway ctx env
      genSig = do
        ctx <- genExecContext @ConwayFn @"GOV" @Conway
        env <- genEnv
        st <- genSt
        CV2.genFromSpec $ signalSpec @ConwayFn @"GOV" @Conway ctx env st
    genEnv `generatesWithin` 3_000_000
    genSt `generatesWithin` 40_000_000
    genSig `generatesWithin` 60_000_000
  describe "Conformance" $ do
    describe "Ticks transition graph" $ do
      pure ()
      xprop "ENACT" $ conformsToImpl @"ENACT" @ConwayFn @Conway
    -- xprop "RATIFY" $ conformsToImpl @"RATIFY" @ConwayFn @Conway
    -- xprop "EPOCH" $ conformsToImpl @"EPOCH" @ConwayFn @Conway
    -- xprop "NEWEPOCH" $ conformsToImpl @"NEWEPOCH" @ConwayFn @Conway
    describe "Blocks transition graph" $ do
      pure ()

-- prop "DELEG" $ conformsToImpl @"DELEG" @ConwayFn @Conway
-- GOVCERT is disabled because the Agda MALONZO code has a bug
-- when accessing the PParams DRepActivity field. When that is fixed
-- we can turn xprop to prop for "GOVCERT"
-- xprop "GOVCERT" $ conformsToImpl @"GOVCERT" @ConwayFn @Conway
-- prop "POOL" $ conformsToImpl @"POOL" @ConwayFn @Conway
-- The PParams DRepActivity field bug in Agda means we must also
-- turn off the "CERT" conformance test because "CERT" contains "GOVCERT"
-- When that is fixed we can turn xprop to prop for "CERT"
-- xprop "CERT" $ conformsToImpl @"CERT" @ConwayFn @Conway
-- xprop "CERTS" $ conformsToImpl @"CERTS" @ConwayFn @Conway
-- prop "GOV" $ conformsToImpl @"GOV" @ConwayFn @Conway
-- xprop "UTXO" $ conformsToImpl @"UTXO" @ConwayFn @Conway

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
