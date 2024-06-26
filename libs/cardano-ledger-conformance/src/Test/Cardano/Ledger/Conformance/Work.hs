{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Specs necessary to generate, environment, state, and signal
-- for the GOVCERT rule
module Test.Cardano.Ledger.Conformance.Work where

import Cardano.Ledger.CertState
import Cardano.Ledger.Conway
import Cardano.Ledger.Conway.Governance
import Cardano.Ledger.Conway.PParams
import Cardano.Ledger.Conway.Rules
import Cardano.Ledger.Conway.TxCert
import qualified Data.Map as Map
import Lens.Micro
import Test.Cardano.Ledger.Conformance
import Test.Cardano.Ledger.Conformance.ExecSpecRule.Conway ()
import Test.Cardano.Ledger.Generic.PrettyCore
import Test.QuickCheck

import Constrained

import Cardano.Ledger.Conway (ConwayEra)
import Cardano.Ledger.Crypto (StandardCrypto)
import Test.Cardano.Ledger.Constrained.Conway.Instances
import Test.Cardano.Ledger.Constrained.Conway.PParams

main :: IO ()
main = do
  ctx <- generate (arbitrary) -- :: Gen (ConwayCertExecContext Conway))
  env <- generate $ genFromSpec $ environmentSpec @ConwayFn @"GOVCERT" @Conway ctx
  state <- generate $ genFromSpec $ stateSpec @ConwayFn @"GOVCERT" @Conway ctx env
  signal <- generate $ genFromSpec $ signalSpec @ConwayFn @"GOVCERT" @Conway ctx env state
  putStrLn $ show $ prettyA signal

-- env <- generate $ genFromSpec $  govCertEnvSpec @ConwayFn
-- vState <- generate $ genFromSpec $  vStateSpec @ConwayFn
-- govCert <- generate $ genFromSpec $ govCertSpec @ConwayFn env vState
