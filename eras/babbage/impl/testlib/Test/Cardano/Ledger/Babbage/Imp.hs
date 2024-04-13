{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Test.Cardano.Ledger.Babbage.Imp where

import Cardano.Ledger.Babbage.Rules (BabbageUtxowPredFailure (..))
import Cardano.Ledger.Babbage.TxOut (BabbageEraTxOut)
import Cardano.Ledger.Core
import Test.Cardano.Ledger.Alonzo.ImpTest
import qualified Test.Cardano.Ledger.Babbage.Imp.UtxowSpec as Utxow
import Test.Cardano.Ledger.Common

spec ::
  forall era.
  ( AlonzoEraImp era
  , BabbageEraTxOut era
  , InjectRuleFailure "LEDGER" BabbageUtxowPredFailure era
  ) =>
  Spec
spec =
  describe "BabbageImpTest" . withImpState @era $ do
    Utxow.spec @era
