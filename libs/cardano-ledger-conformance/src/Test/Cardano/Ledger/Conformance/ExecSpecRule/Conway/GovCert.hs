{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Test.Cardano.Ledger.Conformance.ExecSpecRule.Conway.GovCert (
  nameGovCert,
  adjustGStateForDormantEpochs,
) where

import Cardano.Ledger.BaseTypes
import Cardano.Ledger.CertState (VState (..))
import Cardano.Ledger.Conway
import Cardano.Ledger.Conway.TxCert
import Cardano.Ledger.Core
import Data.Bifunctor (Bifunctor (..))
import qualified Data.List.NonEmpty as NE
import qualified Data.Text as T
import qualified Lib as Agda
import Test.Cardano.Ledger.Conformance
import Test.Cardano.Ledger.Conformance.ExecSpecRule.Conway.Base
import Test.Cardano.Ledger.Constrained.Conway

instance IsConwayUniv fn => ExecSpecRule fn "GOVCERT" Conway where
  type ExecContext fn "GOVCERT" Conway = ConwayCertExecContext Conway

  environmentSpec _ctx = govCertEnvSpec

  stateSpec _ctx _env = vStateSpec

  signalSpec _ctx env st = govCertSpec env st

  classOf = Just . nameGovCert

  runAgdaRule env st sig =
    first (\e -> OpaqueErrorString (T.unpack e) NE.:| [])
      . computationResultToEither
      $ Agda.govCertStep' env st sig

  fixupAgdaResult ctx _ st sig =
    bimap (fixup <$>) (adjustGStateForDormantEpochs @fn @"GOVCERT" ctx st sig . fixup)

adjustGStateForDormantEpochs ::
  ExecContext fn rule era ->
  VState era ->
  ConwayGovCert (EraCrypto era) ->
  Agda.GState' ->
  Agda.GState'
adjustGStateForDormantEpochs
  ctx
  (VState {vsNumDormantEpochs})
  cert
  agdaSt@(Agda.MkGState' (Agda.MkHSMap ls) hks ds) =
    case cert of
      ConwayUpdateDRep cred _ ->
        let expectRight' (Right x) = x
            expectRight' (Left e) =
              error ("Failed to translate cred: " <> show cred <> ", " <> show e)
            agdaCred = expectRight' $ runSpecTransM ctx $ toSpecRep cred
            updateEpoch e = toInteger $ fromInteger e - unEpochNo vsNumDormantEpochs
            dreps = [(c, if agdaCred == c then updateEpoch e else e) | (c, e) <- ls]
         in Agda.MkGState' (Agda.MkHSMap dreps) hks ds
      _ -> agdaSt

nameGovCert :: ConwayGovCert c -> String
nameGovCert (ConwayRegDRep {}) = "ConwayRegDRep"
nameGovCert (ConwayUnRegDRep {}) = "ConwayUnRegDRep"
nameGovCert (ConwayUpdateDRep {}) = "ConwayUpdateDRep"
nameGovCert (ConwayAuthCommitteeHotKey {}) = "ConwayAuthCommitteeHotKey"
nameGovCert (ConwayResignCommitteeColdKey {}) = "ConwayResignCommitteeColdKey"
