{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Test.Cardano.Ledger.Conformance.ExecSpecRule.Conway.Cert (nameTxCert) where

import Cardano.Ledger.CertState (CertState (..))
import Cardano.Ledger.Conway
import Cardano.Ledger.Conway.TxCert
import Data.Bifunctor (bimap, first)
import qualified Data.List.NonEmpty as NE
import qualified Data.Text as T
import qualified Lib as Agda
import Test.Cardano.Ledger.Conformance
import Test.Cardano.Ledger.Conformance.ExecSpecRule.Conway.Base
import Test.Cardano.Ledger.Conformance.ExecSpecRule.Conway.Deleg (nameDelegCert)
import Test.Cardano.Ledger.Conformance.ExecSpecRule.Conway.GovCert (
  adjustGStateForDormantEpochs,
  nameGovCert,
 )
import Test.Cardano.Ledger.Conformance.ExecSpecRule.Conway.Pool (namePoolCert)
import Test.Cardano.Ledger.Constrained.Conway

instance
  IsConwayUniv fn =>
  ExecSpecRule fn "CERT" Conway
  where
  type ExecContext fn "CERT" Conway = ConwayCertExecContext Conway
  environmentSpec _ = certEnvSpec
  stateSpec _ _ = certStateSpec
  signalSpec _ env st = txCertSpec env st
  runAgdaRule env st sig =
    first (\e -> OpaqueErrorString (T.unpack e) NE.:| [])
      . computationResultToEither
      $ Agda.certStep' env st sig

  fixupAgdaResult ctx _ CertState {certVState} sig =
    bimap (fixup <$>) (updateCertState . fixup)
    where
      updateCertState =
        case sig of
          ConwayTxCertGov govCert -> updateGState govCert
          _ -> id
      updateGState govCert cs =
        cs
          { Agda.gState' =
              adjustGStateForDormantEpochs @fn @"CERT" ctx certVState govCert (Agda.gState' cs)
          }

  classOf = Just . nameTxCert

nameTxCert :: ConwayTxCert Conway -> String
nameTxCert (ConwayTxCertDeleg x) = nameDelegCert x
nameTxCert (ConwayTxCertPool x) = namePoolCert x
nameTxCert (ConwayTxCertGov x) = nameGovCert x
