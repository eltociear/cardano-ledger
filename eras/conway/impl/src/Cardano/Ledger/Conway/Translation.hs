{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}

{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-unused-local-binds #-}

module Cardano.Ledger.Conway.Translation where

import Cardano.Ledger.Allegra.Scripts (translateTimelock)
import Cardano.Ledger.Alonzo.Scripts (AlonzoScript (..))
import Cardano.Ledger.Alonzo.Tx (AlonzoEraTx (..))
import Cardano.Ledger.Babbage (BabbageEra)
import Cardano.Ledger.Babbage.TxBody (BabbageTxOut (..), Datum (..))
import Cardano.Ledger.Binary (DecoderError)
import Cardano.Ledger.Conway.Core hiding (Tx)
import Cardano.Ledger.Conway.Era (ConwayEra)
import Cardano.Ledger.Conway.Scripts ()
import Cardano.Ledger.Conway.Tx ()
import qualified Cardano.Ledger.Core as Core (Tx)
import Cardano.Ledger.Crypto (Crypto)
import Cardano.Ledger.Shelley.API (
  DPState (..),
  DState (..),
  EpochState (..),
  NewEpochState (..),
  StrictMaybe (..),
  UTxOState (..), LedgerState (..), IncrementalStake (..), KeyRole (..)
 )
import qualified Cardano.Ledger.Shelley.API as API
import Data.Coerce
import qualified Data.Map.Strict as Map
import Lens.Micro
import Data.Set (Set, elemAt)
import Cardano.Ledger.Credential (Ptr, Credential)
import qualified Cardano.Ledger.Val as Val ((<->))

--------------------------------------------------------------------------------
-- Translation from Babbage to Conway
--
-- The instances below are needed by the consensus layer. Do not remove any of
-- them without coordinating with consensus.
--
-- Please add auxiliary instances and other declarations at the bottom of this
-- module, not in the list below so that it remains clear which instances the
-- consensus layer needs.
--
-- WARNING: when a translation instance currently uses the default
-- 'TranslationError', i.e., 'Void', it means the consensus layer relies on it
-- being total. Do not change it!
--------------------------------------------------------------------------------

type instance TranslationContext (ConwayEra c) = API.GenDelegs c

instance Crypto c => TranslateEra (ConwayEra c) NewEpochState where
  translateEra ctxt nes =
    pure $
      NewEpochState
        { nesEL = nesEL nes
        , nesBprev = nesBprev nes
        , nesBcur = nesBcur nes
        , nesEs = translateEra' ctxt $ nesEs nes
        , nesRu = nesRu nes
        , nesPd = nesPd nes
        , stashedAVVMAddresses = ()
        }

newtype Tx era = Tx {unTx :: Core.Tx era}

instance Crypto c => TranslateEra (ConwayEra c) Tx where
  type TranslationError (ConwayEra c) Tx = DecoderError
  translateEra _ctxt (Tx tx) = do
    -- Note that this does not preserve the hidden bytes field of the transaction.
    -- This is under the premise that this is irrelevant for TxInBlocks, which are
    -- not transmitted as contiguous chunks.
    txBody <- translateEraThroughCBOR "TxBody" $ tx ^. bodyTxL
    txWits <- translateEraThroughCBOR "TxWitness" $ tx ^. witsTxL
    auxData <- case tx ^. auxDataTxL of
      SNothing -> pure SNothing
      SJust auxData -> SJust <$> translateEraThroughCBOR "AuxData" auxData
    let isValidTx = tx ^. isValidTxL
        newTx =
          mkBasicTx txBody
            & witsTxL .~ txWits
            & isValidTxL .~ isValidTx
            & auxDataTxL .~ auxData
    pure $ Tx newTx

--------------------------------------------------------------------------------
-- Auxiliary instances and functions
--------------------------------------------------------------------------------

instance Crypto c => TranslateEra (ConwayEra c) PParams where
  translateEra _ = pure . upgradePParams ()

instance Crypto c => TranslateEra (ConwayEra c) EpochState where
  translateEra ctxt es =
    pure
      EpochState
        { esAccountState = esAccountState es
        -- ???: do we have to also adjust the snapshots?
        , esSnapshots = esSnapshots es
        , esLState = translateEra' ctxt $ esLState es
        , esPrevPp = upgradePParams () $ esPrevPp es
        , esPp = upgradePParams () $ esPp es
        , esNonMyopic = esNonMyopic es
        }

instance Crypto c => TranslateEra (ConwayEra c) API.LedgerState where
  translateEra newGenDelegs ls =
    pure
      API.LedgerState
        { API.lsUTxOState = translateEra' newGenDelegs $ API.lsUTxOState ls
        , API.lsDPState = updateGenesisKeys $ API.lsDPState ls
        }
    where
      updateGenesisKeys (DPState dstate pstate) = DPState dstate' pstate
        where
          dstate' = dstate {dsGenDelegs = newGenDelegs}

instance Crypto c => TranslateEra (ConwayEra c) UTxOState where
  translateEra ctxt us =
    pure
      UTxOState
        { API.utxosUtxo = translateEra' ctxt $ API.utxosUtxo us
        , API.utxosDeposited = API.utxosDeposited us
        , API.utxosFees = API.utxosFees us
        , API.utxosGovernance = emptyGovernanceState
        , API.utxosStakeDistr = adjustIncrStake (API.utxosPtrs us) (API.utxosStakeDistr us) undefined
        , API.utxosPtrs = API.utxosPtrs us
        }

instance Crypto c => TranslateEra (ConwayEra c) API.UTxO where
  translateEra _ctxt utxo =
    pure $ API.UTxO $ translateTxOut `Map.map` API.unUTxO utxo

instance Crypto c => TranslateEra (ConwayEra c) API.ProposedPPUpdates where
  translateEra _ctxt (API.ProposedPPUpdates ppup) =
    pure $ API.ProposedPPUpdates $ fmap (upgradePParamsUpdate ()) ppup

translateTxOut ::
  Crypto c =>
  TxOut (BabbageEra c) ->
  TxOut (ConwayEra c)
translateTxOut (BabbageTxOut addr value d s) =
  BabbageTxOut addr value (translateDatum d) (translateScript <$> s)

translateDatum :: Datum (BabbageEra c) -> Datum (ConwayEra c)
translateDatum = \case
  NoDatum -> NoDatum
  DatumHash dh -> DatumHash dh
  Datum bd -> Datum (coerce bd)

translateScript :: Crypto c => Script (BabbageEra c) -> Script (ConwayEra c)
translateScript = \case
  TimelockScript ts -> TimelockScript $ translateTimelock ts
  PlutusScript l sbs -> PlutusScript l sbs

adjustIncrStake ::
  Set Ptr ->
  IncrementalStake (EraCrypto (BabbageEra c)) ->
  Map.Map Ptr (Credential 'Staking (EraCrypto (ConwayEra c))) ->
  IncrementalStake (EraCrypto (ConwayEra c))
adjustIncrStake ptrs incrStake@(IStake credMap ptrMap) ptrToCredsMap =
  let
      firstPtr = elemAt 0 ptrs --TODO: replace with fold, to do it for ptrs in the set
      cred = Map.lookup firstPtr ptrToCredsMap
      ptrVal = Map.lookup firstPtr ptrMap
      adjust :: API.Coin -> Credential 'Staking (EraCrypto (BabbageEra c)) -> API.Coin -> API.Coin
      adjust toSubtract c v = (Val.<->) v toSubtract
      updatedCredMap = case (cred, ptrVal) of
         (Just c, Just v) -> Map.adjustWithKey (adjust v) c credMap
         _ -> credMap
  in IStake updatedCredMap ptrMap --todo: should we remove the ptr from ptrMap?
      -- f :: IncrementalStake (EraCrypto (BabbageEra c)) -> Ptr -> IncrementalStake (EraCrypto (BabbageEra c))
      -- f (IStake credMap ptrMap) ptr = undefined


incrStakeEpochStateL :: Lens' (EpochState era) (API.IncrementalStake (EraCrypto era))
incrStakeEpochStateL =
  lens
    (\es -> (utxosStakeDistr . lsUTxOState . esLState) es)
    (\es incrStake -> es {esLState = (esLState es) {lsUTxOState = ((lsUTxOState . esLState) es) {utxosStakeDistr = incrStake}} })
