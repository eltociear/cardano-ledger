{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-deprecations #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

-- |
-- Module      : Test.Cardano.Ledger.Shelley.Examples.Updates
-- Description : Protocol Parameter Update Example
--
-- Example demonstrating using the protocol parameter update system.
module Test.Cardano.Ledger.Conway.Examples.Prototype where

import Cardano.Ledger.Allegra.Scripts (Timelock (RequireAllOf))
import Cardano.Ledger.Alonzo.Data (
  AuxiliaryDataHash (AuxiliaryDataHash),
  Datum (NoDatum),
  mkAlonzoTxAuxData,
 )
import Cardano.Ledger.Alonzo.Tx (IsValid (IsValid))
import Cardano.Ledger.Alonzo.TxWits (Redeemers (Redeemers), TxDats (TxDats))
import Cardano.Ledger.Babbage
import Cardano.Ledger.Babbage.TxBody (BabbageTxOut (..))
import Cardano.Ledger.BaseTypes (
  EpochInterval (EpochInterval),
  Network (Mainnet),
  Nonce,
  StrictMaybe (..),
  WithOrigin (At),
 )
import Cardano.Ledger.Binary (mkSized)
import Cardano.Ledger.Block (Block)
import Cardano.Ledger.Coin (Coin (..))
import Cardano.Ledger.Conway (Conway, ConwayEra)
import Cardano.Ledger.Conway.Core
import Cardano.Ledger.Conway.Genesis (ConwayGenesis)
import Cardano.Ledger.Conway.Governance (VotingProcedures (VotingProcedures))
import Cardano.Ledger.Conway.Scripts (
  AlonzoScript (TimelockScript),
  ConwayPlutusPurpose (ConwaySpending),
 )
import Cardano.Ledger.Conway.Tx (AlonzoTx (AlonzoTx))
import Cardano.Ledger.Conway.TxBody
import Cardano.Ledger.Conway.TxWits (AlonzoTxWits (AlonzoTxWits))
import Cardano.Ledger.Crypto
import Cardano.Ledger.Keys (
  GenDelegPair (GenDelegPair),
  Hash,
  KeyPair (KeyPair),
  KeyRole (GenesisDelegate),
  VerKeyVRF,
  asWitness,
  hashKey,
  vKey,
 )
import Cardano.Ledger.Mary.Value (MaryValue (MaryValue))
import Cardano.Ledger.Plutus (Datum (Datum), Language (PlutusV1), dataToBinaryData)
import Cardano.Ledger.Plutus.Data (Data (Data), hashData)
import Cardano.Ledger.Plutus.ExUnits (ExUnits (ExUnits))
import Cardano.Ledger.Plutus.Language (Language (PlutusV2))
import Cardano.Ledger.SafeHash (hashAnnotated)
import Cardano.Ledger.Shelley.API (hashVerKeyVRF)
import Cardano.Ledger.Shelley.API.Types (Network (Testnet))
import Cardano.Ledger.Shelley.LedgerState (
  FutureGenDeleg (FutureGenDeleg),
  NewEpochState,
  StashedAVVMAddresses,
 )
import Cardano.Ledger.Shelley.Tx (ShelleyTx (ShelleyTx))
import Cardano.Ledger.Shelley.TxBody (RewardAccount (RewardAccount))
import Cardano.Ledger.Slot (
  BlockNo (..),
  EpochNo (..),
  SlotNo (..),
 )
import Cardano.Ledger.TxIn (TxId (TxId), mkTxInPartial)
import Cardano.Ledger.UTxO (UTxO (..), balance)
import Cardano.Ledger.Val ((<->))
import qualified Cardano.Ledger.Val as Val
import Cardano.Protocol.TPraos.API (PraosCrypto)
import Cardano.Protocol.TPraos.BHeader (
  BHeader,
  HashHeader (HashHeader),
  LastAppliedBlock (LastAppliedBlock),
  hashHeaderToNonce,
 )
import Cardano.Protocol.TPraos.OCert (KESPeriod (..))
import Data.Default.Class (Default)
import qualified Data.Map.Strict as Map
import Data.Proxy (Proxy (Proxy))
import qualified Data.Sequence.Strict as StrictSeq
import qualified Data.Set as Set
import GHC.Stack (HasCallStack)
import Lens.Micro ((&), (.~))
import qualified PlutusLedgerApi.Common as P
import Test.Cardano.Ledger.Alonzo.Arbitrary (alwaysFails)
import Test.Cardano.Ledger.Alonzo.Scripts (alwaysSucceeds)
import Test.Cardano.Ledger.Conway.Examples
import Test.Cardano.Ledger.Conway.Examples.Combinators (evolveNonceUnfrozen, newLab)
import qualified Test.Cardano.Ledger.Conway.Examples.Combinators as C
import Test.Cardano.Ledger.Conway.Examples.Consensus (exampleConwayCerts)
import Test.Cardano.Ledger.Conway.Genesis (expectedConwayGenesis)
import Test.Cardano.Ledger.Conway.Rules.Chain (ChainState, initialConwayState)
import Test.Cardano.Ledger.Core.KeyPair (mkAddr, mkWitnessesVKey)
import Test.Cardano.Ledger.Core.Utils (unsafeBoundRational)
import qualified Test.Cardano.Ledger.Mary.Examples.Consensus as MarySLE
import Test.Cardano.Ledger.Shelley.ConcreteCryptoTypes (ExMock)
import qualified Test.Cardano.Ledger.Shelley.Examples.Cast as Cast
import qualified Test.Cardano.Ledger.Shelley.Examples.Consensus as SLE
import Test.Cardano.Ledger.Shelley.Examples.Federation (
  coreNodeKeysBySchedule,
  coreNodeVK,
  genDelegs,
 )
import Test.Cardano.Ledger.Shelley.Generator.Core (
  NatNonce (..),
  RawSeed (RawSeed),
  VRFKeyPair (vrfVerKey),
  genesisCoins,
  mkBlockFakeVRF,
  mkOCert,
 )
import Test.Cardano.Ledger.Shelley.Generator.EraGen (genesisId)
import Test.Cardano.Ledger.Shelley.Generator.ShelleyEraGen ()
import Test.Cardano.Ledger.Shelley.Generator.Trace.Chain ()
import Test.Cardano.Ledger.Shelley.Utils (
  getBlockNonce,
  maxLLSupply,
  mkDummySafeHash,
  mkHash,
  mkKeyPair,
  mkVRFKeyPair,
 )

------------------

initUTxO :: EraTxOut era => UTxO era
initUTxO =
  genesisCoins
    genesisId
    [ mkBasicTxOut Cast.aliceAddr aliceInitCoin
    , mkBasicTxOut Cast.bobAddr bobInitCoin
    ]
  where
    aliceInitCoin = Val.inject $ Coin $ 10 * 1000 * 1000 * 1000 * 1000 * 1000
    bobInitCoin = Val.inject $ Coin $ 1 * 1000 * 1000 * 1000 * 1000 * 1000

initStEx1 ::
  ( EraTxOut era
  , Default (StashedAVVMAddresses era)
  , EraGov era
  ) =>
  ChainState era
initStEx1 = initSt (UTxO mempty) -- initUTxO

blockEx1 ::
  forall era.
  ( EraSegWits era
  , Tx era ~ AlonzoTx Conway
  , PraosCrypto (EraCrypto era)
  ) =>
  Block (BHeader (EraCrypto era)) era
blockEx1 = SLE.exampleShelleyLedgerBlockTxs mempty -- exampleTransactionInBlock

exampleTransactionInBlock :: AlonzoTx Conway
exampleTransactionInBlock = AlonzoTx b w (IsValid True) a
  where
    ShelleyTx b w a = exampleTx

blockNonce ::
  forall era.
  ( EraSegWits era
  , Tx era ~ AlonzoTx Conway
  , PraosCrypto (EraCrypto era)
  ) =>
  Nonce
blockNonce = getBlockNonce (blockEx1 @era)

expectedStEx1 ::
  forall era.
  ( EraSegWits era
  , EraGov era
  , Default (StashedAVVMAddresses era)
  , Tx era ~ AlonzoTx Conway
  , PraosCrypto (EraCrypto era)
  ) =>
  ChainState era
expectedStEx1 = evolveNonceUnfrozen (blockNonce @era) . newLab blockEx1 $ initStEx1

-- | = Empty Block Example
--
-- This is the most minimal example of using the CHAIN STS transition.
-- It applies an empty block to an initial shelley chain state.
--
-- The only things that change in the chain state are the
-- evolving and candidate nonces, and the last applied block.
exEmptyBlock ::
  ( EraSegWits era
  , Default (StashedAVVMAddresses era)
  , EraGov era
  , Tx era ~ AlonzoTx Conway
  , PraosCrypto (EraCrypto era)
  ) =>
  CHAINExample (BHeader (EraCrypto era)) era
exEmptyBlock = CHAINExample initStEx1 blockEx1 (Right expectedStEx1)

-- ------------------
-- initUTxO :: EraTxOut era => UTxO era
-- initUTxO =
--   genesisCoins
--     genesisId
--     [ mkBasicTxOut Cast.aliceAddr aliceInitCoin
--     , mkBasicTxOut Cast.bobAddr bobInitCoin
--     ]
--   where
--     aliceInitCoin = Val.inject $ Coin $ 10 * 1000 * 1000 * 1000 * 1000 * 1000
--     bobInitCoin = Val.inject $ Coin $ 1 * 1000 * 1000 * 1000 * 1000 * 1000

-- initStGenesisDeleg ::
--   ( EraTxOut era
--   , EraGov era
--   , Default (StashedAVVMAddresses era)
--   ) =>
--   ChainState era
-- initStGenesisDeleg = initSt initUTxO

-- --
-- -- Block 1, Slot 10, Epoch 0
-- --

-- newGenDelegate ::
--   Crypto c =>
--   KeyPair 'GenesisDelegate c
-- newGenDelegate = KeyPair vkCold skCold
--   where
--     (skCold, vkCold) = mkKeyPair (RawSeed 108 0 0 0 1)

-- newGenesisVrfKH :: forall c. Crypto c => Hash c (VerKeyVRF c)
-- newGenesisVrfKH = hashVerKeyVRF (vrfVerKey (mkVRFKeyPair @c (RawSeed 9 8 7 6 5)))

-- feeTx1 :: Coin
-- feeTx1 = Coin 1

-- blockEx1 ::
--   forall c.
--   ExMock (EraCrypto (ConwayEra c)) =>
--   Block (BHeader c) (ConwayEra c)
-- blockEx1 =
--   mkBlockFakeVRF @(ConwayEra c)
--     lastByronHeaderHash
--     (coreNodeKeysBySchedule @(ConwayEra c) ppEx 10)
--     [txEx1]
--     (SlotNo 10)
--     (BlockNo 1)
--     (nonce0 @c)
--     (NatNonce 1)
--     minBound
--     0
--     0
--     (mkOCert @c (coreNodeKeysBySchedule @(ConwayEra c) ppEx 10) 0 (KESPeriod 0))

-- txEx1 :: forall c. ExMock (EraCrypto (ConwayEra c)) => AlonzoTx (ConwayEra c)
-- txEx1 =
--   AlonzoTx
--     exampleTxBodyConway
--     ( AlonzoTxWits
--         (mkWitnessesVKey (hashAnnotated exampleTxBodyConway) [asWitness SLE.examplePayKey]) -- vkey
--         mempty -- bootstrap
--         ( Map.singleton
--             (hashScript @(ConwayEra c) $ alwaysSucceeds @'PlutusV1 3)
--             (alwaysSucceeds @'PlutusV1 3) -- txscripts
--         )
--         (TxDats $ Map.singleton (hashData datumExample) datumExample)
--         ( Redeemers $
--             Map.singleton (ConwaySpending $ AsIx 0) (redeemerExample, ExUnits 5000 5000)
--         ) -- redeemers
--     )
--     (IsValid True)
--     SNothing

-- newGenDeleg ::
--   forall c.
--   Crypto c =>
--   (FutureGenDeleg c, GenDelegPair c)
-- newGenDeleg =
--   ( FutureGenDeleg (SlotNo 43) (hashKey $ coreNodeVK 0)
--   , GenDelegPair (hashKey . vKey $ newGenDelegate) (newGenesisVrfKH @c)
--   )

-- expectedStEx1 ::
--   forall c.
--   ExMock (EraCrypto (ConwayEra c)) =>
--   ChainState (ConwayEra c)
-- expectedStEx1 =
--   C.evolveNonceUnfrozen (getBlockNonce @(ConwayEra c) blockEx1)
--     . C.newLab blockEx1
--     . C.feesAndDeposits ppEx feeTx1 [] []
--     . C.newUTxO exampleTxBodyConway
--     . C.setFutureGenDeleg newGenDeleg
--     $ initStGenesisDeleg

-- -- === Block 1, Slot 10, Epoch 0
-- --
-- -- In the first block, stage a new future genesis delegate
-- genesisDelegation1 ::
--   ExMock (EraCrypto (ConwayEra c)) =>
--   CHAINExample (BHeader c) (ConwayEra c)
-- genesisDelegation1 = CHAINExample initStGenesisDeleg blockEx1 (Right expectedStEx1)

collateralOutput :: Crypto c => BabbageTxOut (ConwayEra c)
collateralOutput =
  BabbageTxOut
    (mkAddr (SLE.examplePayKey, SLE.exampleStakeKey))
    (MaryValue (Coin 8675309) mempty)
    NoDatum
    SNothing

testOutput :: Crypto c => BabbageTxOut (ConwayEra c)
testOutput =
  BabbageTxOut
    (mkAddr (SLE.examplePayKey, SLE.exampleStakeKey))
    (MarySLE.exampleMultiAssetValue 2)
    (Datum $ dataToBinaryData datumExample) -- inline datum
    (SJust $ alwaysSucceeds @'PlutusV2 3) -- reference script

exampleTxBodyConway :: forall c. Crypto c => ConwayTxBody (ConwayEra c)
exampleTxBodyConway =
  ConwayTxBody
    (Set.fromList [mkTxInPartial (TxId (mkDummySafeHash Proxy 1)) 0]) -- spending inputs
    (Set.fromList [mkTxInPartial (TxId (mkDummySafeHash Proxy 2)) 1]) -- collateral inputs
    (Set.fromList [mkTxInPartial (TxId (mkDummySafeHash Proxy 1)) 3]) -- reference inputs
    ( StrictSeq.fromList
        [ mkSized (eraProtVerHigh @Conway) testOutput
        -- BabbageTxOut
        --   (mkAddr @c (SLE.examplePayKey, SLE.exampleStakeKey))
        --   (MarySLE.exampleMultiAssetValue 2)
        --   (Datum $ dataToBinaryData datumExample) -- inline datum
        --   (SJust $ alwaysSucceeds @'PlutusV2 3) -- reference script
        ]
    )
    (SJust $ mkSized (eraProtVerHigh @Conway) collateralOutput) -- collateral return
    (SJust $ Coin 8675309) -- collateral tot
    exampleConwayCerts -- txcerts
    ( Withdrawals $
        Map.singleton
          (RewardAccount Testnet (SLE.keyToCredential SLE.exampleStakeKey))
          (Coin 100) -- txwdrls
    )
    (Coin 999) -- txfee
    (ValidityInterval (SJust (SlotNo 2)) (SJust (SlotNo 4))) -- txvldt
    (Set.singleton $ SLE.mkKeyHash 212) -- reqSignerHashes
    exampleMultiAsset -- mint
    (SJust $ mkDummySafeHash (Proxy @c) 42) -- scriptIntegrityHash
    (SJust . AuxiliaryDataHash $ mkDummySafeHash (Proxy @c) 42) -- adHash
    (SJust Mainnet) -- txnetworkid
    (VotingProcedures mempty)
    mempty
    (SJust $ Coin 867530900000) -- current treasury value
    mempty
    mempty
    mempty
    mempty
  where
    MaryValue _ exampleMultiAsset = MarySLE.exampleMultiAssetValue 3

datumExample :: Crypto c => Data (ConwayEra c)
datumExample = Data (P.I 191)

redeemerExample :: Crypto c => Data (ConwayEra c)
redeemerExample = Data (P.I 919)

exampleTx :: ShelleyTx Conway
exampleTx =
  ShelleyTx
    exampleTxBodyConway
    ( AlonzoTxWits
        (mkWitnessesVKey (hashAnnotated exampleTxBodyConway) [asWitness SLE.examplePayKey]) -- vkey
        mempty -- bootstrap
        ( Map.singleton
            (hashScript @Conway $ alwaysSucceeds @'PlutusV1 3)
            (alwaysSucceeds @'PlutusV1 3) -- txscripts
        )
        (TxDats $ Map.singleton (hashData datumExample) datumExample)
        ( Redeemers $
            Map.singleton (ConwaySpending $ AsIx 0) (redeemerExample, ExUnits 5000 5000)
        ) -- redeemers
    )
    ( SJust $
        mkAlonzoTxAuxData
          SLE.exampleAuxDataMap -- metadata
          [alwaysFails @'PlutusV1 2, TimelockScript $ RequireAllOf mempty] -- Scripts
    )

-- ------

-- | Initial Protocol Parameters
ppEx :: EraPParams era => PParams era
ppEx =
  emptyPParams
    & ppMaxBBSizeL
    .~ 50000
    & ppMaxBHSizeL
    .~ 10000
    & ppMaxTxSizeL
    .~ 10000
    & ppEMaxL
    .~ EpochInterval 10000
    & ppKeyDepositL
    .~ Coin 7
    & ppPoolDepositL
    .~ Coin 250
    & ppTauL
    .~ unsafeBoundRational 0.2
    & ppRhoL
    .~ unsafeBoundRational 0.0021

-- | === The hash of the last Bryon Header
--
-- The first block of the Shelley era will point back to the
-- last block of the Byron era.
-- For our purposes in the examples we can bootstrap the chain
-- by just coercing the value.
-- When this transition actually occurs,
-- the consensus layer will do the work of making
-- sure that the hash gets translated across the fork.
lastByronHeaderHash ::
  forall c.
  Crypto c =>
  HashHeader c
lastByronHeaderHash = HashHeader $ mkHash 0

-- | === Initial Nonce
nonce0 ::
  forall c.
  Crypto c =>
  Nonce
nonce0 = hashHeaderToNonce (lastByronHeaderHash @c)

-- | === Initial Chain State
--
-- The initial state for the examples uses the function
-- 'initialShelleyState' with the genesis delegation
-- 'genDelegs' and any given starting 'UTxO' set.
initSt ::
  forall era.
  ( EraTxOut era
  , Default (StashedAVVMAddresses era)
  , EraGov era
  ) =>
  UTxO era ->
  ChainState era
initSt utxo =
  initialConwayState
    (At $ LastAppliedBlock (BlockNo 0) (SlotNo 0) lastByronHeaderHash)
    (EpochNo 0)
    utxo
    (maxLLSupply <-> Val.coin (balance utxo))
    genDelegs
    (ppEx @era)
    (nonce0 @(EraCrypto era))