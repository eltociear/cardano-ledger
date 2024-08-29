{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Specs necessary to generate constrained (well formed) values in the Cardano Ledger.
module Test.Cardano.Ledger.Constrained.Conway.StateSpecs where

import Cardano.Ledger.Alonzo.TxOut (AlonzoTxOut (..))
import Cardano.Ledger.Api
import Cardano.Ledger.Babbage.TxOut (BabbageTxOut (..))
import Cardano.Ledger.BaseTypes hiding (inject)
import Cardano.Ledger.CertState
import Cardano.Ledger.Coin (Coin (..), DeltaCoin (..))
import Cardano.Ledger.Conway.Rules
import Cardano.Ledger.Core (Value)
import Cardano.Ledger.Credential (Credential, StakeReference (..))
import Cardano.Ledger.EpochBoundary (SnapShot (..), SnapShots (..), Stake (..), calculatePoolDistr)
import Cardano.Ledger.Keys (KeyHash, KeyRole (..))
import Cardano.Ledger.Mary (MaryValue)
import Cardano.Ledger.PoolDistr (PoolDistr (..))
import Cardano.Ledger.PoolParams (PoolParams (..))
import Cardano.Ledger.SafeHash ()
import Cardano.Ledger.Shelley.LedgerState (
  AccountState (..),
  EpochState (..),
  IncrementalStake (..),
  LedgerState (..),
  NewEpochState (..),
  StashedAVVMAddresses,
  UTxOState (..),
  updateStakeDistribution,
 )
import Cardano.Ledger.Shelley.TxOut (ShelleyTxOut (..))
import Cardano.Ledger.TxIn (TxId (..))
import Cardano.Ledger.UMap (CompactForm (..))
import qualified Cardano.Ledger.UMap as UMap
import Cardano.Ledger.UTxO (UTxO (..))
import Constrained hiding (Value)
import Constrained.Base (Pred (..), Sized (..), fromList_, hasSize, rangeSize)
import Data.Default.Class (Default (def))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Proxy (Proxy (..))
import qualified Data.Set as Set
import Data.VMap (VB, VMap, VP)
import qualified Data.VMap as VMap
import Data.Word (Word64)
import System.IO.Unsafe (unsafePerformIO)
import Test.Cardano.Ledger.Constrained.Conway ()
import Test.Cardano.Ledger.Constrained.Conway.Gov (govProposalsSpec)
import Test.Cardano.Ledger.Constrained.Conway.Instances
import Test.Cardano.Ledger.Constrained.Conway.PParams (pparamsSpec)
import Test.Cardano.Ledger.Generic.PrettyCore (
  PrettyA (prettyA),
  pcIRewards,
  pcSnapShotL,
  ppRecord,
 )
import Test.Hspec
import Test.QuickCheck (Gen, Property, arbitrary, generate, property)

-- ===========================================================

-- | classes with operations to support Era parametric Specs.
--   They contains methods that navigate the differences in types parameterized
--   by 'era' that embed type families that change from one Era to another.
--   For example (PParams era) in the 'EraPP' class, and
--   TxOut, GovState, and StashedAVVMAddresses in the 'Cardano' class
class
  ( HasSpec fn (TxOut era)
  , IsNormalType (TxOut era)
  , HasSpec fn (GovState era)
  , HasSpec fn (StashedAVVMAddresses era)
  , EraTxOut era
  , IsConwayUniv fn
  , EraPP era
  ) =>
  CardanoState era fn
  where
  irewardSpec :: Term fn AccountState -> Specification fn (InstantaneousRewards (EraCrypto era))
  hasPtrs :: proxy era -> Term fn Bool
  correctTxOut ::
    Term fn (Map (Credential 'Staking (EraCrypto era)) (KeyHash 'StakePool (EraCrypto era))) ->
    Term fn (TxOut era) ->
    Pred fn
  govStateSpec :: PParams era -> Specification fn (GovState era)
  newEpochStateSpec :: PParams era -> Specification fn (NewEpochState era)

instance IsConwayUniv fn => CardanoState Shelley fn where
  irewardSpec = instantaneousRewardsSpec
  hasPtrs _proxy = lit True
  correctTxOut = betterTxOutShelley
  govStateSpec = shelleyGovStateSpec
  newEpochStateSpec = newEpochStateSpecUTxO

instance IsConwayUniv fn => CardanoState Allegra fn where
  irewardSpec = instantaneousRewardsSpec
  hasPtrs _proxy = lit True
  correctTxOut = betterTxOutShelley
  govStateSpec = shelleyGovStateSpec
  newEpochStateSpec = newEpochStateSpecUnit

instance IsConwayUniv fn => CardanoState Mary fn where
  irewardSpec = instantaneousRewardsSpec
  hasPtrs _proxy = lit True
  correctTxOut = betterTxOutMary
  govStateSpec = shelleyGovStateSpec
  newEpochStateSpec = newEpochStateSpecUnit

instance IsConwayUniv fn => CardanoState Alonzo fn where
  irewardSpec = instantaneousRewardsSpec
  hasPtrs _proxy = lit True
  correctTxOut = betterTxOutAlonzo
  govStateSpec = shelleyGovStateSpec
  newEpochStateSpec = newEpochStateSpecUnit

instance IsConwayUniv fn => CardanoState Babbage fn where
  irewardSpec = instantaneousRewardsSpec
  hasPtrs _proxy = lit True
  correctTxOut = betterTxOutBabbage
  govStateSpec = shelleyGovStateSpec
  newEpochStateSpec = newEpochStateSpecUnit

instance IsConwayUniv fn => CardanoState Conway fn where
  irewardSpec _ = constrained $ \ [var|irewards|] ->
    match irewards $ \ [var|reserves|] [var|treasury|] [var|deltaRes|] [var|deltaTreas|] ->
      [ reserves ==. lit Map.empty
      , treasury ==. lit Map.empty
      , deltaRes ==. lit (DeltaCoin 0)
      , deltaTreas ==. lit (DeltaCoin 0)
      ]

  -- ptrPred _proxy ptrmap _umap = assertExplain (pure "dom ptrMap is empty") $ dom_ ptrmap ==. mempty
  hasPtrs _proxy = lit False
  correctTxOut = betterTxOutBabbage
  govStateSpec pp = conwayGovStateSpec pp (testGovEnv pp)
  newEpochStateSpec = newEpochStateSpecUnit

-- | Want (Rng v3) == (Dom v0), except the Rng is List and the Dom is a Set.
domEqualRng ::
  ( IsConwayUniv fn
  , Ord ptr
  , Ord cred
  , HasSpec fn cred
  , HasSpec fn ptr
  , HasSpec fn ume
  ) =>
  Term fn (Map ptr cred) ->
  Term fn (Map cred ume) ->
  Pred fn
domEqualRng [var|mapXCred|] [var|mapCredY|] =
  Block
    [ assert $ sizeOf_ mapCredY <=. sizeOf_ mapXCred
    , assert $ sizeOf_ mapXCred >=. lit 0
    , assert $ sizeOf_ mapCredY >=. lit 0
    , assertExplain (pure "Domain mapCredX == Range  mapXCred") $
        [dependsOn mapCredY mapXCred, assert $ dom_ mapCredY ==. fromList_ (rng_ mapXCred)]
    ]

go0 :: IO ()
go0 = do
  (x, y) <-
    generate $
      genFromSpec @ConwayFn @(Map Int Int, Map Int Int)
        (constrained' $ \x y -> domEqualRng x y)
  putStrLn ("x = " ++ show (Set.fromList (Map.elems x)))
  putStrLn ("y = " ++ show (Map.keysSet y))

-- ======================================================================================
-- TxOut and Value are two of the type families, whose instance changes from Era to Era.
-- TxOuts, we need SimpleRep for each possible TxOut (Shelley,Mary,Alonzo,Babbage)
-- We also need to define the method 'correctTxOut' for every 'Cardanoed' instance
-- These instances are tricky, since there is a unique combination of Value and TxOut
-- ======================================================================================

betterTxOutShelley ::
  (EraTxOut era, Value era ~ Coin, IsConwayUniv fn) =>
  Term fn (Map (Credential 'Staking (EraCrypto era)) (KeyHash 'StakePool (EraCrypto era))) ->
  Term fn (ShelleyTxOut era) ->
  Pred fn
betterTxOutShelley delegs txOut =
  match txOut $ \ [var|addr|] [var|val|] ->
    [ match val $ \ [var|c|] -> [0 <. c, c <=. fromIntegral (maxBound :: Word64)]
    , (caseOn addr)
        ( branch $ \ [var|n|] _ [var|r|] ->
            [ assert $ n ==. lit Testnet
            , satisfies r (delegatedStakeReference delegs)
            ]
        )
        ( branch $ \bootstrapAddr ->
            match bootstrapAddr $ \_ [var|nm|] _ ->
              (caseOn nm)
                (branch $ \_ -> False)
                (branch $ \_ -> True)
        )
    ]

betterTxOutMary ::
  (EraTxOut era, Value era ~ MaryValue (EraCrypto era), IsConwayUniv fn) =>
  Term fn (Map (Credential 'Staking (EraCrypto era)) (KeyHash 'StakePool (EraCrypto era))) ->
  Term fn (ShelleyTxOut era) ->
  Pred fn
betterTxOutMary delegs txOut =
  match txOut $ \ [var|addr|] [var|val|] ->
    [ match val $ \c -> [0 <. c, c <=. fromIntegral (maxBound :: Word64)]
    , (caseOn addr)
        ( branch $ \n _ r ->
            [ assert $ n ==. lit Testnet
            , satisfies r (delegatedStakeReference delegs)
            ]
        )
        ( branch $ \bootstrapAddr ->
            match bootstrapAddr $ \_ nm _ ->
              (caseOn nm)
                (branch $ \_ -> False)
                (branch $ \_ -> True)
        )
    ]

betterTxOutAlonzo ::
  (AlonzoEraTxOut era, Value era ~ MaryValue (EraCrypto era), IsConwayUniv fn) =>
  Term fn (Map (Credential 'Staking (EraCrypto era)) (KeyHash 'StakePool (EraCrypto era))) ->
  Term fn (AlonzoTxOut era) ->
  Pred fn
betterTxOutAlonzo delegs txOut =
  match txOut $ \ [var|addr|] [var|val|] _ ->
    [ match val $ \c -> [0 <. c, c <=. fromIntegral (maxBound :: Word64)]
    , (caseOn addr)
        ( branch $ \n _ r ->
            [ assert $ n ==. lit Testnet
            , satisfies r (delegatedStakeReference delegs)
            ]
        )
        ( branch $ \bootstrapAddr ->
            match bootstrapAddr $ \_ _nm _ -> False
            {-
            (caseOn nm)
              (branch $ \_ -> False)
              (branch $ \_ -> True) -}
        )
    ]

betterTxOutBabbage ::
  ( EraTxOut era
  , Value era ~ MaryValue (EraCrypto era)
  , IsNormalType (Script era)
  , HasSpec fn (Script era)
  , IsConwayUniv fn
  ) =>
  Term fn (Map (Credential 'Staking (EraCrypto era)) (KeyHash 'StakePool (EraCrypto era))) ->
  Term fn (BabbageTxOut era) ->
  Pred fn
betterTxOutBabbage delegs txOut =
  match txOut $ \ [var|addr|] [var|val|] _ _ ->
    [ match val $ \c -> [0 <. c, c <=. fromIntegral (maxBound :: Word64)]
    , (caseOn addr)
        ( branch $ \n _ r ->
            [ assert $ n ==. lit Testnet
            , satisfies r (delegatedStakeReference delegs)
            ]
        )
        ( branch $ \bootstrapAddr ->
            match bootstrapAddr $ \_ nm _ ->
              (caseOn nm)
                (branch $ \_ -> False)
                (branch $ \_ -> True)
        )
    ]

delegatedStakeReference ::
  (IsConwayUniv fn, Crypto c) =>
  Term fn (Map (Credential 'Staking c) (KeyHash 'StakePool c)) ->
  Specification fn (StakeReference c)
delegatedStakeReference delegs =
  constrained $ \ [var|ref|] ->
    caseOn
      ref
      (branch $ \ [var|base|] -> member_ base (dom_ delegs))
      (branch $ \_ptr -> False)
      (branch $ \_null -> False)

-- ====================================================================================
-- Some Specifications are constrained by types (say 'x') that do not appear in the type being
-- specified. We use the strategy of passing (Term fn x) as inputs to those specifcations.
-- For example, the AcountState must have sufficient capacity to support the InstantaneousRewards
-- So we pass a (Term fn AccountState) as input to 'instantaneousRewardsSpec'
-- In order to create tests, not involving the outer specifications (i.e. instantaneousRewardsSpec
-- in the example above), we make literal 'test' terms, we use by passing the test terms
--  as inputs to the tests and examples of those 'inner' specifications.
-- ====================================================================================

testAcctState :: Term fn AccountState
testAcctState = lit (AccountState (Coin 100) (Coin 100))

testGovEnv :: Era era => PParams era -> GovEnv era
testGovEnv pp =
  GovEnv
    (TxId def) -- SafeHash has a Default instance
    (EpochNo 99)
    pp
    SNothing
    (CertState def def def)

testEpochNo :: Term fn EpochNo
testEpochNo = lit (EpochNo 99)

testPools ::
  forall era c.
  (c ~ EraCrypto era, CardanoState era ConwayFn) =>
  Term ConwayFn (Map (KeyHash 'StakePool c) (PoolParams c))
testPools = unsafePerformIO $ generate $ do
  ps <- specToGen @(Map (KeyHash 'StakePool c) (PoolParams c)) (hasSize (rangeSize 8 8))
  pure (lit ps)

testDelegations ::
  forall c. Crypto c => Term ConwayFn (Map (Credential 'Staking c) (KeyHash 'StakePool c))
testDelegations = unsafePerformIO $ generate $ do
  ds <- specToGen @(Map (Credential 'Staking c) (KeyHash 'StakePool c)) (hasSize (rangeSize 8 8))
  pure (lit ds)

testPP :: EraPParams era => PParams era
testPP = def

testCertState :: forall era. CardanoState era ConwayFn => Term ConwayFn (CertState era)
testCertState = unsafePerformIO $ generate $ do
  cs <- specToGen @(CertState era) (certStateSpec testAcctState testEpochNo)
  pure (lit cs)

testLedgerState :: forall era. CardanoState era ConwayFn => LedgerState era
testLedgerState = unsafePerformIO $ generate $ do
  ls <- specToGen @(LedgerState era) (ledgerStateSpec testPP testAcctState testEpochNo)
  pure ls

-- ================================================================================
-- Specifications for types that appear in the CardanoState Ledger
-- the functions  goXX :: IO () (or IO Bool) visualize a test run they are crcuial
-- to eyeballing that the spes are working as expected. Eventually we will get
-- rid of them. But until the Specifications becoe stable, we will keep them.
-- ================================================================================

instantaneousRewardsSpec ::
  forall c fn.
  (IsConwayUniv fn, Crypto c) =>
  Term fn AccountState ->
  Specification fn (InstantaneousRewards c)
instantaneousRewardsSpec acct = constrained $ \ [var| irewards |] ->
  match acct $ \ [var| acctRes |] [var| acctTreas |] ->
    match irewards $ \ [var| reserves |] [var| treasury |] [var| deltaRes |] [var| deltaTreas |] ->
      [ assertExplain (pure "deltaTreausry and deltaReserves sum to 0") $ negate deltaRes ==. deltaTreas
      , forAll (rng_ reserves) (\ [var| x |] -> x /=. (lit (Coin 0)))
      , forAll (rng_ treasury) (\ [var| y |] -> y /=. (lit (Coin 0)))
      , --  , dependsOn acctRes deltaRes
        assert $ (toDelta_ (foldMap_ id (rng_ reserves))) - deltaRes <=. toDelta_ acctRes
      , assert $ (toDelta_ (foldMap_ id (rng_ treasury))) - deltaTreas <=. toDelta_ acctTreas
      ]

go1 :: IO ()
go1 = do
  acct <- generate (arbitrary :: Gen AccountState)
  let xx :: Specification ConwayFn (InstantaneousRewards StandardCrypto)
      xx = instantaneousRewardsSpec @(EraCrypto Shelley) @ConwayFn (lit acct)
  ir <- generateSpec xx
  putStrLn (show (pcIRewards ir))
  putStrLn ("conforms " ++ show (conformsToSpec ir xx) ++ "  " ++ show acct)

-- ========================================================================
-- The CertState specs
-- ========================================================================

instance IsConwayUniv fn => NumLike fn EpochNo

drepStateSpec :: (IsConwayUniv fn, Crypto c) => Term fn EpochNo -> Specification fn (DRepState c)
drepStateSpec epoch = constrained $ \ [var|drepstate|] ->
  match drepstate $ \ [var|expiry|] _anchor [var|drepDdeposit|] ->
    [ assertExplain (pure "epoch of expiration must follow the current epoch") $ epoch <=. expiry
    , assertExplain (pure "no deposit is 0") $ lit (Coin 0) <=. drepDdeposit
    ]

go2 :: IO Bool
go2 = ioTest @(DRepState StandardCrypto) (drepStateSpec testEpochNo)

vstateSpec :: (IsConwayUniv fn, Era era) => Term fn EpochNo -> Specification fn (VState era)
vstateSpec epoch = constrained $ \ [var|vstate|] ->
  match vstate $ \ [var|dreps|] [var|comstate|] [var|numdormant|] ->
    [ forAll (rng_ dreps) (\ [var|x|] -> x `satisfies` (drepStateSpec epoch))
    , satisfies (dom_ dreps) (hasSize (rangeSize 5 12))
    , assertExplain (pure "num dormant epochs should not be too large") $
        [epoch <=. numdormant, numdormant <=. epoch + (lit (EpochNo 10))]
    , dependsOn numdormant epoch -- Solve epoch first.
    , match comstate $ \ [var|commap|] -> sizeRng commap 1 4
    ]

go3 :: IO Bool
go3 = ioTest @(VState Shelley) (vstateSpec testEpochNo)

dstateSpec ::
  forall era fn.
  CardanoState era fn =>
  Term fn AccountState ->
  Term fn (Map (KeyHash 'StakePool (EraCrypto era)) (PoolParams (EraCrypto era))) ->
  Specification fn (DState era)
dstateSpec acct poolreg = constrained $ \ [var| ds |] ->
  match ds $ \ [var|umap|] [var|futureGenDelegs|] [var|genDelegs|] [var|irewards|] ->
    match umap $ \ [var|rdMap|] [var|ptrMap|] [var|sPoolMap|] _dRepMap ->
      [ assert $ (sizeOf_ sPoolMap) >=. lit 5
      , assertExplain (pure "The delegations delegate to actual pools") $
          forAll (rng_ sPoolMap) (\ [var|keyhash|] -> member_ keyhash (dom_ poolreg))
      , assertExplain (pure "dom sPoolMap is a subset of dom rdMap") $ dom_ sPoolMap `subset_` dom_ rdMap
      , -- reify here, forces us to solve for ptrMap, before sovling for rdMap
        whenTrue (hasPtrs (Proxy @era)) (reify ptrMap id (\ [var|pm|] -> domEqualRng pm rdMap))
      , whenTrue (not_ (hasPtrs (Proxy @era))) (assert $ ptrMap ==. lit Map.empty)
      , satisfies irewards (irewardSpec @era acct)
      , satisfies futureGenDelegs (hasSize (rangeSize 0 3))
      , match genDelegs $ \ [var|gd|] -> satisfies gd (hasSize (rangeSize 1 4)) -- Strip off the newtype constructor
      ]

go4 :: IO Bool
go4 = do
  cs <-
    generateSpec @(Map (KeyHash 'StakePool StandardCrypto) (PoolParams StandardCrypto))
      (hasSize (rangeSize 10 10))
  putStrLn ("STAKEPOOL MAP\n" ++ show (prettyA cs))
  t <- generateSpec @(DState Conway) (dstateSpec testAcctState (lit cs))
  putStrLn ("DSTATE\n" ++ show (prettyA t))
  pure (conformsToSpec @ConwayFn t (dstateSpec testAcctState (lit cs)))

pstateSpec ::
  (IsConwayUniv fn, Era era) =>
  Term fn EpochNo ->
  Specification fn (PState era)
pstateSpec currepoch = constrained $ \ [var|pState|] ->
  match pState $ \ [var|stakePoolParams|] [var|futureStakePoolParams|] [var|retiring|] [var|pooldeposits|] ->
    [ assertExplain (pure "dom of retiring is a subset of dom of stakePoolParams") $
        dom_ retiring `subset_` dom_ stakePoolParams
    , assertExplain (pure "retiring after current epoch") $
        forAll (rng_ retiring) (\ [var|epoch|] -> currepoch <=. epoch)
    , assertExplain (pure "dom of deposits is dom of stakePoolParams") $
        dom_ pooldeposits ==. dom_ stakePoolParams
    , assertExplain (pure "no deposit is 0") $
        not_ $
          lit (Coin 0) `elem_` rng_ pooldeposits
    , assertExplain (pure "dom of stakePoolParams is disjoint from futureStakePoolParams") $
        dom_ stakePoolParams `disjoint_` dom_ futureStakePoolParams
    , assert $ sizeOf_ (dom_ futureStakePoolParams) <=. 4
    , assert $ 3 <=. sizeOf_ (dom_ stakePoolParams)
    , assert $ sizeOf_ (dom_ stakePoolParams) <=. 8
    ]

go5 :: IO Bool
go5 = ioTest @(PState Shelley) (pstateSpec testEpochNo)

accountStateSpec :: IsConwayUniv fn => Specification fn AccountState
accountStateSpec =
  constrained
    ( \ [var|accountState|] ->
        match
          accountState
          (\ [var|reserves|] [var|treasury|] -> [lit (Coin 100) <=. treasury, lit (Coin 100) <=. reserves])
    )

certStateSpec ::
  forall era fn.
  CardanoState era fn =>
  Term fn AccountState ->
  Term fn EpochNo ->
  Specification fn (CertState era)
certStateSpec acct epoch = constrained $ \ [var|certState|] ->
  match certState $ \ [var|vState|] [var|pState|] [var|dState|] ->
    [ satisfies vState (vstateSpec epoch)
    , satisfies pState (pstateSpec epoch)
    , reify pState psStakePoolParams (\ [var|poolreg|] -> satisfies dState (dstateSpec acct poolreg))
    ]

go6 :: IO Bool
go6 = ioTest @(CertState Shelley) (certStateSpec testAcctState testEpochNo)

-- ==============================================================
-- Specs for UTxO and UTxOState
-- ==============================================================

utxoSpec ::
  forall era fn.
  CardanoState era fn =>
  Term fn (Map (Credential 'Staking (EraCrypto era)) (KeyHash 'StakePool (EraCrypto era))) ->
  Specification fn (UTxO era)
utxoSpec delegs = constrained $ \ [var|utxo|] ->
  match utxo $ \ [var|utxomap|] ->
    [ forAll (rng_ utxomap) (\ [var|output|] -> correctTxOut delegs output)
    , assert $ (sizeOf_ (rng_ utxomap)) ==. 8 -- Arbitrary for testing purposes.
    -- , GenHint 10 utxomap
    ]

go7 :: IO Bool
go7 = do
  cs <-
    generateSpec @(Map (Credential 'Staking StandardCrypto) (KeyHash 'StakePool StandardCrypto))
      (hasSize (rangeSize 30 30))
  putStrLn ("Stake Registration MAP\n" ++ show (prettyA cs))
  t <- generateSpec @(UTxO Mary) (utxoSpec @Mary (lit cs))
  putStrLn ("UTxO\n" ++ show (prettyA t))
  pure (conformsToSpec @ConwayFn t (utxoSpec @Mary (lit cs)))

utxoStateSpec ::
  forall era fn.
  CardanoState era fn =>
  PParams era ->
  Term fn (CertState era) ->
  Specification fn (UTxOState era)
utxoStateSpec pp certstate =
  constrained $ \ [var|utxoState|] ->
    match utxoState $ \ [var|utxo|] [var|deposits|] [var|fees|] [var|gov|] [var|distr|] [var|donation|] ->
      [ assert $ donation ==. lit (Coin 0)
      , reify
          certstate
          (sumObligation . obligationCertState)
          (\ [var|depositsum|] -> assert $ deposits ==. depositsum)
      , assert $ lit (Coin 0) <=. fees
      , reify certstate getDelegs (\ [var|delegs|] -> satisfies utxo (utxoSpec delegs))
      , satisfies gov (govStateSpec @era @fn pp)
      , reify utxo (updateStakeDistribution pp mempty mempty) (\ [var|i|] -> distr ==. i)
      ]

getDelegs ::
  forall era.
  CertState era ->
  Map (Credential 'Staking (EraCrypto era)) (KeyHash 'StakePool (EraCrypto era))
getDelegs cs = UMap.sPoolMap (dsUnified (certDState cs))

go8 :: IO Bool
go8 = do
  cs <- generateSpec @(CertState Shelley) (certStateSpec testAcctState testEpochNo)
  t <- generateSpec @(UTxOState Shelley) (utxoStateSpec @Shelley @ConwayFn def (lit cs))
  putStrLn ("UTXOSTATE\n" ++ show (prettyA t))
  putStrLn ("CERTSTATE\n" ++ show (prettyA cs))
  pure (conformsToSpec t (utxoStateSpec @Shelley @ConwayFn def (lit cs)))

-- ====================================================================
-- Specs for LedgerState
-- ====================================================================

shelleyGovStateSpec ::
  forall era fn. CardanoState era fn => PParams era -> Specification fn (ShelleyGovState era)
shelleyGovStateSpec pp =
  constrained $ \ [var|shellGovState|] ->
    match shellGovState $ \ [var|curpro|] [var|futpro|] [var|curpp|] _prevpp _futpp ->
      match curpro $ \ [var|cm|] ->
        [ satisfies cm (hasSize (rangeSize 1 2))
        , match futpro $ \ [var|fm|] -> satisfies fm (hasSize (rangeSize 1 2))
        , assert $ curpp ==. lit pp
        -- FIXME -- match _futpp (\ fpp -> canFollow (protocolVersion_ fpp) (protocolVersion_ curpp))
        ]

go9 :: IO Bool
go9 = ioTest @(ShelleyGovState Mary) (shelleyGovStateSpec @Mary @ConwayFn def)

govEnvSpec ::
  IsConwayUniv fn =>
  PParams Conway ->
  Specification fn (GovEnv Conway)
govEnvSpec pp = constrained $ \ [var|govEnv|] ->
  match govEnv $ \_ _ [var|cppx|] _ _ -> [assert $ lit pp ==. cppx]

conwayGovStateSpec ::
  forall fn.
  CardanoState Conway fn =>
  PParams Conway ->
  GovEnv Conway ->
  Specification fn (ConwayGovState Conway)
conwayGovStateSpec pp govenv =
  constrained $ \ [var|conwaygovstate|] ->
    match conwaygovstate $ \ [var|proposals|] _mcommittee _consti [var|curpp|] _prevpp _futurepp _derepPulstate ->
      [ assert $ curpp ==. lit pp
      , satisfies proposals (govProposalsSpec govenv)
      ]

-- =========================================================================

ledgerStateSpec ::
  forall era fn.
  CardanoState era fn =>
  PParams era ->
  Term fn AccountState ->
  Term fn EpochNo ->
  Specification fn (LedgerState era)
ledgerStateSpec pp acct epoch =
  constrained $ \ [var|ledgerState|] ->
    match ledgerState $ \ [var|utxoS|] [var|csg|] ->
      [ satisfies csg (certStateSpec @era @fn acct epoch)
      , reify csg id (\ [var|certstate|] -> satisfies utxoS (utxoStateSpec @era @fn pp certstate))
      ]

go11 :: IO ()
go11 = do
  ls <- generateSpec (ledgerStateSpec @Shelley @ConwayFn def testAcctState testEpochNo)
  let d = sumObligation $ obligationCertState $ lsCertState ls
  putStrLn (show (prettyA ls))
  putStrLn ("Total certstate deposits " ++ show d)

-- ===========================================================

-- TODO make this more realistic
snapShotSpec :: (Crypto c, IsConwayUniv fn) => Specification fn (SnapShot c)
snapShotSpec =
  constrained $ \ [var|snap|] ->
    match snap $ \ [var|stake|] [var|delegs|] [var|poolparams|] ->
      match stake $ \ [var|stakemap|] ->
        [ assert $ stakemap ==. lit VMap.empty
        , assert $ delegs ==. lit VMap.empty
        , assert $ poolparams ==. lit VMap.empty
        ]

go12 :: IO ()
go12 = do
  -- No PrettyA instance so we write it out
  sn <- generateSpec (snapShotSpec @(EraCrypto Shelley) @ConwayFn)
  putStrLn (show (ppRecord "SnapShot" (pcSnapShotL "" sn)))

snapShotsSpec ::
  (Crypto c, IsConwayUniv fn) => Term fn (SnapShot c) -> Specification fn (SnapShots c)
snapShotsSpec marksnap =
  constrained $ \ [var|snap|] ->
    match snap $ \ [var|mark|] [var|pooldistr|] [var|set|] [var|go|] _fee ->
      Block
        [ assert $ mark ==. marksnap
        , satisfies set snapShotSpec
        , satisfies go snapShotSpec
        , reify marksnap calculatePoolDistr $ \ [var|pd|] -> pooldistr ==. pd
        ]

go13 :: IO Bool
go13 =
  ioTest @(SnapShots StandardCrypto)
    (snapShotsSpec (lit (getMarkSnapShot (testLedgerState @Babbage))))

-- | The Mark SnapShot (at the epochboundary) is a pure function of the LedgerState
getMarkSnapShot :: forall era. LedgerState era -> SnapShot (EraCrypto era)
getMarkSnapShot ls = SnapShot @(EraCrypto era) (Stake markStake) markDelegations markPoolParams
  where
    markStake :: VMap VB VP (Credential 'Staking (EraCrypto era)) (CompactForm Coin)
    markStake = VMap.fromMap (credMap (utxosStakeDistr (lsUTxOState ls)))
    markDelegations ::
      VMap VB VB (Credential 'Staking (EraCrypto era)) (KeyHash 'StakePool (EraCrypto era))
    markDelegations = VMap.fromMap (UMap.sPoolMap (dsUnified (certDState (lsCertState ls))))
    markPoolParams :: VMap VB VB (KeyHash 'StakePool (EraCrypto era)) (PoolParams (EraCrypto era))
    markPoolParams = VMap.fromMap (psStakePoolParams (certPState (lsCertState ls)))

-- ====================================================================
-- Specs for EpochState and NewEpochState
-- ====================================================================

epochStateSpec ::
  forall era fn.
  CardanoState era fn =>
  PParams era ->
  Term fn EpochNo ->
  Specification fn (EpochState era)
epochStateSpec pp epoch =
  constrained $ \ [var|epochState|] ->
    match epochState $ \ [var|acctst|] [var|eLedgerState|] [var|snaps|] [var|nonmyopic|] ->
      Block
        [ dependsOn acctst epoch
        , satisfies eLedgerState (ledgerStateSpec pp acctst epoch)
        , reify eLedgerState getMarkSnapShot $ \ [var|marksnap|] -> satisfies snaps (snapShotsSpec marksnap)
        , match acctst $ \ [var|acctTreasury|] [var|acctReserves|] -> [acctTreasury >=. lit (Coin 100), acctReserves >=. lit (Coin 100)]
        , match nonmyopic $ \ [var|x|] [var|c|] -> [assert $ (sizeOf_ x) ==. 0, assert $ c ==. lit (Coin 0)]
        ]

go14 :: IO Bool
go14 = ioTest @(EpochState Babbage) (epochStateSpec def testEpochNo)

getPoolDistr :: forall era. EpochState era -> PoolDistr (EraCrypto era)
getPoolDistr es = ssStakeMarkPoolDistr (esSnapshots es)

-- | Used for Eras where StashedAVVMAddresses era ~ () (Allegra,Mary,Alonzo,Babbage,Conway)
-- The 'newEpochStateSpec' method (of (CardanoState era fn) class) in the instances for (Allegra,Mary,Alonzo,Babbage,Conway)
newEpochStateSpecUnit ::
  forall era fn.
  (CardanoState era fn, StashedAVVMAddresses era ~ ()) =>
  PParams era ->
  Specification fn (NewEpochState era)
newEpochStateSpecUnit pp =
  constrained
    ( \ [var|newEpochStateUnit|] ->
        match
          (newEpochStateUnit :: Term fn (NewEpochState era))
          ( \ [var|eno|] [var|blocksPrev|] [var|blocksCurr|] [var|epochstate|] _mpulser [var|pooldistr|] [var|stashAvvm|] ->
              Block
                [ reify eno id (\ [var|epoch|] -> satisfies epochstate (epochStateSpec @era @fn pp epoch))
                , satisfies stashAvvm (constrained (\ [var|x|] -> lit () ==. x))
                , reify epochstate getPoolDistr $ \ [var|pd|] -> pooldistr ==. pd
                , match blocksPrev (genHint 3)
                , match blocksCurr (genHint 3)
                ]
          )
    )

-- | Used for Eras where StashedAVVMAddresses era ~ UTxO era (Shelley)
-- The 'newEpochStateSpec' method (of (CardanoState era fn) class) in the Shelley instance
newEpochStateSpecUTxO ::
  forall era fn.
  (CardanoState era fn, StashedAVVMAddresses era ~ UTxO era) =>
  PParams era ->
  Specification fn (NewEpochState era)
newEpochStateSpecUTxO pp =
  constrained
    ( \ [var|newEpochStateUTxO|] ->
        match
          (newEpochStateUTxO :: Term fn (NewEpochState era))
          ( \ [var|eno|] [var|blocksPrev|] [var|blocksCurr|] [var|epochstate|] _mpulser [var|pooldistr|] [var|stashAvvm|] ->
              Block
                [ reify eno id (\ [var|epoch|] -> satisfies epochstate (epochStateSpec @era @fn pp epoch))
                , satisfies stashAvvm (constrained (\ [var|u|] -> u ==. lit (UTxO @era Map.empty)))
                , reify epochstate getPoolDistr $ \ [var|pd|] -> pooldistr ==. pd
                , match blocksPrev (genHint 3)
                , match blocksCurr (genHint 3)
                ]
          )
    )

go15 :: IO Bool
go15 = ioTest @(NewEpochState Shelley) (newEpochStateSpec def)

go16 :: IO Bool
go16 = ioTest @(NewEpochState Alonzo) (newEpochStateSpec def)

-- ==============================================================
-- The WellFormed class and instances
-- ==============================================================

class (HasSpec ConwayFn t, CardanoState era ConwayFn) => WellFormed t era where
  wffp :: PParams era -> Gen t
  wff :: Gen t
  wff = do
    pp <- specToGen @(PParams era) pparamsSpec
    wffp pp

instance CardanoState era ConwayFn => WellFormed (PParams era) era where
  wff = specToGen @(PParams era) pparamsSpec
  wffp p = pure p

instance CardanoState era ConwayFn => WellFormed AccountState era where
  wff = specToGen @AccountState accountStateSpec
  wffp _ = specToGen @AccountState accountStateSpec

instance CardanoState era ConwayFn => WellFormed (PState era) era where
  wff = specToGen @(PState era) (pstateSpec testEpochNo)
  wffp _ = specToGen @(PState era) (pstateSpec testEpochNo)

instance CardanoState era ConwayFn => WellFormed (DState era) era where
  wff = specToGen @(DState era) (dstateSpec testAcctState (testPools @era @(EraCrypto era)))
  wffp _ = specToGen @(DState era) (dstateSpec testAcctState (testPools @era @(EraCrypto era)))

instance CardanoState era ConwayFn => WellFormed (VState era) era where
  wff = specToGen @(VState era) (vstateSpec testEpochNo)
  wffp _ = specToGen @(VState era) (vstateSpec testEpochNo)

instance CardanoState era ConwayFn => WellFormed (CertState era) era where
  wff = specToGen @(CertState era) (certStateSpec testAcctState testEpochNo)
  wffp _ = specToGen @(CertState era) (certStateSpec testAcctState testEpochNo)

instance CardanoState era ConwayFn => WellFormed (UTxOState era) era where
  wffp pp = specToGen @(UTxOState era) (utxoStateSpec pp testCertState)

instance CardanoState era ConwayFn => WellFormed (LedgerState era) era where
  wffp pp = specToGen @(LedgerState era) (ledgerStateSpec pp testAcctState testEpochNo)

-- TODO, this fails sometimes, has something to do with the sizes
-- listOfUntilLenT fails finding lists with valid length where goalLen = 8
-- We need to avoid suchThatT.

instance CardanoState era ConwayFn => WellFormed (EpochState era) era where
  wffp pp = specToGen @(EpochState era) (epochStateSpec pp testEpochNo)

instance CardanoState era ConwayFn => WellFormed (NewEpochState era) era where
  wffp pp = specToGen @(NewEpochState era) (newEpochStateSpec pp)

instance WellFormed (GovEnv Conway) Conway where
  wffp pp = specToGen @(GovEnv Conway) (govEnvSpec pp)

instance WellFormed (ConwayGovState Conway) Conway where
  wffp pp = do
    env <- specToGen @(GovEnv Conway) (govEnvSpec pp)
    specToGen @(ConwayGovState Conway) (conwayGovStateSpec pp env)

instance CardanoState era ConwayFn => WellFormed (ShelleyGovState era) era where
  wffp pp = specToGen @(ShelleyGovState era) (shelleyGovStateSpec pp)

instance (CardanoState era ConwayFn, c ~ EraCrypto era) => WellFormed (SnapShot c) era where
  wffp _ = specToGen @(SnapShot (EraCrypto era)) snapShotSpec
  wff = specToGen @(SnapShot (EraCrypto era)) snapShotSpec

instance (CardanoState era ConwayFn, c ~ EraCrypto era) => WellFormed (SnapShots c) era where
  wffp pp = do
    ls <- specToGen @(LedgerState era) (ledgerStateSpec pp testAcctState testEpochNo)
    specToGen @(SnapShots (EraCrypto era)) (snapShotsSpec (lit (getMarkSnapShot ls)))

instance (CardanoState era ConwayFn, c ~ EraCrypto era) => WellFormed (InstantaneousRewards c) era where
  wffp _ = specToGen @(InstantaneousRewards (EraCrypto era)) (instantaneousRewardsSpec testAcctState)
  wff = specToGen @(InstantaneousRewards (EraCrypto era)) (instantaneousRewardsSpec testAcctState)

-- =============================================================
-- helper functions for examples and tests

testwff :: forall p era. (WellFormed (p era) era, PrettyA (p era)) => IO ()
testwff = do
  x <- generate (wff @(p era) @era)
  putStrLn (show (prettyA x))

generateSpec :: forall a. HasSpec ConwayFn a => Specification ConwayFn a -> IO a
generateSpec specx = generate (genFromSpec @ConwayFn specx)

specToGen :: forall t. HasSpec ConwayFn t => Specification ConwayFn t -> Gen t
specToGen = genFromSpec

genSpec :: HasSpec ConwayFn a => Specification ConwayFn a -> IO a
genSpec = generateSpec

ioTest :: forall t. (HasSpec ConwayFn t, PrettyA t) => Specification ConwayFn t -> IO Bool
ioTest specx = do
  t <- generateSpec @t specx
  putStrLn (show (prettyA t))
  pure (conformsToSpec t specx)

sizeRng :: (HasSpec fn t, Sized t) => Term fn t -> Integer -> Integer -> Pred fn
sizeRng t lo hi = satisfies t (hasSize (rangeSize lo hi))

utxosDeposits_ ::
  ( EraTxOut era
  , IsNormalType (TxOut era)
  , HasSpec fn (TxOut era)
  , HasSpec fn (GovState era)
  , IsConwayUniv fn
  ) =>
  Term fn (UTxOState era) ->
  Term fn Coin
utxosDeposits_ = sel @1

-- ===================================================================
-- HSpec tests
-- ===================================================================

soundSpec :: forall t. HasSpec ConwayFn t => Specification ConwayFn t -> Gen Property
soundSpec specx = do
  x <- specToGen @t specx
  pure $ property $ (conformsToSpec x specx)

spec :: Spec
spec = do
  describe "WellFormed types from the Cardano Ledger" $ do
    it "InstantaneousRewards" $
      property $
        soundSpec @(InstantaneousRewards StandardCrypto) (instantaneousRewardsSpec testAcctState)
    it "PState" $ property $ soundSpec @(PState Shelley) (pstateSpec testEpochNo)
    it "DState" $ property $ soundSpec @(DState Shelley) (dstateSpec testAcctState (testPools @Shelley))
    it "VState" $ property $ soundSpec @(VState Shelley) (vstateSpec testEpochNo)
    it "CertState" $ property $ soundSpec @(CertState Shelley) (certStateSpec testAcctState testEpochNo)
    it "UTxO" $ property $ soundSpec @(UTxO Mary) (utxoSpec testDelegations)
    it "UTxOState" $ property $ soundSpec @(UTxOState Shelley) (utxoStateSpec testPP testCertState)
    it "LedgerState" $
      property $
        soundSpec @(LedgerState Babbage) (ledgerStateSpec testPP testAcctState testEpochNo)
    it "EpochState" $ property $ soundSpec @(EpochState Mary) (epochStateSpec testPP testEpochNo)
    it "NewEpochState" $ property $ soundSpec @(NewEpochState Conway) (newEpochStateSpec testPP)
    it "SnapShots" $
      property $
        soundSpec @(SnapShots StandardCrypto)
          (snapShotsSpec (lit (getMarkSnapShot (testLedgerState @Babbage))))

-- ========================================
-- TODO FIXME The dependency on this needs to be debugged

canFollow :: IsConwayUniv fn => Term fn ProtVer -> Term fn ProtVer -> Pred fn
canFollow pv pv' =
  match pv $ \majV minV ->
    match pv' $ \majV' minV' ->
      [ assert $ majV <=. majV'
      , ifElse
          (lit maxBound ==. majV)
          (majV ==. majV')
          (succV_ majV >=. majV')
      , ifElse
          (majV ==. majV')
          (minV' ==. minV + 1)
          (minV' ==. 0)
          -- , majV `dependsOn` majV'
      ]

testfollow :: Specification ConwayFn (ProtVer, ProtVer)
testfollow =
  constrained
    ( \x ->
        match x (\p1 p2 -> canFollow p1 p2)
    )

go30 :: IO (ProtVer, ProtVer)
go30 = generateSpec @(ProtVer, ProtVer) testfollow

rngSpec :: Specification ConwayFn (Map Int Int)
rngSpec = constrained $ \m -> 3 <=. sizeOf_ (fromList_ (rng_ m))

testRngSet :: IO ()
testRngSet = hspec $ do
  describe "WellFormed types from the Cardano Ledger" $ do
    it "Rng of Maps" $ property $ soundSpec @(Map Int Int) rngSpec
