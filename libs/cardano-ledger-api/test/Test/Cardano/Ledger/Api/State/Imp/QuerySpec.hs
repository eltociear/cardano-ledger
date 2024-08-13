{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Test.Cardano.Ledger.Api.State.Imp.QuerySpec where

import Cardano.Ledger.Api.State.Query (
  CommitteeMemberState (..),
  CommitteeMembersState (..),
  HotCredAuthStatus (..),
  MemberStatus (..),
  NextEpochChange (..),
  queryCommitteeMembersState,
  queryDRepState,
 )
import Cardano.Ledger.BaseTypes
import Cardano.Ledger.Coin
import Cardano.Ledger.Conway.Governance (
  Committee (..),
  ConwayEraGov (..),
  GovAction (..),
 )
import Cardano.Ledger.Conway.PParams (ppDRepActivityL)
import Cardano.Ledger.Core
import Cardano.Ledger.Credential (Credential (KeyHashObj))
import Cardano.Ledger.DRep
import Cardano.Ledger.Keys (KeyRole (..))
import Cardano.Ledger.Shelley.LedgerState
import Data.Default (def)
import Data.Foldable (Foldable (..))
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lens.Micro
import Lens.Micro.Mtl
import Test.Cardano.Ledger.Conway.ImpTest
import Test.Cardano.Ledger.Core.Rational ((%!))
import Test.Cardano.Ledger.Imp.Common

spec ::
  forall era.
  ConwayEraImp era =>
  SpecWith (ImpTestState era)
spec = do
  describe "DRep" $ do
    describe "Expiries are reported correctly" $ do
      let drepStateFromQuery ::
            (HasCallStack, Monad m) =>
            Credential 'DRepRole (EraCrypto era) ->
            NewEpochState era ->
            m (DRepState (EraCrypto era))
          drepStateFromQuery drep nes =
            case Map.lookup drep (queryDRepState nes mempty) of
              Nothing -> error $ "Expected for DRep " ++ show drep ++ " to be present in the query result"
              Just state -> pure state
      it "simple expiry" $ do
        curEpochNo <- getsNES nesELL
        let drepActivity = 3
        modifyPParams $ ppDRepActivityL .~ EpochInterval drepActivity
        (drep, _, _) <- setupSingleDRep 1_000_000
        nes <- getsNES id
        drepState <- drepStateFromQuery drep nes
        drepState ^. drepExpiryL `shouldBe` addEpochInterval curEpochNo (EpochInterval drepActivity)
        let n = 4
        passNEpochsChecking n $
          isDRepExpired drep `shouldReturn` False
        expectDRepExpiry drep $ addEpochInterval curEpochNo $ EpochInterval drepActivity
        expectActualDRepExpiry drep $
          addEpochInterval curEpochNo $
            EpochInterval (drepActivity + fromIntegral n)

      it "dRep registered when there are dormant epochs" $ do
        let drepActivity = 3
        modifyPParams $ ppDRepActivityL .~ EpochInterval drepActivity
        let n = 2
        passNEpochs n
        -- 2 dormant epochs
        expectNumDormantEpochs $ EpochNo (fromIntegral n)
        -- register drep
        (drep, _, _) <- setupSingleDRep 1_000_000

        -- submit ga
        void $ submitParameterChange SNothing $ def & ppuMinFeeAL .~ SJust (Coin 3000)

        epochNo <- getsNES nesELL
        let expectedExpiry =
              binOpEpochNo
                (+)
                (addEpochInterval epochNo (EpochInterval drepActivity))
                (EpochNo (fromIntegral n))
        expectDRepExpiry drep expectedExpiry

        nes <- getsNES id
        drepState <- drepStateFromQuery drep nes
        drepState ^. drepExpiryL `shouldBe` expectedExpiry

      it "proposals are made and numDormantEpochs are added" $ do
        curEpochNo <- getsNES nesELL
        let drepActivity = 3
        modifyPParams $ ppDRepActivityL .~ EpochInterval drepActivity
        let submitParamChangeProposal =
              submitParameterChange SNothing $ def & ppuMinFeeAL .~ SJust (Coin 3000)
        (drep, _, _) <- setupSingleDRep 1_000_000
        nes <- getsNES id
        drepState <- drepStateFromQuery drep nes
        drepState ^. drepExpiryL `shouldBe` addEpochInterval curEpochNo (EpochInterval drepActivity)
        let n = 2
            actualExpiry = addEpochInterval curEpochNo $ EpochInterval (drepActivity + fromIntegral n)
        passNEpochsChecking n $
          isDRepExpired drep `shouldReturn` False
        expectActualDRepExpiry drep actualExpiry
        expectDRepExpiry drep $ addEpochInterval curEpochNo $ EpochInterval drepActivity
        void submitParamChangeProposal
        expectDRepExpiry drep actualExpiry
        nes1 <- getsNES id
        drepState1 <- drepStateFromQuery drep nes1
        drepState1 ^. drepExpiryL `shouldBe` actualExpiry
        passNEpochsChecking (fromIntegral drepActivity) $
          isDRepExpired drep `shouldReturn` False
        passEpoch
        isDRepExpired drep `shouldReturn` True
      it "update certificates are submitted and proposals are made" $ do
        curEpochNo <- getsNES nesELL
        let drepActivity = 3
        modifyPParams $ ppDRepActivityL .~ EpochInterval drepActivity
        let submitParamChangeProposal =
              submitParameterChange SNothing $ def & ppuMinFeeAL .~ SJust (Coin 3000)
        (drep, _, _) <- setupSingleDRep 1_000_000
        nes <- getsNES id
        drepState <- drepStateFromQuery drep nes
        drepState ^. drepExpiryL `shouldBe` addEpochInterval curEpochNo (EpochInterval drepActivity)
        let n = 3
        passNEpochsChecking n $
          isDRepExpired drep `shouldReturn` False
        expectNumDormantEpochs $ EpochNo (fromIntegral n)
        expectDRepExpiry drep $ addEpochInterval curEpochNo $ EpochInterval drepActivity
        expectActualDRepExpiry drep $
          addEpochInterval curEpochNo $
            EpochInterval (drepActivity + fromIntegral n)
        updateDRep drep
        expectDRepExpiry drep $ addEpochInterval curEpochNo $ EpochInterval drepActivity
        expectActualDRepExpiry drep $
          addEpochInterval curEpochNo $
            EpochInterval (drepActivity + fromIntegral n)
        expectNumDormantEpochs $ EpochNo (fromIntegral n)
        nes1 <- getsNES id
        drepState1 <- drepStateFromQuery drep nes1
        drepState1
          ^. drepExpiryL
            `shouldBe` addEpochInterval
              curEpochNo
              (EpochInterval (drepActivity + fromIntegral n))
        expectDRepExpiry drep $ addEpochInterval curEpochNo $ EpochInterval drepActivity
        passEpoch
        expectNumDormantEpochs $ EpochNo (fromIntegral n + 1)
        void submitParamChangeProposal
        expectNumDormantEpochs $ EpochNo 0
        nes2 <- getsNES id
        drepState2 <- drepStateFromQuery drep nes2
        let drepExpiry2 = addEpochInterval curEpochNo $ EpochInterval (drepActivity + fromIntegral n + 1)
        drepState2 ^. drepExpiryL `shouldBe` drepExpiry2
        expectActualDRepExpiry drep drepExpiry2
        passNEpochsChecking (fromIntegral drepActivity) $ do
          isDRepExpired drep `shouldReturn` False
        passEpoch
        isDRepExpired drep `shouldReturn` True
  describe "Committee members hot key pre-authorization" $ do
    it "authorized members not elected get removed in the next epoch" $ do
      whenPostBootstrap $ do
        c1 <- KeyHashObj <$> freshKeyHash
        submitGovAction_ $
          UpdateCommittee SNothing mempty (Map.singleton c1 (EpochNo 4321)) (1 %! 1)
        hk1 <- registerCommitteeHotKey c1
        expectQueryResult (Set.singleton c1) mempty mempty $
          [(c1, CommitteeMemberState (MemberAuthorized hk1) Unrecognized Nothing ToBeRemoved)]
        passEpoch
        expectQueryResult (Set.singleton c1) mempty mempty Map.empty

    it "members should remain authorized if authorized during the epoch after their election" $
      whenPostBootstrap $ do
        (drep, _, _) <- setupSingleDRep 1_000_000

        c1 <- KeyHashObj <$> freshKeyHash
        _ <- electCommittee SNothing drep Set.empty [(c1, EpochNo 12)]
        passEpoch
        hk1 <- registerCommitteeHotKey c1
        expectQueryResult (Set.singleton c1) mempty mempty $
          [(c1, CommitteeMemberState (MemberAuthorized hk1) Unrecognized Nothing ToBeEnacted)]
        passEpoch
        expectQueryResult (Set.singleton c1) mempty mempty $
          [(c1, CommitteeMemberState (MemberAuthorized hk1) Active (Just 12) NoChangeExpected)]

  it "Committee queries" $ whenPostBootstrap $ do
    (drep, _, _) <- setupSingleDRep 1_000_000
    c1 <- KeyHashObj <$> freshKeyHash
    c2 <- KeyHashObj <$> freshKeyHash
    c3 <- KeyHashObj <$> freshKeyHash
    c4 <- KeyHashObj <$> freshKeyHash
    c5 <- KeyHashObj <$> freshKeyHash
    c6 <- KeyHashObj <$> freshKeyHash
    c7 <- KeyHashObj <$> freshKeyHash
    c8 <- KeyHashObj <$> freshKeyHash
    let newMembers =
          [ (c1, EpochNo 12)
          , (c2, EpochNo 2)
          , (c3, EpochNo 7)
          , (c4, EpochNo 5)
          ]
    initialMembers <- getCommitteeMembers

    ga1 <-
      electCommittee
        SNothing
        drep
        initialMembers
        newMembers

    expectMembers initialMembers
    passNEpochs 2 -- epoch 2
    expectMembers $ Map.keysSet newMembers
    -- members for which the expiration epoch is the current epoch are `ToBeExpired`
    expectNoFilterQueryResult
      [ (c1, CommitteeMemberState MemberNotAuthorized Active (Just 12) NoChangeExpected)
      , (c2, CommitteeMemberState MemberNotAuthorized Active (Just 2) ToBeExpired)
      , (c3, CommitteeMemberState MemberNotAuthorized Active (Just 7) NoChangeExpected)
      , (c4, CommitteeMemberState MemberNotAuthorized Active (Just 5) NoChangeExpected)
      ]
    -- hot cred status of members with registered hot keys becomes `MemberAuthorized`
    hk1 <- registerCommitteeHotKey c1
    hk2 <- registerCommitteeHotKey c2
    expectNoFilterQueryResult
      [ (c1, CommitteeMemberState (MemberAuthorized hk1) Active (Just 12) NoChangeExpected)
      , (c2, CommitteeMemberState (MemberAuthorized hk2) Active (Just 2) ToBeExpired)
      , (c3, CommitteeMemberState MemberNotAuthorized Active (Just 7) NoChangeExpected)
      , (c4, CommitteeMemberState MemberNotAuthorized Active (Just 5) NoChangeExpected)
      ]
    expectQueryResult
      [c2, c3, c5]
      mempty
      [Active, Unrecognized]
      [ (c3, CommitteeMemberState MemberNotAuthorized Active (Just 7) NoChangeExpected)
      , (c2, CommitteeMemberState (MemberAuthorized hk2) Active (Just 2) ToBeExpired)
      ]

    c3Anchor <- arbitrary
    _ <- resignCommitteeColdKey c3 (SJust c3Anchor)
    hk5 <- registerCommitteeHotKey c5
    passTick
    -- hot cred status of resigned member becomes `Resigned`
    -- registering a hot key for a credential that's not part of the committee will yield `Unrecognized` member status
    -- and expected change of `ToBeRemoved`
    expectNoFilterQueryResult
      [ (c1, CommitteeMemberState (MemberAuthorized hk1) Active (Just 12) NoChangeExpected)
      , (c2, CommitteeMemberState (MemberAuthorized hk2) Active (Just 2) ToBeExpired)
      , (c3, CommitteeMemberState (MemberResigned (Just c3Anchor)) Active (Just 7) NoChangeExpected)
      , (c4, CommitteeMemberState MemberNotAuthorized Active (Just 5) NoChangeExpected)
      , (c5, CommitteeMemberState (MemberAuthorized hk5) Unrecognized Nothing ToBeRemoved)
      ]
    expectQueryResult
      [c2, c3, c5]
      [hk5]
      [Unrecognized]
      ( Map.singleton
          c5
          (CommitteeMemberState (MemberAuthorized hk5) Unrecognized Nothing ToBeRemoved)
      )

    passEpoch -- epoch 3
    -- the `Unrecognized` member gets removed from the query result
    -- the member which in the previous epoch was expected `ToBeEpired`, has now MemberStatus `Expired` and `NoChangeExpected`
    expectNoFilterQueryResult
      [ (c1, CommitteeMemberState (MemberAuthorized hk1) Active (Just 12) NoChangeExpected)
      , (c2, CommitteeMemberState (MemberAuthorized hk2) Expired (Just 2) NoChangeExpected)
      , (c3, CommitteeMemberState (MemberResigned (Just c3Anchor)) Active (Just 7) NoChangeExpected)
      , (c4, CommitteeMemberState MemberNotAuthorized Active (Just 5) NoChangeExpected)
      ]

    -- elect new committee to be: c1 (term extended ), c3 (no changes), c4 (term shortened, expiring next epoch), c6, c7 (new)
    ga2 <-
      electCommittee
        (SJust ga1)
        drep
        [c2]
        [ (c1, 13)
        , (c4, 4)
        , (c6, 6)
        , (c7, 7)
        ]
    passEpoch -- epoch 4
    hk6 <- registerCommitteeHotKey c6
    hk8 <- registerCommitteeHotKey c8

    -- in the next epoch after the election, the old committee is still in place
    expectMembers [c1, c2, c3, c4]
    -- members that are not be part of the next committee are `ToBeRemoved`
    -- members that are part of both current and next committee have `NoChangeExpected` or `TermAdjusted`
    -- members that part of only next committee are `ToBeEnacted`
    expectNoFilterQueryResult
      [ (c1, CommitteeMemberState (MemberAuthorized hk1) Active (Just 12) (TermAdjusted 13))
      , (c2, CommitteeMemberState (MemberAuthorized hk2) Expired (Just 2) ToBeRemoved)
      , (c3, CommitteeMemberState (MemberResigned (Just c3Anchor)) Active (Just 7) NoChangeExpected)
      , -- though its term was adjusted, `ToBeExpired` takes precedence
        (c4, CommitteeMemberState MemberNotAuthorized Active (Just 5) ToBeExpired)
      , (c6, CommitteeMemberState (MemberAuthorized hk6) Unrecognized Nothing ToBeEnacted)
      , (c7, CommitteeMemberState MemberNotAuthorized Unrecognized Nothing ToBeEnacted)
      , (c8, CommitteeMemberState (MemberAuthorized hk8) Unrecognized Nothing ToBeRemoved)
      ]
    expectQueryResult
      [c2]
      [hk2]
      [Expired]
      ( Map.singleton
          c2
          (CommitteeMemberState (MemberAuthorized hk2) Expired (Just 2) ToBeRemoved)
      )

    passNEpochs 2 -- epoch 6
    -- the new committee is in place with the adjusted terms
    expectMembers [c1, c3, c4, c6, c7]
    expectNoFilterQueryResult
      [ (c1, CommitteeMemberState (MemberAuthorized hk1) Active (Just 13) NoChangeExpected)
      , (c3, CommitteeMemberState (MemberResigned (Just c3Anchor)) Active (Just 7) NoChangeExpected)
      , (c4, CommitteeMemberState MemberNotAuthorized Expired (Just 4) NoChangeExpected)
      , (c6, CommitteeMemberState (MemberAuthorized hk6) Active (Just 6) ToBeExpired)
      , (c7, CommitteeMemberState MemberNotAuthorized Active (Just 7) NoChangeExpected)
      ]
    expectQueryResult
      Set.empty
      Set.empty
      [Unrecognized]
      Map.empty

    -- elect new committee to be:
    -- c4 (which is presently `Expired`, set a new term),
    -- c6 (which is presently `ToBeExpired`, set a new term)
    -- c7 (which will become `ToBeExpired` in the next epoch)
    -- c3 (which would become `ToBeExpired` in the next epoch, but set a new term)
    _ <-
      electCommittee
        (SJust ga2)
        drep
        [c1]
        [ (c3, 9)
        , (c4, 9)
        , (c6, 9)
        ]
    passEpoch -- epoch 7
    -- members whose term changed have next epoch change `TermAdjusted`
    expectNoFilterQueryResult
      [ (c1, CommitteeMemberState (MemberAuthorized hk1) Active (Just 13) ToBeRemoved)
      , (c3, CommitteeMemberState (MemberResigned (Just c3Anchor)) Active (Just 7) (TermAdjusted 9))
      , (c4, CommitteeMemberState MemberNotAuthorized Expired (Just 4) (TermAdjusted 9))
      , (c6, CommitteeMemberState (MemberAuthorized hk6) Expired (Just 6) (TermAdjusted 9))
      , (c7, CommitteeMemberState MemberNotAuthorized Active (Just 7) ToBeExpired)
      ]
    passEpoch -- epoch 8
    expectMembers [c3, c4, c6, c7]
    expectNoFilterQueryResult
      [ (c3, CommitteeMemberState (MemberResigned (Just c3Anchor)) Active (Just 9) NoChangeExpected)
      , (c4, CommitteeMemberState MemberNotAuthorized Active (Just 9) NoChangeExpected)
      , (c6, CommitteeMemberState (MemberAuthorized hk6) Active (Just 9) NoChangeExpected)
      , (c7, CommitteeMemberState MemberNotAuthorized Expired (Just 7) NoChangeExpected)
      ]
  where
    expectMembers ::
      HasCallStack => Set.Set (Credential 'ColdCommitteeRole (EraCrypto era)) -> ImpTestM era ()
    expectMembers expKhs = do
      committee <-
        getsNES $
          nesEsL . esLStateL . lsUTxOStateL . utxosGovStateL . committeeGovStateL
      let members = Map.keysSet $ foldMap' committeeMembers committee
      impAnn "Expecting committee members" $ members `shouldBe` expKhs

    expectQueryResult ::
      HasCallStack =>
      Set.Set (Credential 'ColdCommitteeRole (EraCrypto era)) ->
      Set.Set (Credential 'HotCommitteeRole (EraCrypto era)) ->
      Set.Set MemberStatus ->
      Map.Map (Credential 'ColdCommitteeRole (EraCrypto era)) (CommitteeMemberState (EraCrypto era)) ->
      ImpTestM era ()
    expectQueryResult ckFilter hkFilter statusFilter expResult = do
      nes <- use impNESL
      let CommitteeMembersState {csCommittee} =
            queryCommitteeMembersState
              ckFilter
              hkFilter
              statusFilter
              nes
      impAnn "Expecting query result" $
        csCommittee `shouldBe` expResult

    expectNoFilterQueryResult ::
      HasCallStack =>
      Map.Map (Credential 'ColdCommitteeRole (EraCrypto era)) (CommitteeMemberState (EraCrypto era)) ->
      ImpTestM era ()
    expectNoFilterQueryResult =
      expectQueryResult mempty mempty mempty
