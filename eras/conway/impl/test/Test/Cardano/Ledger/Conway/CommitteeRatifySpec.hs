{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Test.Cardano.Ledger.Conway.CommitteeRatifySpec (spec) where

import Cardano.Ledger.BaseTypes (EpochNo (..), StrictMaybe (..))
import Cardano.Ledger.CertState (CommitteeState (..))
import Cardano.Ledger.Conway
import Cardano.Ledger.Conway.Core
import Cardano.Ledger.Conway.Governance (
  GovAction (..),
  GovActionState (..),
  RatifyState,
  Vote (..),
  ensCommitteeL,
  rsEnactStateL,
 )
import Cardano.Ledger.Conway.Rules (
  RatifyEnv (..),
  committeeAccepted,
  committeeAcceptedRatio,
 )
import Cardano.Ledger.Credential (Credential (..))
import Cardano.Ledger.Keys (KeyRole (..))
import Control.Monad (guard, join)
import Data.Functor.Identity (Identity)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes)
import Data.Ratio ((%))
import qualified Data.Set as Set
import Lens.Micro ((&), (.~))
import Test.Cardano.Ledger.Common
import Test.Cardano.Ledger.Conway.Arbitrary ()
import Test.Cardano.Ledger.Core.Arbitrary ()

spec :: Spec
spec = do
  describe "Committee Ratification" $ do
    acceptedRatioProp @Conway
    acceptedProp @Conway
    allYesProp @Conway
    allNoProp @Conway
    allAbstainProp @Conway
    resignedMembersProp @Conway
    expiredMembersProp @Conway

acceptedRatioProp :: forall era. Era era => Spec
acceptedRatioProp =
  prop "Committee vote count for arbitrary vote ratios" $
    forAll genRatios $ \ratios -> do
      forAll (genTestData ratios) $
        \TestData {members, votes, committeeState} -> do
          let acceptedRatio =
                committeeAcceptedRatio @era members (totalVotes votes) committeeState (EpochNo 0)
              Votes {..} = votes
              -- everyone is registered and noone is resigned,
              -- so we expect the accepted ratio to be yes / (yes + no + noVoted)
              expectedRatio =
                toInteger (length votedYes)
                  % toInteger (length votedYes + length votedNo + length notVoted)

          acceptedRatio `shouldBe` expectedRatio

          -- we can also express this as : yes / (total - abstain)
          let expectedRatioAlt =
                toInteger (length votedYes)
                  % toInteger (length members - length votedAbstain)

          acceptedRatio `shouldBe` expectedRatioAlt

acceptedProp ::
  forall era.
  ( EraPParams era
  , Arbitrary (PParamsHKD Identity era)
  , Arbitrary (PParamsHKD StrictMaybe era)
  ) =>
  Spec
acceptedProp =
  prop "Only NoConfidence or UpdateCommittee should pass without a committee" $
    forAll (arbitrary @(RatifyState era, RatifyEnv era, GovActionState era)) $ do
      \(rs, rEnv, gas) -> do
        committeeAccepted @era (rs & rsEnactStateL . ensCommitteeL .~ SNothing) rEnv gas
          `shouldBe` isNoConfidenceOrUpdateCommittee gas
  where
    isNoConfidenceOrUpdateCommittee GovActionState {gasAction} =
      case gasAction of
        NoConfidence {} -> True
        UpdateCommittee {} -> True
        _ -> False

allYesProp :: forall era. Era era => Spec
allYesProp =
  prop "If all vote yes, ratio is 1" $
    forAll (genTestData (Ratios {yes = 1, no = 0, abstain = 0})) $
      \TestData {members, votes, committeeState} -> do
        let acceptedRatio =
              committeeAcceptedRatio @era members (totalVotes votes) committeeState (EpochNo 0)
        acceptedRatio `shouldBe` 1

allNoProp :: forall era. Era era => Spec
allNoProp =
  prop "If all vote no, ratio is 0" $
    forAll (genTestData (Ratios {yes = 0, no = 1, abstain = 0})) $
      \TestData {members, votes, committeeState} -> do
        let acceptedRatio =
              committeeAcceptedRatio @era members (totalVotes votes) committeeState (EpochNo 0)
        acceptedRatio `shouldBe` 0

allAbstainProp :: forall era. Era era => Spec
allAbstainProp =
  prop "If all abstain, ratio is 0" $
    forAll (genTestData (Ratios {yes = 0, no = 0, abstain = 1})) $
      \TestData {members, votes, committeeState} -> do
        let acceptedRatio =
              committeeAcceptedRatio @era members (totalVotes votes) committeeState (EpochNo 0)
        acceptedRatio `shouldBe` 0

resignedMembersProp :: forall era. Era era => Spec
resignedMembersProp =
  prop "Resigned members are not counted" $
    forAll genRatios $ \ratios -> do
      forAll (genTestData @era ratios) $
        \testData -> do
          let Votes {votedYes, votedNo, notVoted} = votes testData
              -- resign all "no" voters
              TestData {members = members', votes = votes', committeeState = committeeState'} =
                resignMembers @era votedNo testData
              acceptedRatio' =
                committeeAcceptedRatio @era members' (totalVotes votes') committeeState' (EpochNo 0)
              expectedRatio' =
                if (length votedYes + length notVoted) == 0
                  then 0
                  else
                    toInteger (length votedYes)
                      % toInteger (length votedYes + length notVoted)
          acceptedRatio' `shouldBe` expectedRatio'
          -- resign half of the "yes" voters
          let resignedYes = length votedYes `div` 2
              remainingYes = length votedYes - resignedYes
              TestData {members = members'', votes = votes'', committeeState = committeeState''} =
                resignMembers @era (Set.take resignedYes votedYes) testData
              acceptedRatio'' =
                committeeAcceptedRatio @era members'' (totalVotes votes'') committeeState'' (EpochNo 0)
              expectedRatio'' =
                if (remainingYes + length votedNo + length notVoted) == 0
                  then 0
                  else
                    toInteger remainingYes
                      % toInteger (remainingYes + length votedNo + length notVoted)
          acceptedRatio'' `shouldBe` expectedRatio''

-- TODO: remove duplication between `resignedMembersProp` and `expiredMembersProp`
-- TODO: generalize setting expired and resigned members
expiredMembersProp :: forall era. Era era => Spec
expiredMembersProp =
  prop "Expired members are not counted" $
    forAll genRatios $ \ratios -> do
      forAll (genTestData @era ratios) $
        \testData -> do
          let Votes {votedYes, votedNo, votedAbstain, notVoted} = votes testData
              -- expire all "no" voters
              TestData {members = members', votes = votes', committeeState = committeeState'} =
                expireMembers @era votedNo (EpochNo 0) testData
              acceptedRatio' =
                committeeAcceptedRatio @era members' (totalVotes votes') committeeState' (EpochNo 5)
              expectedRatio' =
                if (length votedYes + length notVoted) == 0
                  then 0
                  else
                    toInteger (length votedYes)
                      % toInteger (length votedYes + length notVoted)
          acceptedRatio' `shouldBe` expectedRatio'

          -- expire half of the "yes" voters
          let expiredYes = length votedYes `div` 2
              remainingYes = length votedYes - expiredYes
              TestData {members = members'', votes = votes'', committeeState = committeeState''} =
                expireMembers @era (Set.take expiredYes votedYes) (EpochNo 0) testData
              acceptedRatio'' =
                committeeAcceptedRatio @era members'' (totalVotes votes'') committeeState'' (EpochNo 5)
              expectedRatio'' =
                if (remainingYes + length votedNo + length notVoted) == 0
                  then 0
                  else
                    toInteger remainingYes
                      % toInteger (remainingYes + length votedNo + length notVoted)
          acceptedRatio'' `shouldBe` expectedRatio''

          -- expire all "abstain" voters and check that the ratio is the same as when they are not expired
          let TestData {members = members''', votes = votes''', committeeState = committeeState'''} =
                expireMembers @era votedAbstain (EpochNo 0) testData
          committeeAcceptedRatio @era members''' (totalVotes votes''') committeeState''' (EpochNo 5)
            `shouldBe` committeeAcceptedRatio @era (members testData) (totalVotes (votes testData)) (committeeState testData) (EpochNo 5)

data Ratios = Ratios
  { yes :: Rational
  , no :: Rational
  , abstain :: Rational
  }
  deriving (Show)

data TestData era = TestData
  { members :: Map (Credential 'ColdCommitteeRole (EraCrypto era)) EpochNo
  , votes :: Votes era
  , committeeState :: CommitteeState era
  }
  deriving (Show)

data Votes era = Votes
  { votedYes :: Set.Set (Credential 'HotCommitteeRole (EraCrypto era))
  , votedNo :: Set.Set (Credential 'HotCommitteeRole (EraCrypto era))
  , votedAbstain :: Set.Set (Credential 'HotCommitteeRole (EraCrypto era))
  , notVoted :: Set.Set (Credential 'HotCommitteeRole (EraCrypto era))
  }
  deriving (Show)

genTestData ::
  forall era.
  Era era =>
  Ratios ->
  Gen (TestData era)
genTestData ratios = do
  coldCreds <- genNonEmptyColdCreds @era
  committeeState@(CommitteeState {csCommitteeCreds}) <- genNonResignedCommitteeState @era coldCreds
  members <- genMembers @era coldCreds
  let hotCreds = Set.fromList $ catMaybes $ Map.elems csCommitteeCreds
      votes = distributeVotes @era ratios hotCreds
  pure $ TestData members votes committeeState

resignMembers ::
  Set.Set (Credential 'HotCommitteeRole (EraCrypto era)) ->
  TestData era ->
  TestData era
resignMembers hotCreds tc@TestData {committeeState} =
  tc
    { committeeState =
        CommitteeState
          ( Map.map
              (\mhk -> mhk >>= \hk -> hk <$ guard (hk `Set.notMember` hotCreds))
              (csCommitteeCreds committeeState)
          )
    }

expireMembers ::
  Set.Set (Credential 'HotCommitteeRole (EraCrypto era)) ->
  EpochNo ->
  TestData era ->
  TestData era
expireMembers hotCreds newEpochNo td@TestData {members, committeeState} =
  td
    { members =
        Map.mapWithKey (\ck epochNo -> if expire ck then newEpochNo else epochNo) members
    }
  where
    expire ck = hk ck `Set.isSubsetOf` hotCreds
    hk ck =
      maybe Set.empty Set.singleton $
        join $
          Map.lookup ck (csCommitteeCreds committeeState)

totalVotes :: Votes era -> Map (Credential 'HotCommitteeRole (EraCrypto era)) Vote
totalVotes Votes {votedYes, votedNo, votedAbstain} =
  Map.unions
    [ Map.fromSet (const VoteYes) votedYes
    , Map.fromSet (const VoteNo) votedNo
    , Map.fromSet (const Abstain) votedAbstain
    ]

genNonEmptyColdCreds :: Era era => Gen (Set.Set (Credential 'ColdCommitteeRole (EraCrypto era)))
genNonEmptyColdCreds =
  Set.fromList <$> listOf1 arbitrary

genMembers ::
  Set.Set (Credential 'ColdCommitteeRole (EraCrypto era)) ->
  Gen (Map (Credential 'ColdCommitteeRole (EraCrypto era)) EpochNo)
genMembers coldCreds =
  Map.fromList . zip (Set.toList coldCreds)
    <$> vectorOf (length coldCreds) (EpochNo <$> choose (10, 100))

genNonResignedCommitteeState ::
  forall era.
  Era era =>
  Set.Set (Credential 'ColdCommitteeRole (EraCrypto era)) ->
  Gen (CommitteeState era)
genNonResignedCommitteeState coldCreds = do
  hotCredsMap <- sequence $ Map.fromSet (\_ -> Just <$> arbitrary) coldCreds
  pure $ CommitteeState hotCredsMap

distributeVotes ::
  Ratios ->
  Set.Set (Credential 'HotCommitteeRole (EraCrypto era)) ->
  Votes era
distributeVotes Ratios {yes, no, abstain} hotCreds = do
  let (yesCreds, noCreds, abstainCreds, notVotedCreds) = splitByPct yes no abstain hotCreds
   in Votes
        { votedYes = yesCreds
        , votedNo = noCreds
        , votedAbstain = abstainCreds
        , notVoted = notVotedCreds
        }
  where
    splitByPct ::
      Rational ->
      Rational ->
      Rational ->
      Set.Set a ->
      (Set.Set a, Set.Set a, Set.Set a, Set.Set a)
    splitByPct x y z l =
      let
        size = fromIntegral $ length l
        (xs, rest) = Set.splitAt (round (x * size)) l
        (ys, rest') = Set.splitAt (round (y * size)) rest
        (zs, rest'') = Set.splitAt (round (z * size)) rest'
       in
        (xs, ys, zs, rest'')

genRatios :: Gen Ratios
genRatios = do
  (a, b, c, _) <- genPctsOf100
  pure $ Ratios {yes = a, no = b, abstain = c}

genPctsOf100 :: Gen (Rational, Rational, Rational, Rational)
genPctsOf100 = do
  a <- choose (0, 100)
  b <- choose (0, 100)
  c <- choose (0, 100)
  d <- choose (0, 100)
  let s = a + b + c + d
  pure (a % s, b % s, c % s, d % s)
