{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wno-unused-local-binds #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

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
import Cardano.Ledger.Conway.PParams (ConwayEraPParams)
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
import Data.List ((\\))
import qualified Data.Set as Set
import Lens.Micro ((&), (.~))
import Test.Cardano.Ledger.Common
import Test.Cardano.Ledger.Conway.Arbitrary ()
import Test.Cardano.Ledger.Core.Arbitrary ()

import Debug.Trace (trace)

spec :: Spec
spec = do
  describe "Committee Ratification" $ do
    acceptedRatioProp @Conway
    acceptedProp @Conway
    allYesProp @Conway
    allNoProp @Conway
    allAbstainProp @Conway
    resignedMembersProp @Conway
    resignedMembersProp2 @Conway
    expiredMembersProp @Conway
    expiredAndResignedMembersProp @Conway

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
              expectedRatio = ratioOrZero
                                (length votedYes)
                                (length votedYes + length votedNo + length notVoted)

          acceptedRatio `shouldBe` expectedRatio

          -- we can also express this as : yes / (total - abstain)
          let expectedRatioAlt = ratioOrZero
                                  (length votedYes)
                                  (length members - length votedAbstain)

          acceptedRatio `shouldBe` expectedRatioAlt

acceptedProp ::
  forall era.
  ( ConwayEraPParams era
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


expiredAndResignedMembersProp :: forall era. Era era => Spec
expiredAndResignedMembersProp =
  prop "Expired or resigned members are not counted" $ withMaxSuccess 1000 $
     -- $ withMaxSuccess 100 $
    forAll genRatios $ \ratios -> do
      forAll (genTestData @era ratios) $
        \testData -> do
          let Votes {votedYes, votedNo, votedAbstain, notVoted} = votes testData
          forAll (arbitrary @(Rational, Rational, Rational, Rational)) $
            \(pctYes, pctNo, pctAbstain, pctNotVoted) -> do
                let (td, remainingYes) = doSomething @era testData pctYes votedYes (expireMembers (EpochNo 5))
                    (td', remainingNo) = doSomething @era td pctNo votedNo resignMembers
                    (td'', remainingAbstain) = doSomething @era td' pctAbstain votedAbstain expireAndResign
                    (td''', remainingNotVoted) = doSomething @era td'' pctNotVoted notVoted expireAndResign
                    TestData {members, votes, committeeState} = td'''
                    acceptedRatio =
                      committeeAcceptedRatio @era members (totalVotes votes) committeeState (EpochNo 10)
                    expectedRatio = ratioOrZero
                                    remainingYes
                                    (remainingYes + remainingNo + remainingNotVoted)
                acceptedRatio `shouldBe` expectedRatio
            where
                  expireAndResign :: Set.Set (Credential 'HotCommitteeRole (EraCrypto era)) -> TestData era -> TestData era
                  expireAndResign hotCreds td =
                      let td' = expireMembers (EpochNo 5) hotCreds td
                          td'' = resignMembers hotCreds td'
                      in td''

doSomething ::
  forall era.
  Era era =>
  TestData era ->
  Rational ->
  [Credential 'HotCommitteeRole (EraCrypto era)] ->
  (Set.Set (Credential 'HotCommitteeRole (EraCrypto era)) -> TestData era -> TestData era) ->
  (TestData era, Int)
doSomething td pct votes action =
  let
    votesSet = Set.fromList votes
    affectedSize =  pctOfN pct (length votes)
    affectedVotes = Set.take affectedSize votesSet
    remainingVotes = filter (`notElem` Set.toList affectedVotes) votes
    remainingSize = length remainingVotes
    res = action affectedVotes td
  in (res, remainingSize)
  where
    pctOfN :: Rational -> Int -> Int
    pctOfN p n = floor (p * fromIntegral n)

resignedMembersProp2 :: forall era. Era era => Spec
resignedMembersProp2 =
  prop "Resigned members are not counted" $ --withMaxSuccess 10 $
     --withMaxSuccess 10 $
    forAll genRatios $ \ratios -> do
      forAll (genTestData @era ratios) $
        \testData -> do
          let Votes {votedYes, votedNo, votedAbstain, notVoted} = votes testData
          forAll (arbitrary @(Rational, Rational, Rational, Rational)) $
            \(pctYes, pctNo, pctAbstain, pctNotVoted) -> do
              -- resign some of each votes
              let (td, remainingYes) = doSomething @era testData pctYes votedYes resignMembers
                  (td', remainingNo) = doSomething @era td pctNo votedNo resignMembers
                  (td'', remainingAbstain) = doSomething @era td' pctAbstain votedAbstain resignMembers
                  (td''', remainingNotVoted) = doSomething @era td'' pctNotVoted notVoted resignMembers
                  TestData {members, votes, committeeState} = td'''
                  acceptedRatio =
                    committeeAcceptedRatio @era members (totalVotes votes) committeeState (EpochNo 0)
                  expectedRatio = ratioOrZero
                                  remainingYes
                                  (remainingYes + remainingNo + remainingNotVoted)
              acceptedRatio `shouldBe` expectedRatio

resignedMembersProp :: forall era. Era era => Spec
resignedMembersProp =
  prop "xxxResigned members are not counted" $ withMaxSuccess 1000 $
    forAll genRatios $ \ratios -> do
      forAll (genTestData @era ratios) $
        \testData -> do
          let Votes {votedYes, votedNo, notVoted} = votes testData
              -- resign all "no" voters
              TestData {members = members', votes = votes', committeeState = committeeState'} =
                resignMembers @era (Set.fromList votedNo) testData
              acceptedRatio' =
                committeeAcceptedRatio @era members' (totalVotes votes') committeeState' (EpochNo 0)
              expectedRatio' = ratioOrZero
                                  (length votedYes)
                                  (length votedYes + length notVoted)
          acceptedRatio' `shouldBe` expectedRatio'
          -- resign half of the "yes" voters
          let votedYesSet = Set.fromList votedYes
              resignedYes = length votedYes `div` 5
              resignedYesMembers = Set.take resignedYes votedYesSet
              remainingYesMembers = filter (`notElem` Set.toList resignedYesMembers) votedYes
              remainingYes = length remainingYesMembers
              TestData {members = members'', votes = votes'', committeeState = committeeState''} =
                resignMembers @era resignedYesMembers testData
          let acceptedRatio'' =
                committeeAcceptedRatio @era members'' (totalVotes votes'') committeeState'' (EpochNo 0)
              expectedRatio'' = ratioOrZero
                                  remainingYes
                                  (remainingYes + length votedNo + length notVoted)
          acceptedRatio'' `shouldBe` expectedRatio''

expiredMembersProp :: forall era. Era era => Spec
expiredMembersProp =
  prop "Expired members are not counted" $ withMaxSuccess 100 $
    forAll genRatios $ \ratios -> do
      forAll (genTestData @era ratios) $
        \testData -> do
          let Votes {votedYes, votedNo, votedAbstain, notVoted} = votes testData
          forAll (arbitrary @(Rational, Rational, Rational, Rational)) $
            \(pctYes, pctNo, pctAbstain, pctNotVoted) -> do
              -- expire some of each votes
              let (td, remainingYes) = doSomething @era testData pctYes votedYes (expireMembers (EpochNo 5))
              let
                  (td', remainingNo) = doSomething @era td pctNo votedNo (expireMembers (EpochNo 5))
                  (td'', remainingAbstain) = doSomething @era td' pctAbstain votedAbstain (expireMembers (EpochNo 5))
                  (td''', remainingNotVoted) = doSomething @era td'' pctNotVoted notVoted (expireMembers (EpochNo 5))
                  TestData {members, votes, committeeState} = td'''
                  acceptedRatio =
                    committeeAcceptedRatio @era members (totalVotes votes) committeeState (EpochNo 10)
                  expectedRatio = ratioOrZero
                                  remainingYes
                                  (remainingYes + remainingNo + remainingNotVoted)
              acceptedRatio `shouldBe` expectedRatio

-- TODO: remove duplication between `resignedMembersProp` and `expiredMembersProp`
-- TODO: generalize setting expired and resigned members
expiredMembersProp2 :: forall era. Era era => Spec
expiredMembersProp2 =
  prop "xxxExpired members are not counted" $
    forAll genRatios $ \ratios -> do
      forAll (genTestData @era ratios) $
        \testData -> do
          let Votes {votedYes, votedNo, votedAbstain, notVoted} = votes testData
              -- expire all "no" voters
              TestData {members = members', votes = votes', committeeState = committeeState'} =
                expireMembers @era (EpochNo 0) (Set.fromList votedNo) testData
              acceptedRatio' =
                committeeAcceptedRatio @era members' (totalVotes votes') committeeState' (EpochNo 5)
              expectedRatio' = ratioOrZero
                                (length votedYes)
                                (length votedYes + length notVoted)
          acceptedRatio' `shouldBe` expectedRatio'

          -- expire half of the "yes" voters
          let expiredYes = length votedYes `div` 2
              remainingYes = length votedYes - expiredYes
              TestData {members = members'', votes = votes'', committeeState = committeeState''} =
                expireMembers @era (EpochNo 0) (Set.take expiredYes (Set.fromList votedYes)) testData
              acceptedRatio'' =
                committeeAcceptedRatio @era members'' (totalVotes votes'') committeeState'' (EpochNo 5)
              expectedRatio'' = ratioOrZero
                                 remainingYes
                                 (remainingYes + length votedNo + length notVoted)
          acceptedRatio'' `shouldBe` expectedRatio''

          -- expire all "abstain" voters and check that the ratio is the same as when they are not expired
          let TestData {members = members''', votes = votes''', committeeState = committeeState'''} =
                expireMembers @era (EpochNo 0) (Set.fromList votedAbstain) testData
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
  { votedYes :: [Credential 'HotCommitteeRole (EraCrypto era)]
  , votedNo :: [Credential 'HotCommitteeRole (EraCrypto era)]
  , votedAbstain :: [Credential 'HotCommitteeRole (EraCrypto era)]
  , notVoted :: [Credential 'HotCommitteeRole (EraCrypto era)]
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
  let hotCreds = catMaybes $ Map.elems csCommitteeCreds
      votes = distributeVotes @era ratios hotCreds
  pure $ TestData members votes committeeState

resignMembers ::
  Set.Set (Credential 'HotCommitteeRole (EraCrypto era)) ->
  TestData era ->
  TestData era
resignMembers hotCreds td@TestData {committeeState} =
  td
    { committeeState =
        CommitteeState
          ( Map.map
              (\mhk -> mhk >>= \hk -> hk <$ guard (hk `Set.notMember` hotCreds))
              (csCommitteeCreds committeeState)
          )
    }

expireMembers ::
  EpochNo ->
  Set.Set (Credential 'HotCommitteeRole (EraCrypto era)) ->
  TestData era ->
  TestData era
expireMembers newEpochNo hotCreds td@TestData {members, committeeState} =
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
    [ Map.fromSet (const VoteYes) (Set.fromList votedYes)
    , Map.fromSet (const VoteNo) (Set.fromList votedNo)
    , Map.fromSet (const Abstain) (Set.fromList votedAbstain)
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
  frequency
    [ (9, pure $ CommitteeState hotCredsMap)
    , (1, CommitteeState <$> overwriteWithDuplicate hotCredsMap)
    ]
  where
    overwriteWithDuplicate m
      | Map.size m < 2 = pure m
      | otherwise = do
        fromIx <- choose (0, Map.size m - 1)
        toIx <- choose (0, Map.size m - 1)
        let valueToDuplicate = snd $ Map.elemAt fromIx m
        let updateIfDefined valueToReplace =
              case (valueToReplace, valueToDuplicate) of
                (Just _, Just _) -> Just valueToDuplicate
                _ -> Just valueToReplace
        pure $ Map.updateAt (\_ v -> updateIfDefined v) toIx m

distributeVotes ::
  Ratios ->
  [Credential 'HotCommitteeRole (EraCrypto era)] ->
  Votes era
distributeVotes Ratios {yes, no, abstain} hotCreds = do
  let
    -- The list of hot credentials, which we split into the 4 voting categories, may contain duplicates.
    -- We want the duplicates to be in the same category (since this is what will happen in practice,
    -- where the votes is a Map from hot credential to vote).
    -- So we first remove the duplicates, then split the list into the 4 categories,
    -- and then add the duplicates back.
    hotCredsSet = Set.fromList hotCreds
    duplicates = Set.fromList $ hotCreds \\ Set.toList hotCredsSet
    (yesCreds, noCreds, abstainCreds, notVotedCreds) = splitByPct yes no abstain hotCredsSet
   in Votes
        { votedYes = addDuplicates yesCreds duplicates
        , votedNo = addDuplicates noCreds duplicates
        , votedAbstain = addDuplicates abstainCreds duplicates
        , notVoted = addDuplicates notVotedCreds duplicates
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
    addDuplicates :: Ord a => Set.Set a -> Set.Set a -> [a]
    addDuplicates s dups =
        if dups `Set.isSubsetOf` s
          then Set.toList s ++ Set.toList dups
          else Set.toList s

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

ratioOrZero :: Integral a => a -> a -> Rational
ratioOrZero a b =
  if b == 0
    then 0
    else fromIntegral a % fromIntegral b
