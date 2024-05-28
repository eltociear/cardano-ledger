{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE PatternSynonyms #-}

-- | This module exports the user-facing interface for the library.
-- It is supposed to contain everything you need to write constraints
-- and implement `HasSpec` and `HasSimpleRep` instances.
module Constrained (
  Specification (..),
  Pred,
  Term,
  HasSpec (..),
  HasSimpleRep (..),
  NumLike (..),
  OrdLike (..),
  Forallable (..),
  Foldy (..),
  MaybeBounded (..),
  FunctionLike (..),
  Functions (..),
  HOLE (..),
  BaseUniverse,
  Member,
  BaseFn,
  BaseFns,
  Fix,
  OneofL,
  IsPred,
  IsNormalType,
  Value (..),
  SOP,
  (:::),
  MapFn,
  FunFn,
  -- TODO: it would be nice not to have to expose these
  PairSpec (..),
  NumSpec (..),
  MapSpec (..),
  FoldSpec (..),
  simplifySpec,
  genFromSpecT,
  genFromSpec,
  genFromSpecWithSeed,
  shrinkWithSpec,
  conformsToSpec,
  conformsToSpecProp,
  monitorSpec,
  forAllSpec,
  forAllSpecShow,
  giveHint,
  typeSpec,
  con,
  isCon,
  onCon,
  sel,
  caseBoolSpec,
  constrained,
  constrained',
  satisfies,
  letBind,
  match,
  assert,
  assertExplain,
  caseOn,
  branch,
  branchW,
  chooseSpec,
  ifElse,
  whenTrue,
  onJust,
  isJust,
  reify,
  reify',
  reifies,
  assertReified,
  explanation,
  monitor,
  genHint,
  dependsOn,
  forAll,
  forAll',
  exists,
  unsafeExists,
  fst_,
  snd_,
  pair_,
  (<=.),
  (<.),
  (==.),
  (/=.),
  (||.),
  member_,
  subset_,
  disjoint_,
  singleton_,
  elem_,
  not_,
  foldMap_,
  sum_,
  size_,
  rng_,
  dom_,
  left_,
  right_,
  toGeneric_,
  fromGeneric_,
  sizeOf_,
  length_,
  injectFn,
  app,
  lit,
  -- Working with number-like types
  emptyNumSpec,
  combineNumSpec,
  genFromNumSpec,
  shrinkWithNumSpec,
  conformsToNumSpec,
  toPredsNumSpec,
  cardinalNumSpec,
  addFn,
  -- Working with generics
  toSimpleRepSpec,
  fromSimpleRepSpec,
  algebra,
  inject,
  toPred,
  module X,
)
where

import Constrained.GenT as X
import Constrained.Internals
import Constrained.List as X
import Constrained.Properties
import Constrained.Spec.Tree as X
