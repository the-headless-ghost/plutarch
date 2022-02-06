module Examples.ConstrData (tests) where

import Test.Tasty (TestTree, testGroup)

import Utils

tests :: HasTester => TestTree
tests = testGroup "Data construction tests" []

-- TODO: Also add tests for pair and unit PIsData instances (not in this module).
