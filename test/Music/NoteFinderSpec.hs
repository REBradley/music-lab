module Music.NoteFinderSpec where

import NoteFinder
import Euterpea
import Test.Hspec
import Test.QuickCheck hiding (scale)
import Generators


spec :: Spec
spec =
  describe "mkChord" $ do
    it "makes triads in major keys" $ property $ propMajorTriad
    it "makes triads in natural minor keys" $ property $ propNatMinorTriad

propMajorTriad :: Pitch -> Bool
propMajorTriad key =
  let majorScale = take 7 $ map pitch $ scale key majorIntervals
  in map (triadType . triadMajor key) majorScale == majorScaleTriads

propNatMinorTriad :: Pitch -> Bool
propNatMinorTriad key =
  let minorScale = take 7 $ map pitch $ scale key natMinorIntervals
  in map (triadType . triadNatMinor key) minorScale == natMinorScaleTriads
