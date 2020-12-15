{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module NoteFinderTest where

import NoteFinder
import Test.QuickCheck hiding (scale)

import Euterpea


octaves :: Gen Octave
octaves = choose (0,10)

instance Arbitrary PitchClass where
  arbitrary = arbitraryBoundedEnum

instance {-# OVERLAPPING #-} Arbitrary Pitch where
  arbitrary = do
    pc <- arbitrary
    oc <- octaves
    return (pc,oc)

keyInMajor :: AbsPitch -> Gen AbsPitch
keyInMajor ap = do let s = scale ap majorIntervals 
                   i <- choose (0,7)
                   return (s !! i)

keyInMinor :: AbsPitch -> Gen AbsPitch
keyInMinor ap = do let s = scale ap natMinorIntervals 
                   i <- choose (0,7)
                   return (s !! i)

prop_MajChords :: Pitch -> Bool
prop_MajChords p  = 
  map triadType (chordProgression p Major [1..7]) == majorScaleTriads

prop_MinChords :: Pitch -> Bool
prop_MinChords p  = 
  map triadType (chordProgression p Minor [1..7]) == natMinorScaleTriads

prop_DegreeInKeyMaj :: Pitch -> Pitch -> Property
prop_DegreeInKeyMaj k p = inKey ==> snd (findDegree k Major p) == ap
  where inKey = (tonic <= ap ) && (ap `elem` scale tonic majorIntervals)
        tonic = absPitch k
        ap    = absPitch p

prop_DegreeInKeyMajor :: Pitch -> Property
prop_DegreeInKeyMajor k =  forAll (keyInMajor tonic) $ 
                           \ap -> snd (findDegree k Major $ pitch ap) == ap
                           where tonic = absPitch k

prop_DegreeInKeyMinor :: Pitch -> Property
prop_DegreeInKeyMinor k =  forAll (keyInMinor tonic) $ 
                           \ap -> snd (findDegree k Minor $ pitch ap) == ap
                           where tonic = absPitch k
