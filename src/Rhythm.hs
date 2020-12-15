module Rhythm (
  Beat,
  MeasureGrid,
  RhythmSpec (..),
  fullLine,
  soundOnDivLine,
  randomLine
  ) where

import Euterpea
import System.Random (RandomGen,StdGen)
import System.Random.Distributions (frequency)

type Beat = [Dur]
type Measure = [Beat]
type TimeSignature = (Int, Dur)
type Bar = (Rational, Measure)      -- ∀(r,bs) : sum bs / r = wn

mkBar :: TimeSignature -> Bar
mkBar (beats,unit) = (factor,bar)
  where factor = fromIntegral beats * unit
        bar    = replicate beats [unit]


type Stem a = a -> Music a
data Switch = Sound | Silence
type SoundRestMix a = [(Switch, Dur -> Stem a)]

lineInBar :: Bar -> SoundRestMix a -> [a] -> Music a
lineInBar (r,beats) mix sounds =
  tempo r . line $ 
  (fillRhythm mix (concat beats)) `attachHeads` sounds

attachHeads :: [(Switch, Stem a)] -> [a] -> [Music a]
attachHeads (stm:stms) wholelist@(s:ss) = 
  case stm of 
    (Sound, stm)   -> stm s : attachHeads stms ss
    (Silence, stm) -> stm s : attachHeads stms wholelist
attachHeads [] _ = []

fillRhythm :: [(Switch, Dur -> a -> Music a)] -> [Dur] -> [(Switch, Stem a)]
fillRhythm ss ds = zipWith (\(sw,mm) d -> (sw,mm d)) ss ds


type MeasureGrid = [(Int,Beat)]

transformMeasure :: (MeasureGrid -> MeasureGrid) -> Measure -> Measure
transformMeasure f = gridToMeasure . f . mkGrid

mkGrid :: Measure -> MeasureGrid
mkGrid ms = zip [1..] ms

gridToMeasure :: MeasureGrid -> Measure
gridToMeasure mg = (snd . unzip) mg


data RhythmSpec a = 
  RhythmSpec {
    tSignature   :: TimeSignature,
    measureTrans :: MeasureGrid -> MeasureGrid,
    mapToMusic   :: Dur -> a -> Music a }

----------------
-- Line Types --
----------------

mkLine :: RhythmSpec a -> SoundRestMix a -> [a] -> Music a
mkLine spec mix sl =
  lineInBar (r, (measureTrans spec) `transformMeasure` measure) mix sl
    where (r,measure) = mkBar (tSignature spec)

-- Full --
fullLine :: RhythmSpec a -> [a] -> Music a
fullLine spec sl = mkLine spec mix sl
  where mix = repeat (Sound, mapToMusic spec)

-- On Division --
soundOnDivLine :: RhythmSpec a -> [a] -> [Int] -> Music a
soundOnDivLine spec sl divs =
  lineInBar (r, (measureTrans spec) `transformMeasure` measure) mix sl
    where (r,measure) = mkBar (tSignature spec)
          mix         = intSRMix (mapToMusic spec) divs

intSRMix nf divs = (snd . unzip) $ map soundOnBeat silentSRGrid
  where silentSRGrid = zip [1..] (repeat (Silence,rest2))
        soundOnBeat = \(i,sr) -> if i `elem` divs then (i,(Sound,nf)) 
                                                  else (i,sr)
        rest2 = \d _ -> rest d

-- Random --
randomLine :: RhythmSpec a -> [a] -> Float -> (StdGen -> Music a)
randomLine spec sl p g =
  lineInBar (r, (measureTrans spec) `transformMeasure` measure) mix sl
    where (r,measure) = mkBar (tSignature spec)
          mix         = randomSRMix (mapToMusic spec) g p

randomSRMix :: (Dur -> a -> Music a) -> StdGen
               -> Float -> SoundRestMix a
randomSRMix nf g p = randsBy options g
  where options = frequency [(1-p, (Silence,rest2)), (p, (Sound,nf))]
        rest2   = \d _ -> rest d

randsBy    :: RandomGen g => (g -> (a,g)) -> g -> [a]
randsBy f g = x : randsBy f g' where (x,g') = f g
