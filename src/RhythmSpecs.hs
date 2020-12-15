module RhythmSpecs where

import Euterpea hiding (perc)
import MusicPercussionSound

import Rhythm


applyAll :: (Beat -> Beat) -> (MeasureGrid -> MeasureGrid)
applyAll f = map (\(n,b) -> (n, f b))

applyIf :: (Int -> Bool) -> (Beat -> Beat) -> (MeasureGrid -> MeasureGrid)
applyIf p f = map (\(n,beat) -> if p n == True then (n, f beat) 
                                               else (n, beat))

subDivide :: Int -> (Beat -> Beat)
subDivide subs ds = replicate subs (unit/(fromIntegral subs))
  where unit = sum ds / fromIntegral (length ds)

-- 4/4
perc44 = RhythmSpec
  {tSignature = (4,qn),
   mapToMusic = perc,
   measureTrans = applyAll id}

perc44odd2div = perc44 {measureTrans = applyIf odd (subDivide 2)}
perc44even4div = perc44 {measureTrans = applyIf even (subDivide 4)}


note44 = RhythmSpec
  {tSignature = (4,qn),
   mapToMusic = note,
   measureTrans = applyAll id}

-- 6/8
perc68 = RhythmSpec
  {tSignature = (6,en),
   mapToMusic = perc,
   measureTrans = applyAll id}

note68 = RhythmSpec
  {tSignature = (6,en),
   mapToMusic = note,
   measureTrans = applyAll id}
