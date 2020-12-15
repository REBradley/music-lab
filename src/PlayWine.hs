module PlayWine where

import Prelude
import Euterpea
import Wine
import NoteFinder (chordToMusic, chordProgressionMajor)

-- vintage -> Dynamics
-- origin  -> ?
playWine :: Wine -> Music AbsPitch
playWine w@(Wine {origin = o, year = y}) = 
  let appellationList   = completeOrigin o
      Just grapeQuality = vintageRating w
  in foundation grapeQuality appellationList

foundation :: Rating -> [Origin] -> Music AbsPitch
foundation r l = 
  line $ map (chordToMusic qn) $ chordProgressionMajor [1,4,5,1] (Ds,3)
  where ratingFactor = r `quot` 100
