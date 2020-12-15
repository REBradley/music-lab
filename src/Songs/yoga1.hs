module Songs.Yoga1 where

import Euterpea hiding (perc)

import System.Random

import MusicPercussionSound
import NoteFinder (chordProgression,chordsToMusic)
import RandProbabilityMarkov
import qualified RhythmSpecs as RSpec
import Rhythm
import Compose (Line(..), layer,transitionWith)
import MidiIO (writeToPath)

location :: FilePath
location = "/Users/rbradley/Projects/Beats/Yoga/yoga1.mid"

write = writeToPath (location,song)

-- BassDrum1
-- SideStick
-- OverdrivenGuitar
-- AcousticGuitarNylon

song = tempo (3/5) $ line [aS,bS,cS,bS',cS,bS'',cS,aS']

playPart m = playDevS 2 $ tempo (3/5) m

--------------
-- Sections --
--------------

aS = (times 4 $ layer [Line p1]) `transitionWith` layer [Line pf]
bS = times 4 $ layer [Line p2, Line gl1]
bS' = times 4 $ layer [Line p2, Line gl1']
bS'' = bS'
cS = (times 4 $ layer [Line p2, Line gl2]) 
     :=: layer [Line (times 3 chordq :+: chorda)]
aS' = times 4 $ layer [Line p1]

-----------
-- Lines --
-----------

chordq = addVolume 60 $ instrument AcousticGrandPiano 
         $ chordsToMusic [qn,dhn] 
         $ chordProgression (B,3) Minor [1,4]

chorda = addVolume 60 $ instrument AcousticGrandPiano 
         $ chordsToMusic [en,hn,en,qn] 
         $ chordProgression (B,3) Minor [1,2,5,1]

gl1 = addVolume 70 $ instrument OverdrivenGuitar
      $ fullLine (RSpec.note68 {measureTrans = mf}) sounds
  where mf     = RSpec.applyIf (<= 2) (RSpec.subDivide 2)
        sounds = replicate 4 (B,3) ++ [(Cs,4)] ++ repeat (B,3) :: [Pitch]

gl1' = addVolume 70 $ instrument OverdrivenGuitar
       $ fullLine (RSpec.note68 {measureTrans = mf}) sounds
  where mf     = RSpec.applyIf (\b -> (b <= 2) || (b == 6)) (RSpec.subDivide 2)
        sounds = replicate 4 (B,3) ++ [(Cs,4)] ++ repeat (B,3) :: [Pitch]

gl2 = addVolume 70 $ instrument OverdrivenGuitar $ b 5 hn :+: ds 6 hn 

p1 = instrument Percussion
     $ fullLine RSpec.perc44 sounds
  where sounds = cycle [BassDrum1,SideStick]

p2 = instrument Percussion
     $ fullLine RSpec.perc68 sounds
  where sounds = cycle [BassDrum1,SideStick,SideStick]

pf = instrument Percussion
     $ fullLine RSpec.perc68 {measureTrans = mf} sounds
  where mf     = RSpec.applyIf (\b -> b <2 || b > 4) (RSpec.subDivide 4)
        sounds = replicate 6 BassDrum1
                 ++ [CrashCymbal1,CrashCymbal1] 
                 ++ replicate 6 BassDrum1 ++ [CrashCymbal1]
