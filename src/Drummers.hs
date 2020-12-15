module Drummers where

import Euterpea
import HSoM
import InterpAndPerf

{- What I'm Building: 
 - © I need to build up a system of describing the concept of bars and time signatures.
 - I need to have a way of describing one player's Score for a song (e.g. a
 - player for hihats)
 - I need a way to Compose Scores.
 -
 - Analogy: 
 - Lines        are Transposed Vectors
 - Bars         are Vectors
 - Compositions are Matrices
 -
 - You can apply a transformation (n x 1 vector) to an mxn-bar-wide composition
 - [1
 -  0
 -  0
 -  1] Select out the ith bar in all lines
 -
 - What's The Interface:
 - TimeSig = [Dur]
 -
 - Percussion :: TimeSig -> [[Dur]] -> Music a
 - NoteInst :: TimeSig -> [[Dur]] -> [Pitch] -> Music a
 -
 - TimeSig -> PlayerScore
 - [PlayerScore] -> Composition
 -
 - Why I'm Building It: Trying to manipulate musical values within a song is
 - difficult. This is because before this module, a song would be one long
 - sequence of Music values using ":=:" and ":+:" on sections of a song,
 - without some way to specify a particular player's "score" and bar
 - interval within that score. I need a "song" to have a better way of being
 - constructed and manipulated. Thus, bars can be manipulated themselves within
 - a score, all bars of a song going vertically can be manipulated to affect all
 - scores, and certain subsets going horizontally can be manipulated. I need a
 - higher level overview on how to specify songs.
 - -}

{- Things to Know:
 - PercussionSound is required in order to turn durations into Music Values.
 - This is done through (perc :: PercussionSound -> Dur -> Music Pitch).
 -
 - type PMap a = PlayerName -> Player a
 - type PlayerName = String
 - type PhraseFun a = PMap a -> Context a -> [PhraseAttribute]
 -                    -> Music a -> (Performance DurT)
-}

lnHat = line (map (perc ClosedHiHat) [en,qn,hn,en,qn,hn]) :+: qnr
lnSnare = hnr :+: (perc AcousticSnare) hn :+: hnr :+: (perc AcousticSnare) hn
lnDrum = line (map (perc AcousticBassDrum) [dden,ddqn,dden,en,en]) :+: ddhnr

tHat = line (map (perc ClosedHiHat) [sn,en,qn,sn,en,qn])
tSnare = offset qn $ (perc AcousticSnare) hn :+: (perc AcousticSnare) qn
tDrum = line (map (perc AcousticBassDrum) [en,qn,en,sn,sn])

pLines = [line hats,line snare,line drum]
         where durToHat = map (perc ClosedHiHat) 
               durToSnr = map (perc AcousticSnare)
               durToDrm = map (perc AcousticBassDrum)
               hats  = (durToHat [sn,en,sn]) 
                       ++ ([denr] ++ durToHat [sn])
                       ++ durToHat [en,en]
                       ++ [qnr]
               snare = [qnr] ++ durToSnr [qn] ++ [qnr] ++ durToSnr [qn]
               drum  = durToDrm [en,en]
                       ++ [enr] ++ durToDrm [en]
                       ++ durToDrm [sn,sn] ++ [enr]
                       ++ [qnr]


tScore = mkScore (4,qn) 4 tDrum

type Score a = [(BarOld, Music a)]
type BarOld = Int
type TimeSig = (Int,Dur)
type Composition a = [(PlayerName, Score a)]
--Not needed: Only thing of value is cycling loop for us
--
mkScore :: TimeSig -> BarOld -> Music a -> Score a
mkScore (beats,d) dblb m = 
  let loop      = cycle
      enumerate = zip [1.. dblb]
  in enumerate $ loop (mkMeasure m)
  where measureDur   = fromIntegral beats * d
        mkMeasure m' = 
          case (compare measureDur (dur m')) of
            EQ -> [m']
            GT -> [m' :+: rest (measureDur - dur m')]
            LT -> [cut measureDur m'] ++ mkMeasure (remove measureDur m')

scoreToMusic :: Score a -> Music a
scoreToMusic = foldr ((:+:) . snd) (rest 0)

together = chord

compositionToMusic :: Composition a -> Music a
compositionToMusic = together . map seatPlayer
  where seatPlayer (pn,bars) =  Modify (Custom $ "Player " ++ pn) $ scoreToMusic bars



-- Next: TRANSFORMING MUSIC --
applyModifications :: [(Int, Music a)] -> [(Int, Music a)]
applyModifications = map mods
  where mods = \(b,m)-> if b `mod` 4 == 0 
                        then (b, Modify (Phrase [Orn Trill]) m) 
                        else (b, m)

