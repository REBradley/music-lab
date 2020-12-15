module Songs.Ambitionz2Pac where

import Euterpea
import HSoM

-- 4/4  90 BPM --

{- Percussion Instruments -}
bassdrum,snaredrum,clsdhihat :: Dur -> Music Pitch
bassdrum  = perc AcousticBassDrum
snaredrum = perc AcousticSnare
clsdhihat = perc ClosedHiHat

{- Piano, Strings, Wind, Synth -}
piano,strings,basstr :: Music Pitch -> Music Pitch
piano   = instrument AcousticGrandPiano
strings = instrument StringEnsemble2
basstr  = instrument AcousticBass
organ   = instrument ReedOrgan
synth   = instrument Pad7Halo

vol   :: StdLoudness -> Music a -> Music a
vol l = Modify (Phrase [Dyn (StdLoudness l)])


{- Treble Lines: B-flat major (internet says D major) -}
mel       = piano mainline
trill     = strings trillline
mainline  = line mainnotes
mainnotes = [a 3 qn, rest en, d 4 qn, rest en, a 3 qn, bf 3 qn]
trillline = times 3 (line [f 5 en, d 5 en])



wind        = organ $ 
              line $ zipWith ($) windT windnotes
windnotes   = zipWith note winddurs windpitches
windpitches = [(C,7), (G,7), (Ef,7), (C,7)] :: [Pitch]
winddurs    = [dqn, (wn+qn), dqn, wn]
windT       = [vol PP, vol P, vol PP, vol PPP]

synthline2    = synth $ d 3 hn :+: c 3 hn
synthline3    = synth $ a 3 hn :+: d 3 hn :+: c 3 hn
fullsynthacc  = vol PPP $ synthline2 :+: rest hn :+: synthline3
synthaccbase  = forever $ vol PPP $
                  times 2 (synthline2 :+: wnr) :+: (synthline3 :+: wnr)
synth2accbase = forever $ vol PPP $ offset hn (synthline2 :+: hnr)

{- Percussion Lines -}
clsdhihatline = line $ map clsdhihat [en,qn,hn,en,qn,hn]
snare         = snaredrum wn :+: snaredrum hn
hihatsnare    = (clsdhihatline :+: qnr) :=: offset hn snare

bassdrumline  = line $ map bassdrum [dden,ddqn,dden,en,en]
bassaccent    = vol MF $ basstr (d 1 tn :+: d 1 ddqn :+: d 1 tn)
bass          = bassdrumline :=: bassaccent
halfdrumbass  = (bassdrum dden :+: bassdrum ddqn) :=: bassaccent

halfdrumnoacc = bassdrum dden :+: bassdrum ddqn

percussionBase :: Music Pitch
percussionBase = forever (hihatsnare :=: bass)

{- Song Structures -}
introAR m           = let introhats   = line $ map clsdhihat [dhn,en,dqn,dhn]
                      in vol FFF m :+: (vol FFF m :=: introhats :=: bassdrumline)
base m              = forever m :=: percussionBase
basehalfdrums m     = halfdrumbass :=: hihatsnare :=: m
basehalfdrumsnare m = halfdrumbass :=: offset hn (snaredrum wn) :=: m
basenoaccentsnr2 m  = bassdrumline :=: offset hn (snaredrum wn) :=: m
dropbeat m          = halfdrumnoacc 
                      :=: (cut (5/4) hihatsnare :+: offset qn (snaredrum hn)) 
                      :=: m
dropbeat2 m         = bassaccent 
                      :=: (cut dqn hihatsnare :+: rest (en + wn) :+: remove dwn hihatsnare) 
                      :=: m
startrap w          = times 2 ((clsdhihatline :+: qnr) :=: (bassaccent :+: hnr)) 
                      :=: (w :+: rest hn :+: snaredrum qn)
chorus8barsetup w m = ((cut 4 (base m) :=: w) :+: (cut 3 (base m) :+: remove wn m))
                      :=: offset dwn (cut (13/2) synthaccbase)
main8Bars w m       = ((cut 4 (base m) :=: w) :+: cut 4 (base m))
                      :=: cut 8 synth2accbase



ambitionz :: Music Pitch -> Music Pitch -> Music Pitch -> Music Pitch
ambitionz w me tr = let mt    = [vol NF, vol MF]
                        m     = line $ zipWith ($) mt [me,tr]
                        basem = base m
                    in removeZeros $
                         introAR (me :+: tr) :+:
                         cut 10 basem :+:
                         basehalfdrums m :+:
                         cut 6 basem :+:
                         (cut 4 basem :=: w) :+:
                         cut 6 basem :+:
                         startrap w :+:
                         (cut 4 basem :=: offset wn fullsynthacc) :+:
                         times 4 (main8Bars w m) :+:
                         ((cut 4 basem :=: w) :=: offset wn fullsynthacc):+:
                         basehalfdrumsnare m :+:
                         basehalfdrums m :+:
                         chorus8barsetup w m :+: 
                         (cut 4 basem :=: w) :+:  --chorus
                         cut 4 basem :+:             --chorus
                         main8Bars w m :+:
                         (cut 4 basem :=: w) :+:
                         cut 2 basem :+:
                         basenoaccentsnr2 m :+:
                         main8Bars w m :+:
                         ((cut 2 basem :+: dropbeat m) :=: w) :+:
                         cut 4 basem :+:
                         (cut 4 basem :=: w) :+:  --chorus
                         cut 4 basem :+:             --chorus
                         times 2 (main8Bars w m) :+:
                         (cut 4 basem :=: w) :+:
                         dropbeat2 m :+:
                         cut 2 basem :+:
                         times 2 (main8Bars w m) :+:
                         ((cut 4 basem :=: w) :=: offset wn fullsynthacc):+:
                         cut 4 basem :+:             --chorus
                         (cut 4 basem :=: w) :+:  --chorus
                         cut 4 basem :+:             --chorus
                         (cut 4 basem :=: w) :+:  --chorus
                         times 3 m             --outro

contextAR = defCon {cKey = (Bf,Major),cDur = metro 180 qn}

playAmbitionz :: Music Pitch -> IO ()
playAmbitionz = playA defPMap contextAR

writeNewMidiAR w m tr = 
  writeMidiA "/Users/rbradley/Projects/Beats/2Pac/ambitionz.mid" 
                  defPMap 
                  contextAR
                  $ toMusic1 (ambitionz w m tr)

writeNewMidi m name = 
  writeMidiA ("/Users/rbradley/Projects/Beats/2Pac/ambitionz" ++ name ++ ".mid") 
                  defPMap 
                  contextAR
                  $ toMusic1 m
