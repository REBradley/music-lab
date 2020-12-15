module Songs.Ambitionz2pacT where

import Euterpea
import qualified HSoM
import Songs.Ambitionz2Pac
import NoteFinder
import MusicTransformations
import Compose

-- Materials --
percsAR = bassdrumline :=: hihatsnare
chp  = chordsToMusic (repeat en) $ chordProgression (D,4) Minor [1,5,4,1]
chpd = chordsToMusic (repeat en) $ chordProgression (D,4) Minor [2,5,4,2]

-- 2 Bars --
bseslo = (times 2 $ chp :+: hnr) :=: percsAR
bsechr = (chp :+: dwnr) :=: percsAR
bsefst = times 4 chp :=: percsAR
bssync = (times 2 $ chp :+: hnr) :=: (qnr :+: remove qn percsAR)
----
hacc = (accln :=:)
lacc = (bline :=:)
facc = hacc . lacc

-- Melodies --
altchp1 = mFold Prim (:+:) (:+:) Modify chp
accdn = instrument Vibraphone $ vol SF $
        transpose 24 (cut (3/8) $ retro altchp1)
accln = offset hn accdn :+: enr :+: hnr :+: accdn

bline = instrument Contrabass $ vol SF $
        transpose (-24) $ remove wn altchp1
----

-- Briges --
dnsemel1 = altchp1 :=: transpose (-12) (chp :+: wnr)
dnsemel2 = altchp1 
           :=: 
           transpose (-12) 
             (times 3 (cut en chp :+: enr :+: cut en (retro chp)))
dnsemel3 = altchp1 
           :=: 
           transpose (-12) 
             (times 3 (cut en chp :+: cut en chpd :+: cut en (retro chp)))
----

intro = times 8
verse = times 4
pchor = times 2
chor  = times 4
brdge = times 4
outro = phrase [Dyn (Diminuendo (4/4))] . times 4

song = (intro (chp :+: hnr) :+: 
        verse bseslo `transitionWith` bssync :+: 
        verse (lacc bseslo) `transitionWith` (lacc bssync) :+: 
        pchor bsefst :+:
        chor (lacc bsechr) :+:
        verse bseslo `transitionWith` bssync :+: 
        verse (hacc bseslo) :+: 
        pchor bsefst :+:
        chor (lacc bsechr) :+:
        brdge dnsemel1 :+: 
        brdge dnsemel2 :+: 
        brdge dnsemel3 :+: 
        verse (facc bseslo) `transitionWith` (facc bssync) :+: 
        verse (facc bseslo) :+:
        outro (times 4 chp)
       )

playSong = playAmbitionz song
writeSong = writeNewMidi song



















------ TRY 2
org = instrument ReedOrgan $ 
      phrase [Dyn (Diminuendo (11/10))] $
      vol SF $ shiftPitches (0) $ 
      chordsToMusic winddurs (chordProgression (Ef,5) Major [1,6,4,5])

m1 = instrument AcousticGrandPiano $ 
     phrase [Art (Staccato (3/10))] $
     vol P $
     line $ map (noteToChord (Ef,2) Major) mainnotes

m2 = instrument StringEnsemble2 $ 
     phrase [Art (Slurred (4/10))] $
     vol FF $
     qnr :+: remove qn trillline

myambitionz2 = playAmbitionz $ ambitionz org m1 m2
-----



------ TRY 1
{- Instrument Parts
bassdrum -> Done
snaredrum -> Done
clsdhihat -> Done

piano -> Done
strings -> Done
basstr -> Done
synthacc ->
wind -> Done
-}


mel1    = (invert mainline) :+: dhnr
mel2    = retroInvert mainline :+: dhnr
basemel = forever $ mel2 :+: mel1

trill1 = trillline --Accent Base
trill2 = retro trillline

bdrum1 = cut dqn (retro bassdrumline)

base2 = mel2 
        :=: (offset qn bdrum1 
            :=: (retro clsdhihatline 
                :=: (offset (dwn + qn) $ snaredrum qn)))

base1 = mel1 
        :=: ((retro clsdhihatline :+: qnr) :=: offset dhn bdrum1)
        :=: bassacc1

base0 = base2 :+: base1

sax = instrument TenorSax $ 
      Modify (Phrase [Dyn (Diminuendo (1/4))]) $
      vol SF $ shiftPitches (-36) $ 
      line $ windnotes

bassacc1 = vol MF $ bassaccent

synthacc = vol PP $ cut 2 synth2accbase

myambitionz1 = tempo (3/2) $
               removeZeros $ 
                 cut 8 basemel :+:
                 times 2 base0 :+:
                 times 2 (base0 :=: offset qn sax) :+:
                 times 3 base2 :+: base1 :+:
                 times 2 (base0 :=: offset qn sax) :+:
                 times 5 base2 :+: base1 :+:
                 times 2 (base0 :=: offset qn sax)
-------                 
