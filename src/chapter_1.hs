import Euterpea


t251 :: Music Pitch
t251 = let dMinor = d 4 wn :=: f 4 wn :=: a 4 wn
           gMajor = g 4 wn :=: b 4 wn :=: d 5 wn
           cMajor = c 4 bn :=: e 4 bn :=: g 4 bn
       in dMinor :+: gMajor :+: cMajor

twoFiveOne :: Pitch -> Dur -> Music Pitch
twoFiveOne p d = let
                    chordii = note d (trans 2 p) :=: note d (trans 5 p) :=: note d (trans 9 p)
                    chordV = note d (trans 7 p) :=: note d (trans 11 p) :=: note d (trans 14 p)
                    chordI = note (2*d) p :=: note (2*d) (trans 4 p) :=: note (2*d) (trans 7 p)
                 in
                    chordii :+: chordV :+: chordI
-----------------


data BluesPitchClass = Ro | MT | Fo | Fi | MS

type BluesPitch = (BluesPitchClass, Octave)

ro, mt, fo, fi, ms :: Octave -> Dur -> Music BluesPitch
ro o d = note d (Ro, o)
mt o d = note d (MT, o)
fo o d = note d (Fo, o)
fi o d = note d (Fi, o)
ms o d = note d (MS, o)


fromBlues :: Music BluesPitch -> Music Pitch
fromBlues (Prim (Note d (pc,o))) = case pc of
                                            Ro    -> c o d
                                            MT    -> ef o d
                                            Fo    -> f o d
                                            Fi    -> g o d
                                            MS    -> bf o d
fromBlues (Prim (Rest d))   = Prim (Rest d)
fromBlues (m1 :+: m2)       = fromBlues m1 :+: fromBlues m2
fromBlues (m1 :=: m2)       = fromBlues m1 :=: fromBlues m2
fromBlues (Modify cntrl m)  = Modify cntrl $ fromBlues m


bluesmel1 = ro 1 bn :=: fo 1 bn :=: fi 1 bn
bluesmel2 = ro 5 wn :+: fi 5 hn :+: fo 5 hn :+: ro 5 hn
bluesmel3 = ro 3 wn :+: fo 3 wn :+: fi 3 wn
bluesmel4 = ro 4 wn :+: fo 4 wn :+: fi 4 wn
bluesmel5 = ro 5 wn :+: fo 5 wn :+: fi 5 wn
bluesmel6 = ro 6 wn :=: fo 6 wn :=: fi 6 wn
bluesmel7 = ro 7 wn :+: fo 7 wn :+: fi 7 wn
bluesmel8 = ro 8 wn :+: fo 8 wn :+: fi 8 wn
bluesmel = bluesmel1 :=: bluesmel6 :=: bluesmel2 :+: bluesmel1





{-- SHOW absPitch (pitch ap) = ap
 -
 -  absPitch (pitch ap) = let (oct,n) = divMod ap 12
 -                        in  absPitch ([C,Cs,D,Ds,E,F,Fs,G,Gs,A,As,B] !! n, oct-1) 
 -
 -                      = absPitch([C,Cs,D,Ds,E,F,Fs,G,Gs,A,As,B] !! (mod ap 12), (quot ap 12) - 1)
 -
 -                      = 12 * ((quot ap 12 - 1) + 1) + pcToInt ([C,Cs,D,Ds,E,F,Fs,G,Gs,A,As,B] !! (mod ap 12))
 -
 -                      = 12 * (quot ap 12) + pcToInt ([C,Cs,D,Ds,E,F,Fs,G,Gs,A,As,B] !! (mod ap 12)) 
 -
 -                      = 12 * (quot ap 12) + case ([C,Cs,D,Ds,E,F,Fs,G,Gs,A,As,B] !! (mod ap 12)) of
 -                                              C -> 0; Cs -> 1; D -> 2; Ds -> 3; E -> 4; F -> 5; Fs -> 6 
 -                                              G -> 7;  Gs -> 8; A -> 9; As -> 10; B -> 11;
 -                      
 -                      = 12 * (quot ap 12) + ([0..11] !! (mod ap 12))
 -                      = ap - remainder + remainder
 -                      = ap
 - 
 -
 - SHOW pitch (absPitch p) = p
 -
 - pitch (absPitch p) = let (pc_p, oct_p) = p 
 -                      in  pitch (12 * (oct_p + 1) + pcToInt pc_p)
 -
 -                    = let (o, p) = ( quot (12 * (oct_p + 1) + pcToInt pc_p) 12,
 -                                     mod  (12 * (oct_p + 1) + pcToInt pc_p) 12  )
                        in  ([C,Cs,D,Ds,E,F,Fs,G,Gs,A,As,B] !! p, o - 1)
                     
 -                    = ([C,Cs,D,Ds,E,F,Fs,G,Gs,A,As,B] !! (mod (12 * (oct_p + 1) + pcToInt pc_p) 12), 
 -                       quot (12 * (oct_p + 1) + pcToInt pc_p) 12  - 1) )
 -
 -                    ----  0 <= pcToInt pc_p <= 11   ----
 -                     
 -                    = (  [C,Cs,D,Ds,E,F,Fs,G,Gs,A,As,B] !! pcToInt pc_p,
 -                         oct_p + 1 - 1  )
 -                   
 -                    = ( [C,Cs,D,Ds,E,F,Fs,G,Gs,A,As,B] !! 
 -                           case pc_p of
 -                              C -> 0; Cs -> 1; D -> 2; Ds -> 3; E -> 4; F -> 5; Fs -> 6 
 -                              G -> 7;  Gs -> 8; A -> 9; As -> 10; B -> 11,
 -                        oct_p)
 -
 -                    = (pc_p, oct_p)
 -
 -
 -                    = p
 -
 - SHOW trans i (trans j p) = trans (i + j) p     
 -
 - trans i (trans j p ) = trans i (pitch (absPitch p + j))
 -
 -                      = pitch (absPitch (pitch (absPitch p + j)) + i)
 -
 -                      = pitch( absPitch p + j + i  )
 -
 -                      = pitch( absPitch p (i + j))
 -
 -                      = trans (i + j) p
 -
 -
 -
 - 
 -
 - --}


transM :: AbsPitch -> Music Pitch -> Music Pitch
transM ap (Prim (Note d p)) = note d (pitch (absPitch p + ap))
transM ap (Prim (Rest d))   = rest d
transM ap (m1 :+: m2)       = (transM ap m1) :+: (transM ap m2)
transM ap (m1 :=: m2)       = (transM ap m1) :=: (transM ap m2)
transM ap (Modify cntrl m)  = Modify cntrl (transM ap m) 






