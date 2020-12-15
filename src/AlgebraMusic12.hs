module AlgebraMusic where

import Prelude
import Euterpea

{-Exercise 12.1: Prove Lemma 12.1.1
 -
 - For all pm, c, and m
 -
 - perf pm c = (hsomPerform pm c m,dur m * cDur c)
 -
 - PROVED AS LAST EXERCISE OF CHAPTER 11
 -}

{-Exercise 12.2: Establish the validity of each of the (below) axioms.

Let tempo r     = Modify (Tempo r)
    transpose p = Modify (Transpose p)
    dt          = cDur c
    t           = cTime c
    k           = cKey c

Axiom 12.3.1 Tempo is multiplicative and Transpose is additive. That is,
for any r1,r2,p1,p2...

    tempo r1 (tempo r2 m) ≡ tempo (r1*r2) m
    PROVED IN EXAMPLE 12.2.1


    trans p1 (trans p2 m) ≡ trans (p1+p2) m

perform pm c (trans p1 (trans p2 m))
-> perform pm (c{cKey = k + p1}) (trans p2 m)
-> perform pm (c{cKey = k + p1 + p2}) m
-> perform pm (c{cKey = k + (p1 + p2)}) m
-> perform pm c (trans (p1 + p2) m)

dur (trans p1 (trans p2 m))
-> dur (trans p2 m)
-> dur m
-> dur (trans (p1 + p2) m)


Axiom 12.3.2 Function composition is commutative with respect to both 
tempo scaling and transposition. That is for any r1,r2,p1, and p2...

    tempo r1 . tempo r2 ≡ tempo r2 . tempo r1

perform pm c ((tempo r1 . tempo r2) m)
-> perform pm c (tempo r1 (tempo r2 m))
-> perform pm (c{cDur = dt/r1}) (tempo r2 m)
-> perform pm (c{cDur = (dt/r1)/r2}) m
-> perform pm (c{cDur = (dt/r2)/r1}) m
-> perform pm (c{cDur = dt/r2}) (tempo r1 m)
-> perform pm c (tempo r2 (tempo r1 m))
-> perform pm c ((tempo r2 . tempo r1) m)

dur ((tempo r1 . tempo r2) m)
-> dur (tempo r1 (tempo r2 m))
-> dur (tempo r2 m) / r1
-> (dur m / r1) / r2
-> (dur m / r2) / r1
-> dur (tempo r1 m) / r2
-> dur (tempo r2 (tempo r1 m))
-> dur ((tempo r2 . tempo r1) m)


    trans p1 . trans p2 ≡ trans p2 . trans p1

perform pm c ((trans p1 . trans p2) m)
-> perform pm c (trans p1 (trans p2 m))
-> perform pm (c{cKey = k + p1}) (trans p2 m)
-> perform pm (c{cKey = (k + p1) + p2}) m
-> perform pm (c{cKey = k + (p1 + p2)}) m
-> perform pm (c{cKey = k + (p2 + p1)}) m
-> perform pm (c{cKey = (k + p2) + p1}) m
-> perform pm (c{cKey = k + p2}) (trans p1 m)
-> perform pm c (trans p2 (trans p1 m))
-> perform pm c ((trans p2 . trans p1) m)

dur ((trans p1 . trans p2) m)
-> dur (trans p1 (trans p2 m))
-> dur (trans p2 m)
-> dur m
-> dur (trans p1 m)
-> dur (trans p2 (trans p1 m))
-> dur ((trans p2 . trans p1) m)


    tempo r1 . trans p1 ≡ trans p1 . tempo r1

perform pm c ((tempo r1 . trans p1) m)
-> perform pm c (tempo r1 (trans p1 m))
-> perform pm (c{cDur= dt/r1}) (trans p1 m)
-> perform pm (c{cDur= dt/r1,cKey= k+p1}) m
-> perform pm (c{cKey= k+p1}) (tempo r1 m)
-> perform pm c (trans p1 (tempo r1 m))
-> perform pm c ((trans p1 . tempo r1) m)

dur ((tempo r1 . trans p1) m)
-> dur (tempo r1 (trans p1 m))
-> dur (trans p1 m) / r1
-> (dur m) / r1
-> dur (tempo r1 m)
-> dur (trans p1 (tempo r1 m))


Axiom 12.3.3 Tempo scaling and transposition are distributive over both
sequential and parallel composition. That is, for any r,p,m1 and m2...

    tempo r (m1 :+: m2) ≡ tempo r m1 :+: tempo r m2

perform pm c (tempo r (m1 :+: m2))
-> perform pm (c{cDur=dt/r}) (m1 :+: m2)
-> let c' = c{cTime = t + dur m1 * dt/r, cDur=(dt/r)}
   in perform pm (c{cDur=(dt/r)}) m1 ++ perform pm c' m2
-> perform pm (c{cDur=(dt/r)}) m1 ++ perform pm (c{cTime=t+dur m1*(dt/r)}) (tempo r m2)
-> perform pm c (tempo r m1) ++ perform pm (c{cTime=t+dur m1*(dt/r)}) (tempo r m2)
-? perform pm c (tempo r m1 :+: tempo r m2)

dur (tempo r (m1 :+: m2))
-> (dur (m1 :+: m2)) / r
-> (dur m1 + dur m2) / r
-> (dur m1) / r + (dur m2) / r
-> dur (tempo r m1) + dur (tempo r m2)
-> dur (tempo r m1 :+: tempo r m2)


    tempo r (m1 :=: m2) ≡ tempo r m1 :=: tempo r m2

perform pm c (tempo r (m1 :=: m2))
-> perform pm (c{cDur = dt/r}) (m1 :=: m2)
-> merge (perform pm (c{cDur = dt/r}) m1) 
         (perform pm (c{cDur = dt/r}) m2)
-> merge (perform pm c (tempo r m1)) 
         (perform pm c (tempo r m2))
-> perform pm c (tempo r m1 :=: tempo r m2)

dur (tempo r (m1 :=: m2))
-> (dur (m1 :=: m2)) / r
-> (max (dur m1) (dur m2)) / r
-> max (dur m1 / r) (dur m1 / r)
-> max (dur (tempo r m1)) (dur (tempo r m2))
-> dur (tempo r m1 :=: tempo r m2)


    trans p (m1 :+: m2) ≡ trans p m1 :+: trans p m2

perform pm c (trans p (m1 :+: m2))
-> perform pm (c{cKey=k+p}) (m1 :+: m2)
-> perform pm (c{cKey=k+p}) m1 ++ perform pm (c{cKey=k+p,cTime=t+dur m1 * dt}) m2
-> perform pm c (trans p m1) ++ perform pm (c{cTime=t+dur m1 * dt}) (trans p m2)
-> perform pm c (trans p m1 :+: trans p m2)

dur (trans p (m1 :+: m2))
-> dur (m1 :+: m2)
-> dur m1 + dur m2
-> dur (trans p m1) + dur (trans p m2)
-> dur (trans p m1 :+: trans p m2)


    trans p (m1 :=: m2) ≡ trans p m1 :=: trans p m2

perform pm c (trans p (m1 :=: m2))
-> perform pm (c{cKey=k+p}) (m1 :=: m2)
-> merge (perform pm (c{cKey=k+p}) m1)
         (perform pm (c{cKey=k+p}) m2)
-> merge (perform pm c (trans p m1))
         (perform pm c (trans p m2))
-> perform pm c (trans p m1 :=: trans p m2)

dur (trans p (m1 :=: m2))
-> dur (m1 :=: m2)
-> max (dur m1) (dur m2)
-> max (dur (trans p m1)) (dur (trans p m2))
-> dur (trans p m1 :=: trans p m2)


Axiom 12.3.4 Sequential and parallel composition are associative.
That is, for any m0,m1,m2...

    m0 :+: (m1 :+: m2) ≡ (m0 :+: m1) :+: m2

let
c' = c{cTime=t+dur m0 * dt}
c'' = c{cTime = t + (dur m0 * dt) + (dur m1 * dt)}
c''' = c{cTime = t + (dur m0 + dur m1) * dt}
c4 = c{cTime = t + dur (m0 :+: m1) * dt}

perform pm c (m0 :+: (m1 :+: m2))
-> perform pm c m0 ++ perform pm c' (m1 :+: m2)
-> perform pm c m0 ++ (perform pm c' m1 ++ perform pm c'' m2)
-> (perform pm c m0 ++ perform pm c' m1) ++ perform pm c'' m2
-> perform pm c (m0 :+: m1) ++ perform pm c''' m2
-> perform pm c (m0 :+: m1) ++ perform pm c4 m2
-> perform pm c ((m0 :+: m1) :+: m2)

dur (m0 :+: (m1 :+: m2))
-> dur m0 + dur (m1 :+: m2)
-> dur m0 + (dur m1 + dur m2)
-> (dur m0 + dur m1) + dur m2
-> dur (m0 :+: m1) + dur m2
-> dur ((m0 :+: m1) :+: m2)



    m0 :=: (m1 :=: m2) ≡ (m0 :=: m1) :=: m2 
    [Assuming m0,m1,m2 are ordered]

perform pm c (m0 :=: (m1 :=: m2))
-> merge (perform pm c m0)
         (perform pm c (m1 :=: m2))
-> merge (perform pm c m0) ((perform pm c m1) `merge` (perform pm c m2))

{LEMMA 1: merge is associative on ordered lists}
Prove xs `merge` (ys `merge` zs) = (xs `merge` ys) `merge` zs
Proof by Induction on zs...
Base Case
xs `merge` (ys `merge` [])
-> xs `merge` ys
-> (xs `merge` ys) `merge []
Induction Step
Assume xs `merge` (ys `merge` zs) = (xs `merge` ys) `merge` zs
Prove xs `merge` (ys `merge` (z:zs)) = (xs `merge` ys) `merge` (z:zs)
xs `merge` (ys `merge` (z:zs)) 
-> xs `merge` (ys `merge` (zs `merge` [z]))
-> xs `merge` ((ys `merge` zs) `merge` [z])
-> (xs `merge` (ys `merge` zs)) `merge` [z]
-> ((xs `merge` ys`) `merge` zs) `merge` [z]
-> (xs `merge` ys) `merge` (zs `merge` [z])
-> (xs `merge` ys) `merge` (z:zs)
{End Lemma 1}
{LEMMA 2: For all ordered non-empty lists, (x:xs) = xs `merge` [x]}
Proof by Calculation:
xs `merge` [x]
-> x : merge xs []
-> x : xs
{End Lemma 2}

-> merge ((perform pm c m0) `merge` (perform pm c m1)) (perform pm c m2)
-> merge (perform pm c (m0 :=: m1)) (perform pm c m2)
-> perform pm c ((m0 :=: m1) :=: m2)

dur (m0 :=: (m1 :=: m2))
-> (dur m0) `max` (dur (m1 :=: m2))
-> (dur m0) `max` ((dur m1) `max` (dur m2))
-> ((dur m0) `max` (dur m1)) `max` (dur m2)  [Assume max is associative]
-> (dur (m0 :=: m1)) `max` (dur m2)
-> dur ((m0 :=: m1) :=: m2)




Axiom 12.3.5 Parallel composition is commutative. That is, for any m0 and m1...

   m0 :=: m1 ≡ m1 :=: m0

perform pm c (m0 :=: m1)
-> merge (perform pm c m0)
         (perform pm c m1)

{LEMMA 1: merge is commutative on lists}
[Ordered lists not necessary because same comparisons would be made either way.]
Prove xs `merge` ys = ys `merge` xs
Proof by Induction on xs...
Base Case
[] `merge` ys
-> ys
-> ys `merge` []
Induction Step
Assume xs `merge` ys = ys `merge` xs
Prove (x:xs) `merge` ys = ys `merge` (x:xs)
(x:xs) `merge` ys
-> ([x] `merge` xs) `merge` ys
-> [x] `merge` (xs `merge` ys)
-> [x] `merge` (ys `merge` xs)
-> (ys `merge` xs) `merge` [x]
-> ys `merge` (xs `merge` [x])
-> ys `merge (x:xs)
{End Lemma 1}
{LEMMA 2: [y] `merge` xs = xs `merge` [y]}
Proof by Induction on xs...
Base Case
[y] `merge` []
-> [y]
-> [] `merge` [y]
Induction Step
Assume [y] `merge` xs = xs `merge` [y]
Prove [y] `merge` (x:xs) = (x:xs) `merge` [y]
[y] `merge` (x:xs)
-> if y < x then y : [] `merge` (x:xs)
            else x : [y] `merge` xs
-> if y < x then y : (x:xs)
            else x : [y] `merge` xs
-> if y < x then y : (x:xs) `merge []
            else x : [y] `merge` xs
-> if y < x then y : (x:xs) `merge []
            else x : xs `merge` [y]
-> if y > x then x : xs `merge` [y]
            else y : (x:xs) `merge []
-> if x < y then x : xs `merge` [y]
            else y : (x:xs) `merge []
-> (x:xs) `merge` [y]
{End Lemma 2}
                   
-> merge (perform pm c m1)
         (perform pm c m0)
-> perform pm c (m1 :=: m0)

dur (m0 :=: m1)
-> max (dur m0) (dur m1)
-> max (dur m1) (dur m0)
-> dur (m1 :=: m0)
{LEMMA: x `max` y = y `max` x}
Proof by Calculation
x `max` y
-> if x >= y then x
             else y
-> case x >= y of
     True  -> x
     False -> y
-> case compare x y /= LT of
     True  -> x
     False -> y
-> case compare x y of
     EQ -> x
     GT -> x
     LT -> y
-> case compare y x of
     EQ -> y
     GT -> y
     LT -> x
-> case compare y x /= LT of
     True  -> y
     False -> x
-> case y >= x of
     True  -> y
     False -> x
-> if y >= x then y
             else x
-> y `max` x
{End Lemma}




Axiom 12.3.6 rest 0 is a unit for tempo and trans, and a zero for sequential
and parallel composition. That is, for any r,p, and m...

    tempo r (rest 0) ≡ rest 0

perform pm c (tempo r (rest 0))
-> perform pm (c{cDur = dt/r}) (rest 0)
-> []
-> perform pm c (rest 0)

dur (tempo r (rest 0))
-> dur (rest 0) / r
-> 0 / r
-> 0
-> dur (rest 0)


    trans p (rest 0) ≡ rest 0

-> perform pm c (trans p (rest 0))
-> perform pm (c{cKey= k + p}) (rest 0)
-> perform pm c (rest 0)

dur (trans p (rest 0))
-> dur (rest 0)


    m :+: rest 0 ≡ m ≡ rest 0 :+: m
t = cTime c

perform pm c (m :+: rest 0)
-> perform pm c m ++ perform pm (c{cTime = t + dur m * dt}) (rest 0)
-> perform pm c m ++ []
-> perform pm c m
-> [] ++ perform pm c m
-> perform pm c (rest 0) ++ perform pm (c{cTime = t + dur (rest 0) * dt}) m
-> perform pm c (rest 0 :+: m)

dur (m :+: rest 0)
-> dur m + dur (rest 0)
-> dur m + 0
-> dur m
-> 0 + dur m
-> dur (rest 0) + dur m
-> dur (rest 0 :+: m)
    m :=: rest 0 ≡ m ≡ rest 0 :=: m

perform pm c (m :=: rest 0)
-> (perform pm c m) `merge` (perform pm c (rest 0))
-> (perform pm c m) `merge` []
-> perform pm c m
-> [] `merge` (perform pm c m)
-> (perform pm c (rest 0)) `merge` (perform pm c m)
-> perform pm c (rest 0 :=: m)

Assume dur >= 0
dur (m :=: rest 0)
-> max (dur m) (dur (rest 0))
-> dur m
-> max (dur (rest 0)) (dur m)
-> dur (rest 0 :=: m)




Axiom 12.3.7 A rest can be used to "pad" a parallel composition. That is, for
any m1 and m2 such that diff = dur m1 - dur m2 >= 0, and any d <= diff...

    m1 :=: m2 ≡ m1 :=: (m2 :+: rest d) 


perform pm c (m1 :=: m2)
-> (perform pm c m1) `merge` (perform pm c m2)
-> (perform pm c m1) `merge` (perform pm c m2 ++ [])
-> (perform pm c m1) `merge` (perform pm c m2 ++ perform pm c rest d)
-> (perform pm c m1) `merge` (perform pm c (m2 :+: rest d)
-> perform pm c (m1 :=: (m2 :+: rest d))

We are assuming dur m1 > dur m2
dur (m1 :=: m2)
-> max (dur m1) (dur m2)
-> max (dur m1) (dur m2 + (dur m1 - dur m2))
let 0 =< d <= dur m1 - dur m2
-> max (dur m1) (dur m2 + d)
-> max (dur m1) (dur m2 + dur (rest d))   [From the above we know it must be rest]
-> max (dur m1) (dur (m2 :+: rest d))
-> dur (m1 :=: (m2 :+: rest d))





Axiom 12.3.8 There is a duality between (:+:) and (:=:), namely that for
any m0,m1,m2,and m3 such that dur m0 = dur m2...

    (m0 :+: m1) :=: (m2 :+: m3) ≡ (m0 :=: m2) :+: (m1 :=: m3)

t  = cTime c
dt = cDur c
perform ((m0 :+: m1) :=: (m2 :+: m3))

-> (perform pm c (m0 :+: m1)) `merge` (perform pm c (m2 :+: m3))

-> (perform pm c m0 ++ perform pm (c{cTime = t + dur m0 * dt}) m1) 
   `merge` 
   (perform pm c m2 ++ perform pm (c{cTime = t + dur m2 * dt}) m3)

-> (perform pm (c{cTime = t}) m0 ++ perform pm (c{cTime = t + dur m0 * dt}) m1) 
   `merge` 
   (perform pm (c{cTime = t}) m2 ++ perform pm (c{cTime = t + dur m2 * dt}) m3)

let x = perform pm (c{cTime = t}) m0
    y = perform pm (c{cTime = t + dur m0 * dt}) m1
    u = perform pm (c{cTime = t}) m2
    v = perform pm (c{cTime = t + dur m2 * dt}) m3

-> (x `merge` y) `merge` (u `merge` v)
-> x `merge` (y `merge` (u `merge` v))
-> x `merge` ((y `merge` u) `merge` v)
-> x `merge` ((u `merge` y) `merge` v)
-> (x `merge` (u `merge` y)) `merge` v
-> ((x `merge` u) `merge` y) `merge` v
-> (x `merge` u) `merge` (y `merge` v)
-> (x `merge` u) `merge` (y `merge` v)

-> ((perform pm (c{cTime = t}) m0) `merge` (perform pm (c{cTime = t}) m2)) 
   `merge` 
   ((perform pm (c{cTime = t + dur m0 * dt}) m1) 
   `merge` (perform pm (c{cTime = t + dur m2 * dt}) m3))

-> ((perform pm (c{cTime = t}) m0) `merge` (perform pm (c{cTime = t}) m2)) 
   ++ 
   ((perform pm (c{cTime = t + dur (m0 :=: m2) * dt}) m1) 
   `merge`
   (perform pm (c{cTime = t + dur (m0 :=: m2) * dt}) m3))

-> perform pm c (m0 :=: m2) 
   ++ 
   perform pm (c{cTime = t + dur (m0 :=: m2) * dt}) (m1 :=: m3) 

-> perform pm c ((m0 :=: m2) :+: (m1 :=: m3))

{Lemma}
If for all x in xs and all y in ys, x < y
xs ++ ys = xs `merge` ys
Proof by Induction on xs...
Base Case
[] ++ ys
-> ys
-> [] `merge` ys
Induction Step
Assume xs ++ ys = xs `merge` ys
Prove (x:xs) ++ ys = (x:xs) `merge` ys
(x:xs) ++ ys
-> x : (xs ++ ys)
-> x : (xs `merge` ys)
-> (x:xs) `merge` ys
{End Lemma}

dur ((m0 :+: m1) :=: (m2 :+: m3))
-> max (dur (m0 :+: m1)) (dur (m2 :+: m3))
-> max (dur m0 + dur m1) (dur m2 + dur m3)
-> max (dur m0 + dur m1) (dur m0 + dur m3)
-> (dur m0) + max (dur m1) (dur m3)
-> max (dur m0) (dur m2) + max (dur m1) (dur m3)
-> dur (m0 :=: m2) + dur (m1 :=: m3)
-> dur ((m0 :=: m2) :+: (m1 :=: m3))


Justification for dur m0 = dur m2....
dur ((m0 :+: m1) :=: (m2 :+: m3))
= max (dur (m0 :+: m1)) (dur (m2 :+: m3))
= max (dur m0 + dur m1) (dur m2 + dur m3)
let dur m1 = dur m2
    dur m1 < dur m3 < m0
= dur m0 + dur m1 
< (max (dur m0) (dur m2)) + (max (dur m1) (dur m3))
= (dur (m0 :=: m2)) + (dur (m1 :=: m3))
= dur ((m0 :=: m2) :+: (m1 :=: m3))
-}


{-Exercise 12.3: Recall the polyphonic and contrapuntal melodies mel1 and mel2
 - from Chapter 1. Prove that mel1 ≡ mel2.

mel1
-> (ef 4 qn :=: c 4 qn) :+: (f 4 qn :=: d 4 qn) :+: (g 4 qn :=: e 4 qn)
-> ((ef 4 qn :+: f 4 qn) :=: (c 4 qn :+: d 4 qn)) :+: (g 4 qn :=: e 4 qn)
-> (ef 4 qn :+: f 4 qn :+: g 4 qn) :=: (c 4 qn :+: d 4 qn :+: e 4 qn)
-> mel2

-}




{-Exercise 12.4: Prove 
 -
 - timesM a m :+: timesM b m ≡ timesM (a + b) m 
 -

Proof by Induction on a
let t  = cTime c
    dt = cDur c
    rest 0 = Rest 0
Base Case
perform pm c (timesM 0 m :+: timesM b m)
-> perform pm c (rest 0 :+: timesM b m)
-> perform pm c (rest 0) 
   ++ perform pm (c{cTime = t + dur (rest 0) * dt}) (timesM b m)
-> [] ++ perform pm (c{cTime = t + dur (rest 0) * dt}) (timesM b m)
-> perform pm (c{cTime = t}) (timesM b m)
-> perform pm c (timesM (0+b) m)
Induction Step
Assume timesM a m :+: timesM b m ≡ timesM (a + b) m 
Prove timesM (a+1) m :+: timesM b m ≡ timesM ((a+1) + b) m 
perform pm c (timesM (a+1) m :+: timesM b m)
-> perform pm c (timesM (a+1) m) 
   ++ perform pm (c{cTime = t + dur (timesM (a+1) m) * dt}) (timesM b m)

-> perform pm c (m :+: timesM a m) 
   ++ perform pm (c{cTime = t + dur (timesM (a+1) m) * dt}) (timesM b m)

-> (perform pm c m ++ perform pm (c{cTime = t + dur m * dt}) (timesM a m))
   ++ perform pm (c{cTime = t + dur (timesM (a+1) m) * dt}) (timesM b m)

-> perform pm c m ++ (perform pm (c{cTime = t + dur m * dt}) (timesM a m)
   ++ perform pm (c{cTime = t + dur (timesM (a+1) m) * dt}) (timesM b m))

-> perform pm c m ++ (perform pm (c{cTime = t + dur m * dt}) (timesM a m)
   ++ perform pm (c{cTime = t + ((a+1) * dur m) * dt}) (timesM b m))

-> perform pm c m ++ (perform pm (c{cTime = t + dur m * dt}) (timesM a m)
   ++ perform pm (c{cTime = t + (dur m + a * dur m) * dt}) (timesM b m))

-> perform pm c m ++ (perform pm (c{cTime = t + dur m * dt}) (timesM a m)
   ++ perform pm (c{cTime = t + (dur m + dur (timesM a m)) * dt}) (timesM b m))

-> perform pm c m ++ (perform pm (c{cTime = t + dur m * dt}) (timesM a m)
   ++ perform pm (c{cTime = (t + dur m * dt) + dur (timesM a m) * dt}) (timesM b m))

-> perform pm c m ++ perform pm (c{cTime = t + dur m * dt}) (timesM a m :+: timesM b m)

-> perform pm c m ++ perform pm (c{cTime = t + dur m * dt}) (timesM (a+b) m)

-> perform pm c (m :+: timesM (a+b) m)

-> perform pm c (timesM ((a+b)+1) m)

-> perform pm c (timesM ((a+1)+b) m)


dur (timesM a m :+: timesM b m)
-> dur (timesM a m) + dur (timesM b m)
{LEMMA: dur (timesM n m) = n * dur m proved last chapter}
-> a * (dur m) + b * (dur m)
-> (a + b) * dur m
-> dur (timesM (a + b) m)

-}


{-Exercise 12.5: Prove as many of the axioms of Figure 12.1 as you can.

Properties of mMap

mMap (\x -> x) = \x -> x
let id = \x -> x
Prove mMap id m1 = id m1
Base Case
mMap id (Prim (Note d x))
-> Prim (pMap id (Note d x))
-> Prim (Note d (id x))
-> Prim (Note d x)
-> id (Prim (Note d x))
mMap id (Prim (Rest d))
-> Prim (pMap id (Rest d))
-> Prim (Rest d)
-> id (Prim (Rest d))
Induction Step
Assume mMap id m1 = id m1
Prove
mMap id (m1 :+: m2)
-> mMap id m1 :+: mMap id m2
-> id m1 :+: id m2
-> m1 :+: m2
-> id (m1 :+: m2)
mMap id (m1 :=: m2)
-> mMap id m1 :=: mMap id m2
-> id m1 :=: id m2
-> m1 :=: m2
-> id (m1 :=: m2)
mMap id (Modify c m1)
-> Modify c (mMap id m1)
-> Modify c m1
-> id (Modify c m1)


Prove mMap (f . g) m = (mMap f . mMap g) m
Proof by induction on m...
Base Cases
mMap (f . g) (Prim (Note d x))
-> Prim (pMap (f . g) (Note d x))
-> Prim (Note d ((f . g) x))
-> Prim (Note d (f(g x)))
-> Prim (pMap f (Note d (g x)))
-> mMap f (Prim (Note d (g x)))
-> mMap f (Prim (pMap g (Note d x)))
-> mMap f (mMap g (Prim (Note d x)))
-> (mMap f . mMap g) (Prim (Note d x))

mMap (f . g) (Prim (Rest d))
-> Prim (pMap (f . g) (Rest d))
-> Prim (Rest d)
-> Prim (pMap f (Rest d))
-> mMap f (Prim (Rest d))
-> mMap f (Prim (pMap g (Rest d)))
-> mMap f (mMap g (Prim (Rest d)))
-> (mMap f . mMap g) (Prim (Rest d))

Induction Step
Assume mMap (f . g) m = (mMap f . mMap g) m
mMap (f . g) (m1 :+: m2)
-> mMap (f . g) m1 :+: mMap (f . g) m2
-> (mMap f . mMap g) m1 :+: (mMap f . mMap g) m2
-> mMap f (mMap g m1) :+: mMap f (mMap g m2)
-> mMap f (mMap g m1 :+: mMap g m2)
-> mMap f (mMap g (m1 :+: m2))
-> (mMap f . mMap g) (m1 :+: m2)

mMap (f . g) (m1 :=: m2)
-> mMap (f . g) m1 :=: mMap (f . g) m2
-> (mMap f . mMap g) m1 :=: (mMap f . mMap g) m2
-> mMap f (mMap g m1) :=: mMap f (mMap g m2)
-> mMap f (mMap g m1 :=: mMap g m2)
-> mMap f (mMap g (m1 :=: m2))
-> (mMap f . mMap g) (m1 :=: m2)

mMap (f . g) (Modify c m)
-> Modify c (mMap (f . g) m)
-> Modify c ((mMap f . mMap g) m)
-> Modify c (mMap f (mMap g m))
-> mMap f (Modify c (mMap g m))
-> mMap f (mMap g (Modify c m))
-> (mMap f . mMap g) (Modify c m)


Prove mMap f . remove d $ m = remove d . mMap f $ m
Proof by Induction on m
Assume d < oldD
Base Cases
mMap f . remove d $ (Prim (Note oldD p))
-> mMap f (remove d (Prim (Note oldD p)))
-> mMap f (Note (oldD - d) p)
-> Note (oldD - d) (f p)
-> remove d (Note oldD (f p))
-> remove d (mMap f (Note oldD p))
-> (remove d . mMap f) (Note oldD p)

mMap f . remove d $ (Prim (Rest oldD))
-> mMap f (remove d (Prim (Rest oldD)))
-> mMap f (Rest (oldD - d))
-> Rest (oldD - d)
-> remove d (Rest oldD)
-> remove d (mMap f (Rest oldD))
-> (remove d . mMap f) (Rest oldD)

Induction Step
Assume (mMap f . remove d) m = (remove d . mMap f) m
(mMap f . remove d) (m1 :+: m2)
-> mMap f (remove d (m1 :+: m2))
-> mMap f (remove d m1 :+: remove (d - dur m1) m2)
-> mMap f (remove d m1) :+: mMap f (remove (d - dur m1) m2)
-> (mMap f . remove d) m1 :+: (mMap f . remove (d - dur m1)) m2
-> (remove d . mMap f) m1 :+: (remove (d - dur m1) . mMap f) m2
-> remove d (mMap f m1) :+: remove (d - dur m1) (mMap f m2)
-> remove d (mMap f m1 :+: mMap f m2)
-> remove d (mMap f (m1 :+: m2))
-> (remove d . mMap f) (m1 :+: m2)

(mMap f . remove d) (m1 :=: m2)
-> mMap f (remove d (m1 :=: m2))
-> mMap f (remove d m1 :=: remove d m2)
-> mMap f (remove d m1) :=: mMap f (remove d m2)
-> (mMap f . remove d) m1 :=: (mMap f . remove d) m2
-> (remove d . mMap f) m1 :=: (remove d . mMap f) m2
-> remove d (mMap f m1) :=: remove d (mMap f m2)
-> remove d (mMap f m1 :=: mMap f m2)
-> remove d (mMap f (m1 :=: m2))
-> (remove d . mMap f) (m1 :=: m2)

let tempo r m = Modify (Tempo r) m
(mMap f . remove d) (tempo r m)
-> mMap f (remove d (tempo r m))
-> mMap f (tempo r (remove (d*r) m))
-> tempo r (mMap f (remove (d*r) m))
-> tempo r ((mMap f . remove (d*r)) m)
-> tempo r ((remove (d*r) . mMap f) m)
-> tempo r (remove (d*r) (mMap f m))
-> remove d (tempo r (mMap f m))
-> remove d (mMap f (tempo r m))
-> (remove d . mMap f) (tempo r m)

(mMap f . remove d) (Modify c m)
-> mMap f (remove d (Modify c m))
-> mMap f (Modify c (remove d m))
-> Modify c (mMap f (remove d m))
-> Modify c ((mMap f . remove d) m)
-> Modify c ((remove d . mMap f) m)
-> Modify c (remove d (mMap f m))
-> remove d (Modify c (mMap f m))
-> remove d (mMap f (Modify c m))
-> (remove d . mMap f) (Modify c m)



Prove mMap f . cut d = cut d . mMap f
Proof by Induction
Assume 0 < d < oldD
Base Case
(mMap f . cut d) (Note oldD x)
-> mMap f (cut d (Note oldD x))
-> mMap f (Note (max (min oldD d) 0) x)
-> Note (max (min oldD d) 0) (f x)
-> cut d (Note oldD (f x))
-> cut d (mMap f (Note oldD x))
-> (cut d . mMap f) (Note oldD x)

(mMap f . cut d) (Rest oldD)
-> mMap f (cut d (Rest oldD))
-> mMap f (Rest (max (min oldD d) 0))
-> Rest (max (min oldD d) 0)
-> cut d (Rest oldD)
-> cut d (mMap f (Rest oldD))
-> (cut d . mMap f) (Rest oldD)

Induction Step
Assume (mMap f . cut d) m = (cut d . mMap f) m
(mMap f . cut d) (m1 :+: m2)
-> mMap f (cut d (m1 :+: m2))
-> mMap f (cut d m1 :+: cut (d - dur (cut d m1)) m2)
-> mMap f (cut d m1) :+: mMap f (cut (d - dur (cut d m1)) m2)
-> cut d (mMap f m1) :+: cut (d - dur (cut d m1)) (mMap f m2)
-> cut d (mMap f m1 :+: mMap f m2)
-> cut d (mMap f (m1 :+: m2))
-> (cut d . mMap f) (m1 :+: m2)

(mMap f . cut d) (m1 :=: m2)
-> mMap f (cut d (m1 :=: m2))
-> mMap f (cut d m1 :=: cut d m2)
-> mMap f (cut d m1) :=: mMap f (cut d m2)
-> (mMap f . cut d) m1 :=: (mMap f . cut d) m2
-> (cut d . mMap f) m1 :=: (cut d . mMap f) m2
-> cut d (mMap f m1) :=: cut d (mMap f m2)
-> cut d (mMap f m1 :=: mMap f m2)
-> cut d (mMap f (m1 :=: m2))
-> (cut d . mMap f) (m1 :=: m2)

let tempo r m = Modify (Tempo r) m
(mMap f . cut d) (tempo r m)
-> mMap f (cut d (tempo r m))
-> mMap f (tempo r (cut (d*r) m))
-> tempo r (mMap f (cut (d*r) m))
-> tempo r ((mMap f . cut (d*r)) m)
-> tempo r ((cut (d*r) . mMap f) m)
-> tempo r (cut (d*r) (mMap f m))
-> cut d (tempo r (mMap f m))
-> cut d (mMap f (tempo r m))
-> (cut d . mMap f) (tempo r m)

(mMap f . cut d) (Modify c m)
-> mMap f (cut d (Modify c m))
-> mMap f (Modify c (cut d m))
-> Modify c (mMap f (cut d m))
-> Modify c ((mMap f . cut d) m)
-> Modify c ((cut d . mMap f) m)
-> Modify c (cut d (mMap f m))
-> cut d (Modify c (mMap f m))
-> cut d (mMap f (Modify c m))
-> (cut d . mMap f) (Modify c m)




Properties of cut and remove
let (f . g) x         = f(g(x))
    (Prim (Note d p)) = note d p
    (Prim (Rest d))   = rest d

For all non-negative d1 and d2...
cut d1 . cut d2 = cut (min d1 d2)
Prove (cut d1 . cut d2) m = cut (min d1 d2) m

Induction on m...
Base Cases
olD > 0 && d2 > 0
cut d1 (cut d2 (note oldD p))
-> cut d1 (note (max (min oldD d2) 0) p)
-> note (max (min (max (min oldD d2) 0) d1) 0) p
-> note (max (max (min (min oldD d2) d1) 0) 0) p  [Lemma (1) below]
-> note (max (max (min oldD (min d2 d1)) 0) 0) p  [Associativity of min]
-> note (max (max (min oldD (min d1 d2)) 0) 0) p  [Commutativity of min]
-> note (max (min oldD (min d1 d2)) 0) p  [Lemma (2) below]
-> cut (min d1 d2) (note oldD p)
oldD = 0 || d2 = 0
cut d1 (cut d2 (note oldD p))
let d' = max (min oldD d2) 0
-> if d' > 0 then cut d1 note d' p else cut d1 (rest 0)
-> cut d1 (rest 0)
-> rest 0
let d'' = max (min oldD (min d1 d2)) 0
-> if d'' > 0 then note d'' p else cut d1 rest 0
-> cut (min d1 d2) (note oldD p)

cut d1 (cut d2 (rest oldD))
-> cut d1 (rest (max (min oldD d2) 0))
-> rest (max (min (max (min oldD d2) 0) d1) 0)
-> rest (max (max (min (min oldD d2) d1) 0) 0)  [Lemma (1) below]
-> rest (max (max (min oldD (min d2 d1)) 0) 0)  [Associativity of min]
-> rest (max (max (min oldD (min d1 d2)) 0) 0)  [Commutativity of min]
-> rest (max (min oldD (min d1 d2)) 0)          [Lemma (2) below]
-> cut (min d1 d2) (rest oldD)


Induction Step

cut d1 (cut d2 (m1 :=: m2))
-> cut d1 (cut d2 m1 :=: cut d2 m2)
-> cut d1 (cut d2 m1) :=: cut d1 (cut d2 m2)
-> cut (min d1 d2) m1 :=: cut (min d1 d2) m2
-> cut (min d1 d2) (m1 :=: m2)

cut d1 (cut d2 (m1 :+: m2))
-> cut d1 (cut d2 m1 :+: cut (d2 - dur (cut d2 m1)) m2) [defn dur]
-> cut d1 (cut d2 m1) 
   :+: cut (d1 - dur (cut d1 (cut d2 m1))) (cut (d2 - dur (cut d2 m1)) m2) [defn dur]
-> cut (min d1 d2) m1
   :+: cut (min (d1 - dur (cut (min d1 d2) m1)) (d2 - dur (cut d2 m1))) m2 [IH]
2 Cases...
d2 <= d1
-> cut (min d1 d2) m1
   :+: cut (min (d1 - dur (cut d2 m1)) (d2 - dur (cut d2 m1))) m2  [defn min]
-> cut (min d1 d2) m1
   :+: cut (min (d1 d2) - dur (cut d2 m1)) m2     [simplification]
-> cut (min d1 d2) m1
   :+: cut (min (d1 d2) - dur (cut (min d1 d2) m1)) m2   [fold min]
-> cut (min d1 d2) (m1 :+: m2)  [fold cut]
d2 > d1
-> cut (min d1 d2) m1
   :+: cut (min (d1 - dur (cut d1 m1)) (d2 - dur (cut d2 m1))) m2  [defn min]

   For all m1  
   (d1 - dur (cut d1 m1)) <= (d2 - dur (cut d2 m1)) 
   -- if dur m1 < d1 then 
   --    dur (cut d1 m1) = dur (cut d2 m1)
   -- if dur m1 >= d1 then 
   --    dur (cut d1 m1) = 0 <= dur (cut d2 m1)

-> cut (min d1 d2) m1
   :+: cut (d1 - dur (cut d1 m1)) m2
-> cut (min d1 d2) m1 
   :+: cut ((min d1 d2) - dur (cut (min d1 d2) m1)) m2
-> cut (min d1 d2) (m1 :+: m2)


cut d1 (cut d2 (tempo r m))
-> cut d1 (tempo r (cut (d2*r) m))
-> tempo r (cut (d1*r) (cut (d2*r) m))
-> tempo r (cut (min (d1*r) (d2*r)) m)
-> tempo r (cut ((min d1 d2)*r) m)
-> cut (min d1 d2) (tempo r m)

cut d1 (cut d2 (Modify c m))
-> cut d1 (Modify c (cut d2 m))
-> Modify c (cut d1 (cut d2 m))
-> Modify c (cut (min d1 d2) m)
-> cut (min d1 d2) (Modify c m)

{LEMMAS}
For all non-negative x and y...
(1)
Prove: min (max x 0) y = max (min x y) 0
Proof by Calculation
min (max x 0) y
-> min x y
-> max (min x y) 0
min y (max x 0) = max (min y x) 0  [in a more obviously "associative" form...]

(2)
Prove: max (max (x y) 0) 0 = max (x y) 0
Proof by Calculation
max (max (x y) 0) 0
-> max (x y) 0
{END Lemma}


Prove
For all non-negative d1 and d2
remove d1 . remove d2 = remove (d1 + d2)
Proof by Induction

If d2 = 0, remove d2 = id and 
remove d1 . remove d2 = remove d1 = remove (d1 + 0)
If d1 = 0, remove d1 = id and 
remove d1 . remove d2 = remove d2 = remove (0 + d2)
If d1,d2 = 0, remove d1 = id, remove d2 = id
remove d1 . remove d2 = id . id = id = remove 0 = remove (0 + 0)
Which makes what needs to be proved obviously true. 
Therefore we consider the non-trivial case,
where we assume d1,d2 > 0

Base Cases

remove d1 (remove d2 (note oldD p))
2 Cases
[1] oldD >= d2
remove d1 (note (max (oldD-d2) 0) p)
-> note (max (oldD - d2 - d1) 0) p
-> note (max (oldD - (d2 + d1)) 0) p
-> note (max (oldD - (d1 + d2)) 0) p
-> remove (d1 + d2) (note oldD p)
[2] oldD < d2
-> remove d1 (rest 0)
-> rest 0
-> remove (d1 + d2) (note oldD p)

remove d1 (remove d2 (rest oldD))
2 Cases
[1] oldD >= d2
remove d1 (remove d2 (rest oldD))
-> remove d1 (rest (max (oldD - d2) 0))
-> rest (max ((max (oldD - d2) 0) - d1) 0)
-> rest (max (max (oldD - d2 - d1) (-d1)) 0)
-> rest (max (oldD - (d2 + d1)) 0)
-> rest (max (oldD - (d1 + d2)) 0)
-> remove (d1 + d2) (rest oldD)
[2] oldD < d2
remove d1 (rest 0)
-> rest 0
-> rest (max (oldD - d2) 0)
-> rest (max (oldD - d1 - d2) 0)
-> rest (max (oldD - (d1 + d2)) 0)
-> remove (d1 + d2) (rest oldD)

Induction Step

remove d1 (remove d2 (m1 :=: m2))
-> remove d1 (remove d2 m1 :=: remove d2 m2)
-> remove d1 (remove d2 m1) :=: remove d1 (remove d2 m2)
-> remove (d1 + d2) m1 :=: remove (d1 + d2) m2
-> remove (d1 + d2) (m1 :=: m2)

remove d1 (remove d2 (m1 :+: m2))
-> remove d1 (remove d2 m1 :+: remove (d2 - dur m1) m2)
-> remove d1 (remove d2 m1) 
   :+: remove (d1 - dur (remove d2 m1)) (remove (d2 - dur m1) m2)
-> remove (d1 + d2) m1
   :+: remove (d1 - dur (remove d2 m1) + (d2 - dur m1)) m2
-> remove (d1 + d2) m1
   :+: remove (d1 + d2 - dur m1 - dur (remove d2 m1)) m2
-> remove (d1 + d2) m1
   :+: remove (((d1 + d2) -  dur m1) + (- dur (remove d2 m1))) m2
-> remove (d1 + d2) m1
   :+: remove ((d1 + d2) -  dur m1) (remove (- dur (remove d2 m1)) m2)
-> remove (d1 + d2) (m1 :+: (remove (- dur (remove d2 m1)) m2))
-> remove (d1 + d2) (m1 :+: m2)

remove d1 (remove d2 (tempo r m))
-> remove d1 (tempo r (remove (d2*r) m))
-> tempo r (remove (d1*r) (remove (d2*r) m))
-> tempo r (remove ((d1*r)+(d2*r)) m)
-> tempo r (remove ((d1+d2)*r) m)
-> remove (d1+d2) (tempo r m)

remove d1 (remove d2 (Modify c m))
-> remove d1 (Modify c (remove d2 m))
-> Modify c (remove d1 (remove d2 m))
-> Modify c (remove (d1+d2) m)
-> remove (d1 + d2) (Modify c m)



Lemma proved previously:
 min (max x 0) y = max (min x y) 0
 (x `max` 0) `min` y = (x `min` y) `max` 0

For all non-negative d1 and d2...
Prove: cut d1 . remove d2 = remove d1 . cut (d1 + d2) [From the book]
FALSE
Let d1 = qn
    d2 = hn
    m  = c 4 wn
(cut qn . remove hn) (c 4 wn) = c 4 qn
(remove qn . cut (qn+hn)) (c 4 wn) = c 4 hn

I think what they meant was the following, which makes more sense.
Prove: cut d1 . remove d2 = remove d2 . cut (d1 + d2)
Proof by Induction on m...
2 Base Cases
(1) (note oldD p)
oldD > d2 (*)
(cut d1 . remove d2) (note oldD p)
-> cut d1 (note ((oldD - d2) `max` 0) p)  (*)
-> note ((((oldD - d2) `max` 0) `min` d1) `max` 0) p
-> note ((((oldD - d2) `max` 0) `min` d1) `max` 0) p
-> note ((((oldD - d2) `min` d1) `max` 0) `max` 0) p
-> note ((((oldD `min` (d1 + d2)) - d2) `max` 0) `max` 0) p
-> note ((((oldD `min` (d1 + d2)) `max` 0) - d2) `max` 0) p (*)
-> remove d2 (note ((oldD `min` (d1 + d2)) `max` 0) p)
-> remove d2 (cut (d1 + d2) (note oldD p))
-> (remove d2 . cut (d1 + d2)) (note oldD p)
oldD <= d2 (*)
(cut d1 . remove d2) (note oldD p)
-> cut d1 (rest 0)  (*)
-> rest 0
-> remove d2 (note oldD p) (*)
-> remove d2 (cut (d1 + d2) note oldD p)  (*)
-> (remove d2 . cut (d1 + d2)) (note oldD p)


(2) (rest oldD)
oldD > d2 (*)
(cut d1 . remove d2) (rest oldD)
-> cut d1 (rest ((oldD - d2) `max` 0))
-> rest ((((oldD - d2) `max` 0) `min` d1) `max` 0)
-> rest ((((oldD - d2) `max` 0) `min` d1) `max` 0)
-> rest ((((oldD - d2) `min` d1) `max` 0) `max` 0)
-> rest ((((oldD `min` (d1 + d2)) - d2) `max` 0) `max` 0)
-> rest ((((oldD `min` (d1 + d2)) `max` 0) - d2) `max` 0)  (*)
-> remove d2 (note ((oldD `min` (d1 + d2)) `max` 0))
-> remove d2 (cut (d1 + d2) (note oldD))
-> (remove d2 . cut (d1 + d2)) (note oldD)
oldD <= d2 (*)
(cut d1 . remove d2) (rest oldD)
-> cut d1 (rest 0)  (*)
-> rest 0
-> remove d2 (rest oldD) (*)
-> remove d2 (cut (d1 + d2) rest oldD)  (*)
-> (remove d2 . cut (d1 + d2)) (rest oldD)

Induction Step
Assume cut d1 . remove d2 = remove d2 . cut (d1 + d2)

(cut d1 . remove d2) (m1 :=: m2)
-> cut d1 (remove d2 (m1 :=: m2))
-> cut d1 (remove d2 m1 :=: remove d2 m2)
-> cut d1 (remove d2 m1) :=: cut d1 (remove d2 m2)
-> remove d2 (cut (d1+d2) m1) :=: remove d2 (cut (d1+d2) m2)
-> remove d2 (cut (d1+d2) m1 :=: cut (d1+d2) m2)
-> remove d2 (cut (d1+d2) (m1 :=: m2))
-> (remove d2 . cut (d1+d2)) (m1 :=: m2)

(cut d1 . remove d2) (m1 :+: m2)
-> cut d1 (remove d2 (m1 :+: m2))
-> cut d1 (remove d2 m1 :+: remove (d2 - dur m1) m2)
-> cut d1 (remove d2 m1) 
   :+: cut (d1 - dur (cut d1 (remove d2 m1))) (remove (d2 - dur m1) m2)
-> remove d2 (cut (d1+d2) m1) 
ih :+: remove (d2 - dur m1) (cut (d1 - dur (cut d1 (remove d2 m1)) + (d2 - dur m1)) m2)
-> remove d2 (cut (d1+d2) m1) 
ih :+: remove (d2 - dur m1) (cut (d1 - dur (remove d2 (cut (d1+d2) m1)) + (d2 - dur m1)) m2)
-> remove d2 (cut (d1+d2) m1) 
   :+: remove (d2 - dur m1) (cut ((d1+d2) - dur (remove d2 (cut (d1+d2) m1)) - dur m1) m2)

if dur m1 <= d2
-> remove d2 m1
   :+: remove (d2 - dur m1) (cut ((d1+d2) - dur m1) m2)   [d2 >= m1 or d2 > m1]
-> remove d2 (m1 :+: cut ((d1+d2) - dur m1) m2)
-> remove d2 (cut (d1+d2) m1 :+: cut ((d1+d2) - dur (cut (d1+d2) m1)) m2)  [same]
-> remove d2 (cut (d1+d2) (m1 :+: m2))

if dur m1 > d2
   dur m1 > d1+d2
-> remove d2 (cut (d1+d2) m1) 
   :+: remove (d2 - dur m1) (cut ((d1+d2) - dur (remove d2 (cut (d1+d2) m1)) - dur m1) m2)
-> remove d2 (cut (d1+d2) m1)  [dur m1 >= d2]
   :+: (cut ((d1+d2) - dur (remove d2 (cut (d1+d2) m1)) - dur m1) m2)
-> remove d2 (cut (d1+d2) m1)  [dur m1 >= d2]
   :+: (cut ((d1+d2) - d1 - dur m1) m2)     [assume dur (remove d2 (cut (d1+d2) m1)) = d1]
-> remove d2 (cut (d1+d2) m1) 
   :+: (cut (d2 - dur m1) m2)
-> remove d2 (cut (d1+d2) m1) 
   :+: rest 0
-> remove d2 (cut (d1+d2) m1) 
   :+: remove (d2 - dur (cut (d1+d2) m1)) rest 0
-> remove d2 (cut (d1+d2) m1 :+: rest 0)
-> remove d2 (cut (d1+d2) m1 :+: cut ((d1+d2) - dur (cut (d1+d2) m1)) m2)  [d1+d2 < dur m1]
-> remove d2 (cut (d1+d2) (m1 :+: m2))

if dur m1 > d2 
   dur m1 <= d1+d2
-> remove d2 (cut (d1+d2) m1) 
   :+: remove (d2 - dur m1) (cut ((d1+d2) - dur (remove d2 (cut (d1+d2) m1)) - dur m1) m2)
-> remove d2 (cut (d1+d2) m1) 
   :+: remove (d2 - dur (cut (d1+d2) m1))   [d1+d2 >= dur m1]
         (cut ((d1+d2) - dur (remove d2 (cut (d1+d2) m1)) - dur m1) m2)
-> remove d2 ((cut (d1+d2) m1) 
   :+: cut ((d1+d2) - dur m1 - dur (remove d2 (cut (d1+d2) m1))) m2)
-> remove d2 ((cut (d1+d2) m1) [d1+d2 >= dur m1]
   :+: cut ((d1+d2) - dur (cut (d1+d2) m1) - dur (remove d2 (cut (d1+d2) m1))) m2)
-> remove d2 ((cut (d1+d2) m1) 
   :+: cut ((d1+d2) - dur (cut (d1+d2) m1) + (- dur (remove d2 (cut (d1+d2) m1)))) m2)
-> remove d2 ((cut (d1+d2) m1) 
   :+: remove (- dur (remove d2 (cut (d1+d2) m1)))
         cut ((d1+d2) - dur (cut (d1+d2) m1) + (- dur (remove d2 (cut (d1+d2) m1)))) m2)
-> remove d2 ((cut (d1+d2) m1) 
   :+: cut ((d1+d2) - dur (cut (d1+d2) m1)) 
         (remove (- dur (remove d2 (cut (d1+d2) m1))) m2)
-> remove d2 ((cut (d1+d2) m1) :+: cut ((d1+d2) - dur (cut (d1+d2) m1)) m2)
-> remove d2 (cut (d1+d2) (m1 :+: m2))


(cut d1 . remove d2) (tempo r m1)
-> cut d1 (remove d2 (tempo r m1))
-> cut d1 (tempo r (remove (d2*r) m1))
-> tempo r (cut (d1*r) (remove (d2*r) m1))
-> tempo r (remove (d2*r) (cut (d1*r)+(d2*r) m1))
-> remove d2 (tempo r (cut (d1*r)+(d2*r) m1))
-> remove d2 (tempo r (cut ((d1+d2)*r) m1))
-> remove d2 (cut (d1+d2) (tempo r m1))
-> (remove d2 . cut (d1+d2)) (tempo r m1))

(cut d1 . remove d2) (Modify c m1)
-> cut d1 (remove d2 (Modify c m1))
-> cut d1 (Modify c (remove d2 m1))
-> Modify c (cut d1 (remove d2 m1))
-> Modify c (remove d2 (cut (d1+d2) m1))
-> remove d2 (Modify c (cut (d1+d2) m1))
-> remove d2 (cut (d1+d2) (Modify c m1))
-> (remove d2 . cut (d1+d2)) (Modify c m1))








For all non-negative d1 and d2 such that d2 >= d1...
Prove: remove d1 . cut d2 = cut (d2 - d1) . remove d1
Proof by Structural Induction...

Base Case
Note
(1)  If oldD = 0
remove d1 (cut d2 (note oldD p))
let d' = max (min (oldD d2)) 0
       = max 0 0
-> remove d1 (if d' > 0 then note d' p else rest 0)
-> remove d1 (rest 0)
-> rest 0
-> cut (d2 - d1) (rest 0)
-> cut (d2 - d1) (remove d1 (note 0 p))
-> cut (d2 - d1) (remove d1 (note oldD p))

(2a) If d2 = 0 (in which case -> d1 = 0)
remove d1 (cut d2 (note oldD p))
let d' = max (min (oldD d2)) 0
       = max 0 0
-> remove d1 (if d' > 0 then note d' p else rest 0)
-> remove d1 (rest 0)
-> rest 0
-> cut (d2 - d1) (rest 0)
-> cut (d2 - d1) (remove d1 (note 0 p))
-> cut (d2 - d1) (remove d1 (note oldD p))

(3a) If d2 > 0 && oldD < d1
remove d1 (cut d2 (note oldD p))
-> remove d1 (note ((oldD `min` d2) `max` 0) p)
-> remove d1 (note (oldD `max` 0) p)
-> remove d1 (note oldD p)
-> rest 0
-> cut (d2 - d1) (rest 0)
-> cut (d2 - d1) (remove d1 (note oldD p))

(3b) If d2 > 0 && oldD >= d1
remove d1 (cut d2 (note oldD p))
-> remove d1 (note ((oldD `min` d2) `max` 0) p)
-> note ((((oldD `min` d2) `max` 0) - d1) `max` 0) p
-> note ((((oldD-d1) `min` (d2-d1)) `max` 0) `max` 0) p
-> note ((((oldD-d1) `max` 0) `min` ((d2-d1) `max` 0))`max` 0) p
-> note ((((oldD-d1) `max` 0) `min` (d2-d1)) `max` 0) p
-> cut (d2-d1) (note ((oldD-d1) `max` 0) p)
-> cut (d2-d1) (remove d1 (note oldD p))


Rest
if oldD >= d1
remove d1 (cut d2 (rest oldD))
-> remove d1 (rest ((oldD `min` d2) `max` 0))
-> rest ((((oldD `min` d2) `max` 0) - d1) `max` 0)
-> rest ((((oldD `min` d2) - d1) `max` (-d1)) `max` 0)
-> rest (((oldD-d1) `min` (d2-d1)) `max` 0)              [oldD >= d1]
-> rest ((((oldD-d1) `max` 0) `min` (d2-d1)) `max` 0)
-> cut (d2-d1) (rest ((oldD-d1) `max` 0) `max` 0)
-> cut (d2-d1) (remove d1 (rest oldD))
if oldD < d1
cut (d2-d1) (remove d1 (rest oldD))
-> cut (d2-d1) (rest 0)
-> rest 0
-> remove d1 (rest oldD)
-> remove d1 (cut d2 (rest oldD))    [cut d2 (rest oldD) = rest oldD since d2 > oldD]


Induction Step

remove d1 (cut d2 (m1 :=: m2))
-> remove d1 (cut d2 m1 :=: cut d2 m2)
-> remove d1 (cut d2 m1) :=: remove d1 (cut d2 m2)
-> cut (d2 - d1) (remove d1 m1) :=: cut (d2 - d1) (remove d1 m2)
-> cut (d2 - d1) (remove d1 m1 :=: remove d1 m2)
-> cut (d2 - d1) (remove d1 (m1 :=: m2))


remove d1 (cut d2 (m1 :+: m2))
-> remove d1 (cut d2 m1 :+: cut (d2 - dur (cut d2 m1)) m2     {unfold cut}
-> remove d1 (cut d2 m1) 
   :+: remove (d1 - dur (cut d2 m1)) (cut (d2 - dur (cut d2 m1)) m2)   {unfold remove}

if d1 >= dur m1                [[to keep (d1-dur(cut d2 m1)) >=0]]
-> remove d1 (cut d2 m1)  {copy}
   :+: remove (d1 - dur (cut d2 m1)) (cut (d2 - dur (cut d2 m1)) m2)
-> cut (d2-d1) (remove d1 m1)    {ih}
   :+: cut ((d2 - dur (cut d2 m1)) - (d1 - dur (cut d2 m1)))
         (remove (d1 - dur (cut d2 m1)) m2)
-> cut (d2-d1) (remove d1 m1)   {remove parentheses}
   :+: cut (d2 - dur (cut d2 m1) - d1 + dur (cut d2 m1))
         (remove (d1 - dur (cut d2 m1)) m2)
-> cut (d2-d1) (remove d1 m1)    {simplify by grouping}
   :+: cut ((d2-d1) - dur (cut d2 m1) + dur (cut d2 m1))
         (remove (d1 - dur (cut d2 m1)) m2)
-> cut (d2-d1) (remove d1 m1)   {simplify}
   :+: cut (d2-d1)
         (remove (d1 - dur (cut d2 m1)) m2)
-> cut (d2-d1) (remove d1 m1)   {add zero}
   :+: cut ((d2-d1) - dur (cut (d1-d2) (rest 0)))
         (remove (d1 - dur (cut d2 m1)) m2)
-> cut (d2-d1) (remove d1 m1)    {manipulate zero assuming d1 >= m1}
   :+: cut ((d2-d1) - dur (cut (d1-d2) (remove d1 m1)))
         (remove (d1 - dur (cut d2 m1)) m2)
-> cut (d2-d1) ((remove d1 m1) :+: remove (d1 - dur (cut d2 m1)) m2) {fold cut}
-> cut (d2-d1) ((remove d1 m1) :+: remove (d1 - dur m1) m2)  {substitue assuming d2 > dur m1}
-> cut (d2-d1) (remove d1 (m1 :+: m2))  {fold remove}

if d1 < dur m1    [[cannot apply ih to term after :+: because d1<dur m1 --> "d1" < 0]]
-> remove d1 (cut d2 m1)  {copy}
   :+: remove (d1 - dur (cut d2 m1)) (cut (d2 - dur (cut d2 m1)) m2)
-> remove d1 (cut d2 m1)               {unfold remove; zeroes out}
   :+: cut (d2 - dur (cut d2 m1)) m2

   if dur m1 >= d2
   -> remove d1 (cut d2 m1) {copy}
      :+: cut (d2 - dur (cut d2 m1)) m2
   -> remove d1 (cut d2 m1) :+: rest 0  {unfold cut; zero out}
   -> cut (d2-d1) (remove d1 m1) :+: rest 0  {ih}
   -> cut (d2-d1) (remove d1 m1)  {add zero}
      :+: cut ((d2-d1) - dur (cut (d2-d1) (remove d1 m1))) m2
   -> cut (d2-d1) (remove d1 m1 :+: m2) {fold cut}
   -> cut (d2-d1) (remove d1 m1 :+: remove (d1 - dur m1) m2)    {add identity}
   -> cut (d2-d1) remove d1 (m1 :+: m2)  {fold remove}

   if dur m1 < d2
   -> remove d1 (cut d2 m1)               {copy}
      :+: cut (d2 - dur (cut d2 m1)) m2
   -> cut (d2-d1) (remove d1 m1)          {ih}
      :+: cut (d2 - dur (cut d2 m1)) m2
   -> cut (d2-d1) (remove d1 m1)          {add/unfold identity}
      :+: remove (dur m1 - dur (cut d2 m1)) 
            (cut (d2 - dur (cut d2 m1)) m2)
   -> cut (d2-d1) (remove d1 m1)           {manipulation assuming d1+dur(remove d1 m1)=dur m1}
      :+: remove ((d1 + dur (remove d1 m1)) - dur (cut d2 m1)) 
            (cut (d2 - dur (cut d2 m1)) m2)
   -> cut (d2-d1) (remove d1 m1)           {manipulation assuming (cut d2 m1)=dur m1}
      :+: remove ((d1 + dur (remove d1 (cut d2 m1))) - dur (cut d2 m1)) 
            (cut (d2 - dur (cut d2 m1)) m2)
   -> cut (d2-d1) (remove d1 m1)     {ih}
      :+: remove ((d1 + dur (cut (d2-d1) (remove d1 m1))) - dur (cut d2 m1)) 
            (cut (d2 - dur (cut d2 m1)) m2)
   -> cut (d2-d1) (remove d1 m1) 
      :+:   {ih}
      cut ((d2 - dur (cut d2 m1))-((d1 + dur (cut (d2-d1) (remove d1 m1)))-dur (cut d2 m1)))
            (remove ((d1 + dur (cut (d2-d1) (remove d1 m1))) - dur (cut d2 m1)) m2) 
   -> cut (d2-d1) (remove d1 m1)   {simplify parentheses in cut}
      :+: cut (d2 - dur (cut d2 m1) - d1 - dur (cut (d2-d1) (remove d1 m1)) + dur (cut d2 m1))
            (remove ((d1 + dur (cut (d2-d1) (remove d1 m1))) - dur (cut d2 m1)) m2) 
   -> cut (d2-d1) (remove d1 m1)   {further simplify cut}
      :+: cut ((d2-d1) - dur (cut (d2-d1) (remove d1 m1)))
            (remove ((d1 + dur (cut (d2-d1) (remove d1 m1))) - dur (cut d2 m1)) m2) 
   -> cut (d2-d1) (remove d1 m1  {fold cut}
      :+: remove ((d1 + dur (cut (d2-d1) (remove d1 m1))) - dur (cut d2 m1)) m2)
   -> cut (d2-d1) (remove d1 m1           {substitute dur (cut d2 m1) = dur m1}
      :+: remove (d1 + dur (cut (d2-d1) (remove d1 m1)) - dur m1) m2)
   -> cut (d2-d1) (remove d1 m1   {invoke property of dur}
      :+: remove (d1 + (min (d2-d1) (dur (remove d1 m1))) - dur m1) m2)
   -> cut (d2-d1) (remove d1 m1    {invoke property of dur}
      :+: remove (d1 + (min (d2-d1) (max 0 (dur m1 - d1))) - dur m1) m2)
   -> cut (d2-d1) (remove d1 m1    {unfold max}
      :+: remove (d1 + (min (d2-d1) (dur m1 - d1)) - dur m1) m2)
   -> cut (d2-d1) (remove d1 m1  {unfold min}
      :+: remove (d1 + dur m1 - d1 - dur m1) m2)
   -> cut (d2-d1) (remove d1 m1 :+: m2)   {unfold remove = id}
   -> cut (d2-d1) (remove d1 m1 :+: (remove (d1 - dur m1) m2))  {add id}
   -> cut (d2-d1) (remove d1 (m1 :+: m2)) {fold remove}


remove d1 (cut d2 (tempo r m))
-> remove d1 (tempo r (cut (d2*r) m))
-> tempo r (remove (d1*r) (cut (d2*r) m))
-> tempo r (cut ((d2*r)-(d1*r)) (remove (d1*r) m))
-> tempo r (cut ((d2-d1)*r) (remove (d1*r) m))
-> cut (d2-d1) (tempo r (remove (d1*r) m))
-> cut (d2-d1) (remove d1 (tempo r m))

remove d1 (cut d2 (Modify c m))
-> remove d1 (Modify c (cut d2 m))
-> Modify c (remove d1 (cut d2 m))
-> Modify c (cut (d2-d1) (remove d1 m))
-> cut (d2-d1) (Modify c (remove d1 m))
-> cut (d2-d1) (remove d1 (Modify c m))






Properties of retro
I DO NOT have to go through every Modify pattern in perform because 
we are just using it as a tool to establish the "musical equivalence" of
two expressions. I just need to go through all the patterns in the definitions
of the functions involved. (I am writing this one proof too late, but oh well.)

Definitions
dt = cDur c
k = cKey c
i = cInst c
pas = []

For all finite-duration m...
Prove: retro (retro m) ≡ m
Proof by Induction on m

Base Case
perform pm c (retro (retro (Prim n)))
-> perform pm c (retro (Prim n))
-> perform pm c (Prim n)

dur (retro (retro (Prim n)))
-> dur (retro (Prim n))
-> dur (Prim n)


Induction Step

perform pm c (retro (retro (tempo r m1)))
-> perform pm c (retro (tempo r (retro m1)))
-> perform pm c (tempo r (retro (retro m1)))
-> perform pm (c{cDur=dt/r}) (retro (retro m1))
-> perform pm (c{cDur=dt/r}) m1
-> perform pm c (tempo r m1)

dur (retro (retro (tempo r m1)))
-> dur (retro (tempo r m1))
-> dur (tempo r m1)


perform pm c (retro (retro (transpose p m1)))
-> perform pm c (retro (transpose p (retro m1)))
-> perform pm c (transpose p (retro (retro m1)))
-> perform pm (c{cKey=k+p}) (retro (retro m1))
-> perform pm (c{cKey=k+p}) m1
-> perform pm c (transpose p m1)

perform pm c (retro (retro (instrument i m1)))
-> perform pm c (instrument i (retro (retro m1)))
-> perform pm (c{cInst=i}) (retro (retro m1))
-> perform pm (c{cInst=i}) m1
-> perform pm c (instrument i m1)

perform pm c (retro (retro (player pn m1)))
-> perform pm c (player pn (retro (retro m1)))
-> perform pm (c{cPlayer=pm pn}) (retro (retro m1))
-> perform pm (c{cPlayer=pm pn}) m1
-> perform pm c (player pn m1)

perform pm c (retro (retro (phrase pas m1)))
-> perform pm c (phrase pas (retro (retro m1)))
-> fst (interpPhrase pl pm c pas (retro (retro m1)))
-> perform pm c (retro (retro m1))
-> perform pm c m1
-> fst (interpPhrase pl pm c pas m1)
-> perform pm c (phrase pas m1)

dur (retro (retro (Modify c m1)))
-> dur (Modify c (retro (retro m1)))
-> dur (retro (retro m1))


perform pm c (retro (retro (m1 :+: m2)))
-> perform pm c (retro (retro m2 :+: retro m1))
-> perform pm c (retro (retro m1) :+: retro (retro m2))
let c' = c{cTime=t + dur (retro (retro m1))*dt}
-> perform pm c (retro (retro m1)) ++ perform pm c' (retro (retro m2))
ih --> c' = c{cTime=t + dur m1 * dt}
-> perform pm c m1 ++ perform pm c' m2
-> perform pm c (m1 :+: m2)

dur (retro (retro (m1 :+: m2)))
-> dur (retro (retro m2 :+: retro m1))
-> dur (retro (retro m1) :+: retro (retro m2))
-> dur (retro (retro m1)) + dur (retro (retro m2))
-> dur m1 + dur m2
-> dur (m1 :+: m2)


perform pm c (retro (retro (m1 :=: m2)))
let d1 = dur m1
    d2 = dur m2
if d1 > d2 [the proof for d1 <= d2 is very similar]
-> perform pm c (retro (retro m1 :=: (rest (d1-d2) :+: retro m2)))
-> perform pm c ((rest 0 :+: retro (retro m1)) :=: retro (rest (d1-d2) :+: retro m2))
-> (perform pm c (rest 0 :+: retro (retro m1))) `merge` (retro (rest (d1-d2) :+: retro m2))
perform pm c (rest 0) --> c' = c
-> (perform pm c (rest 0) ++ perform pm c (retro (retro m1))) 
   `merge` perform pm c (retro (rest (d1-d2) :+: retro m2))
-> ([] ++ perform pm c (retro (retro m1))) 
   `merge` perform pm c (retro (rest (d1-d2) :+: retro m2))
-> perform pm c (retro (retro m1))
   `merge` perform pm c (retro (rest (d1-d2) :+: retro m2))
-> perform pm c (retro (retro m1))
   `merge` perform pm c (retro (retro m2) :+: retro (rest (d1-d2)))
-> perform pm c (retro (retro m1))
   `merge` (perform pm c (retro (retro m2)) ++ perform pm c (retro (rest (d1-d2))))
-> perform pm c (retro (retro m1))
   `merge` (perform pm c (retro (retro m2)) ++ perform pm c (rest (d1-d2)))
-> perform pm c (retro (retro m1))
   `merge` (perform pm c (retro (retro m2)) ++ [])
-> perform pm c (retro (retro m1))
   `merge` perform pm c (retro (retro m2))
-> perform pm c m1
   `merge` perform pm c m2
-> perform pm c (m1 :=: m2)

dur (retro (retro (m1 :=: m2)))
let d1 = dur m1
    d2 = dur m2
if d1 > d2 [again, proof is similar when d1 <= d2]
-> dur ((rest 0 :+: retro (retro m1)) :=: (retro (retro m2) :+: retro (rest (d1-d2))))
-> dur (rest 0 :+: retro (retro m1)) `max` dur (retro (retro m2) :+: retro (rest (d1-d2)))
-> (dur (rest 0) + dur (retro (retro m1))) `max` (dur (retro (retro m2) + dur (rest (d1-d2))))
-> dur (retro (retro m1)) `max` (dur (retro (retro m2)) + (d1-d2))
-> dur m1 `max` (dur m2 + (d1-d2))
-> dur m1
-> dur (m1 :=: m2)



Prove: retro (cut d m) ≡ remove (dur m - d) (retro m)
Proof by structural induction on m...

Base Case
perform pm c (retro (cut d (note oldD p)))
if oldD == 0
-> perform pm c (retro (rest 0))
-> perform pm c (rest 0)
-> perform pm c (remove (oldD - d) (note oldD p))
-> perform pm c (remove (oldD - d) (retro (note oldD p)))
if d == 0
-> perform pm c (retro (rest 0))
-> perform pm c (rest 0)
-> perform pm c (remove oldD (note oldD p))
-> perform pm c (remove (oldD-d) (note oldD p))
-> perform pm c (remove (oldD - d) (retro (note oldD p)))

if oldD <= d
-> perform pm c (retro (note oldD p))
-> perform pm c (note oldD p)
-> perform pm c (remove (oldD - d) (note oldD p))
-> perform pm c (remove (oldD - d) (retro (note oldD p)))
if oldD > d
-> perform pm c (retro (note ((oldD `min` d) `max` 0) p))
-> perform pm c (note ((oldD `min` d) `max` 0) p)
-> perform pm c (note (d `max` 0) p)
-> perform pm c (note ((oldD - oldD + d) `max` 0) p)
-> perform pm c (note ((oldD - (oldD - d)) `max` 0) p)
-> perform pm c (remove (oldD - d) (note oldD p))
-> perform pm c (remove (oldD - d) (retro (note oldD p)))

dur (retro (cut d (note oldD p)))
-> dur (cut d (note oldD p))
if oldD > d
-> min d oldD
-> d
-> d `max` 0
-> (oldD - oldD + d) `max` 0
-> (oldD - (oldD - d)) `max` 0
-> dur (remove (oldD - d) (note oldD p))
-> dur (remove (oldD - d) (retro (note oldD p)))
if oldD <= d
-> dur (cut d (note oldD p))
-> dur (note oldD p)
-> dur (remove (oldD - d) (note oldD p))
-> dur (remove (oldD - d) (retro (note oldD p)))
[I think this accounts for the case where d==0 and oldD==0]

perform pm c (retro (cut d (rest oldD)))
if oldD <= d
-> perform pm c (retro (rest oldD))
-> perform pm c (rest oldD)
-> perform pm c (remove (oldD - d) (rest oldD))
-> perform pm c (remove (oldD - d) (retro (rest oldD)))
if oldD > d
-> perform pm c (retro (rest ((oldD `min` d) `max` 0)))
-> perform pm c (rest ((oldD `min` d) `max` 0))
-> perform pm c (rest (d `max` 0))
-> perform pm c (rest ((oldD - oldD + d) `max` 0))
-> perform pm c (rest ((oldD - (oldD - d)) `max` 0))
-> perform pm c (remove (oldD - d) (rest oldD))
-> perform pm c (remove (oldD - d) (retro (rest oldD)))

dur (retro (cut d (rest oldD)))
-> dur (cut d (rest oldD))
if oldD > d
-> min d oldD
-> d
-> d `max` 0
-> (oldD - oldD + d) `max` 0
-> (oldD - (oldD - d)) `max` 0
-> dur (remove (oldD - d) (rest oldD))
-> dur (remove (oldD - d) (retro (rest oldD)))
if oldD <= d
-> dur (cut d (rest oldD))
-> dur (rest oldD)
-> dur (remove (oldD - d) (rest oldD))
-> dur (remove (oldD - d) (retro (rest oldD)))

Induction Step


perform pm c (retro (cut d (m1 :+: m2)))
-> perform pm c (retro (cut d m1 :+: cut (d - dur (cut d m1)) m2))
-> perform pm c (retro (cut (d - dur (cut d m1)) m2) :+: retro (cut d m1))
-> perform pm c (remove (dur m2 - (d - dur (cut d m1))) (retro m2) 
   :+: remove (dur m1 - d) (retro m1))

if d >= dur m1
-> perform pm c (remove (dur m2 - (d - dur (cut d m1))) (retro m2) 
   :+: remove (dur m1 - d) (retro m1))
-> perform pm c (remove (dur m2 - (d - dur (cut d m1))) (retro m2) :+: retro m1)
-> perform pm c (remove (dur m2 - (d - dur m1)) (retro m2) :+: retro m1)
-> perform pm c (remove (dur m2 - d + dur m1) (retro m2) :+: retro m1)
-> perform pm c (remove ((dur m1 + dur m2) - d) (retro m2) :+: retro m1)
-> perform pm c (remove ((dur m1 + dur m2) - d) (retro m2) 
   :+: remove (((dur m1 + dur m2) - d) - dur (retro m2)) (retro m1))
-> perform pm c (remove (dur (m1 :+: m2) - d) (retro m2) 
   :+: remove ((dur (m1 :+: m2) - d) - dur (retro m2)) (retro m1))
-> perform pm c (remove (dur (m1 :+: m2) - d) (retro m2 :+: retro m1)
-> perform pm c (remove (dur (m1 :+: m2) - d) (retro (m1 :+: m2))

if d < dur m1
-> perform pm c (remove (dur m2 - (d - dur (cut d m1))) (retro m2) 
   :+: remove (dur m1 - d) (retro m1))
-> perform pm c (remove (dur m2) (retro m2) 
   :+: remove (dur m1 - d) (retro m1))
-> perform pm c (rest 0 :+: remove (dur m1 - d) (retro m1))
-> ((rest 0) ++ perform pm c (remove (dur m1 - d) (retro m1)))
-> ([] ++ perform pm c (remove (dur m1 - d) (retro m1)))
-> perform pm c (remove (dur m1 - d) (retro m1))
-> perform pm c (remove (dur (m1 :+: m2) - d) (retro m2) 
   :+: remove (dur m1 - d) (retro m1))
-> perform pm c (remove (dur (m1 :+: m2) - d) (retro m2) 
   :+: remove ((dur m1 - d) + dur m2 - dur (retro m2)) (retro m1))
-> perform pm c (remove (dur (m1 :+: m2) - d) (retro m2) 
   :+: remove ((dur m1 + dur m2) - d - dur (retro m2)) (retro m1))
-> perform pm c (remove (dur (m1 :+: m2) - d) (retro m2) 
   :+: remove ((dur (m1 :+: m2) - d) - dur (retro m2)) (retro m1))
-> perform pm c (remove (dur (m1 :+: m2) - d) (retro m2 :+: retro m1))
-> perform pm c (remove (dur (m1 :+: m2) - d) (retro (m1 :+: m2)))

dur (retro (cut d (m1 :+: m2)))
-> dur (retro (cut d m1 :+: cut (d - (cut d m1)) m2))
-> dur (retro (cut (d - (cut d m1)) m2) :+: retro (cut d m1))
if dur m1 >= d
-> dur (rest 0 :+: retro (cut d m1))
-> dur (rest 0 :+: remove (dur m1 - d) (retro m1))
-> dur (remove (dur m1 + dur m2 - d) (retro m2) :+: remove (dur m1 - d) (retro m1))
-> dur (remove ((dur m1 + dur m2) - d) (retro m2)
   :+: remove ((dur m1 + dur m2) - d - dur m2) (retro m1))
-> dur (remove (dur (m1 :+: m2) - d) (retro m2) 
   :+: remove (dur (m1 :+: m2) - d - dur m2) (retro m1))
-> dur (remove (dur (m1 :+: m2) - d) (retro m2 :+: retro m1))
-> dur (remove (dur (m1 :+: m2) - d) (retro (m1 :+: m2)))
if dur m1 < d
-> dur (retro (cut (d - (cut d m1)) m2) :+: retro (cut d m1))
-> dur (remove (dur m2 - (d - (cut d m1))) (retro m2) :+: retro m1)
-> dur (remove (dur m2 - d + dur m1) (retro m2) :+: retro m1)
-> dur (remove ((dur m1 + dur m2) - d) (retro m2) :+: retro m1)
-> dur (remove ((dur m1 + dur m2) - d) (retro m2) 
        :+: remove ((dur m1 + dur m2) - d - dur (retro m2)) (retro m1))
-> dur (remove ((dur m1 + dur m2) - d) (retro m2 :+: retro m1))
-> dur (remove (dur (m1 :+: m2) - d) (retro m2 :+: retro m1))
-> dur (remove (dur (m1 :+: m2) - d) (retro (m1 :+: m2)))



perform pm c (retro (cut d (m1 :=: m2)))
let cd1 = dur (cut d m1), cd2 = dur (cut d m2)
-> perform pm c (retro (cut d m1 :=: cut d m2))
[assume cd1 > cd2, proof follows similarly for the other case]
-> perform pm c (retro (cut d m1) :=: (rest (cd1 - cd2) :+: retro (cut d m2)))
-> perform pm c (retro (cut d m1)) 
   `merge` perform pm c (rest (cd1 - cd2) :+: retro (cut d m2))
[t = cTime c, dt = cDur c]
[c' = c {cTime = t + dur (rest (cd1-cd2))* dt}]
-> perform pm c (retro (cut d m1)) 
   `merge` (perform pm c (rest (cd1 - cd2)) ++ perform pm c' (retro (cut d m2)))
-> perform pm c (remove (dur m1 - d) (retro m1)) 
   `merge` ([] ++ perform pm c' (remove (dur m2 - d) (retro m2)))
-> perform pm c (remove (dur m1 - d) (retro m1)) 
   `merge` (perform pm c (remove (dur m1 - d) (rest (dur m1 - dur m2)))
           ++ perform pm c' (remove (dur m2 - d) (retro m2)))
-> perform pm c (remove (dur m1 - d) (retro m1)) 
   `merge` (perform pm c (remove (dur m1 - d) (rest (dur m1 - dur m2)))
           ++ perform pm c' (remove (dur m2 - d - (dur m1 - dur m1)) (retro m2)))
-> perform pm c (remove (dur m1 - d) (retro m1)) 
   `merge` (perform pm c (remove (dur m1 - d) (rest (dur m1 - dur m2)))
           ++ perform pm c' (remove ((dur m1 - d) - (dur m1 - dur m2)) (retro m2)))
-> perform pm c (remove (dur m1 - d) (retro m1)) 
   `merge` (perform pm c (remove (dur m1 - d) (rest (dur m1 - dur m2)))
           ++ perform pm c' (remove ((dur m1 - d) - dur (rest (dur m1 - dur m2))) (retro m2)))
-> perform pm c (remove (dur m1 - d) (retro m1)) 
   `merge` 
   perform pm c (remove (dur m1 - d) (rest (dur m1 - dur m2))
     :+: remove ((dur m1 - d) - dur (rest (dur m1 - dur m2))) (retro m2))
-> perform pm c (remove (dur m1 - d) (retro m1)) 
   `merge` 
   perform pm c (remove (dur m1 - d) ((rest (dur m1 - dur m2)) :+: (retro m2)))
-> perform pm c (remove (dur m1 - d) (retro m1) 
   :=: remove (dur m1 - d) ((rest (dur m1 - dur m2)) :+: (retro m2)))
-> perform pm c (remove (dur m1 - d) (retro m1 
   :=: (rest (dur m1 - dur m2)) :+: (retro m2)))
[if dur m1 > dur m2]
-> perform pm c (remove (dur m1 - d) (retro (m1 :=: m2)))


dur (retro (cut d (m1 :=: m2)))
-> dur (retro (cut d m1 :=: cut d m2))
if cd1 > cd2 [--> for any d dur m1 is greater]
-> dur (retro (cut d m1) :=: (rest (cd1-cd2) :+: retro (cut d m2)))
-> dur (retro (cut d m1)) `max` dur (rest (cd1-cd2) :+: retro (cut d m2))
-> dur (retro (cut d m1)) `max` (dur (rest (cd1-cd2)) + dur (retro (cut d m2)))
-> dur (remove (dur m1 - d) (retro m1)) 
   `max` (dur (rest (cd1-cd2)) + dur (remove (dur m2 - d) (retro m2)))
-> dur (remove (dur m1 - d) (retro m1)) 
-> dur (remove (dur m1 - d) (retro (m1 :=: m2))) 
-> dur (remove ((dur m1 `max` dur m2) - d) (retro (m1 :=: m2))) 
-> dur (remove (dur (m1 :=: m2) - d) (retro (m1 :=: m2))) 
if cd1 < cd2 the proof turns out similarly



Aside: This is where the implications behind assuming cd1 > cd2 become obvious...
in determining c' on either side of the induction hypothesis.
Assuming cd1 > cd2 implied
 dur m1 > dur m2
 AND
 dur m2 < d

dur (rest (dur (cut d m1) - dur (cut d m2)))
-> dur (cut d m1) - dur (cut d m2)
-> min (d (dur m1)) - min (d (dur m2))
-> min (d (dur m1)) - dur m2

dur (remove (dur m1 - d) (rest (dur m1 - dur m2)))
-> max (dur m1 - dur m2 - dur m1 + d) 0
-> max (d - dur m2) 0



perform c pm (retro (cut d (tempo r m1)))
-> perform c pm (retro (tempo r (cut (d*r) m1)))
-> perform c pm (tempo r (retro (cut (d*r) m1)))
-> perform c pm (tempo r (remove (dur m1 - d*r) (retro m1)))
-> perform c pm (remove ((dur m1 - d*r)/r) (tempo r (retro m1)))
-> perform c pm (remove ((dur m1 / r) - d) (tempo r (retro m1)))
-> perform c pm (remove (dur (tempo r m1) - d) (tempo r (retro m1)))
-> perform c pm (remove (dur (tempo r m1) - d) (retro (tempo r m1)))

dur (retro (cut d (tempo r m1)))
-> dur (retro (tempo r (cut (d*r) m1)))
-> dur (tempo r (retro (cut (d*r) m1)))
-> dur (tempo r (remove (dur m1 - d*r) (retro m1)))
-> dur (remove ((dur m1 - d*r)/r) (tempo r (retro m1)))
-> dur (remove ((dur m1 / r) - d) (tempo r (retro m1)))
-> dur (remove (dur (tempo r m1) - d) (tempo r (retro m1)))
-> dur (remove (dur (tempo r m1) - d) (retro (tempo r m1)))


let f be a function f :: Control -> Context a -> Context a
such that perform ((f ctrl) c) pm m = perform c pm (Modidfy c m)

perform c pm (retro (cut d (Modify ctrl m1)))
-> perform c pm (Modify ctrl (retro (cut d m1)))
-> perform ((f ctrl) c) pm (retro (cut d m1))
-> perform ((f ctrl) c) pm (remove (dur m1 - d) (retro m1))
-> perform c pm (Modify ctrl (remove (dur m1 - d) (retro m1)))
-> perform c pm (remove (dur m1 - d) (retro (Modify ctrl m1)))






Prove: retro (remove d m) ≡ cut (dur m - d) (retro m)
Proof by structural induction on m...
Base Case

perform pm c (retro (remove d (note oldD p)))
-> perform pm c (remove d (note oldD p))
if d < oldD
-> perform pm c (note ((oldD-d) `max` 0) p)
-> perform pm c (note ((oldD `min` (oldD-d)) `max` 0) p)
-> perform pm c (cut (oldD-d) (note oldD p))
-> perform pm c (cut (oldD-d) (retro (note oldD p)))
if d >= oldD
-> perform pm c (remove d (note oldD p))
-> perform pm c (rest 0)
-> perform pm c (cut (oldD-d) (note oldD p))
-> perform pm c (cut (oldD-d) (retro (note oldD p)))

dur (retro (remove d (note oldD p)))
-> dur (remove d (note oldD p))
-> (oldD-d) `max` 0
-> (oldD `min` (oldD-d)) `max` 0
-> dur (cut (oldD-d) (note oldD p))


perform pm c (retro (remove d (rest oldD)))
-> perform pm c (remove d (rest oldD))
-> perform pm c (rest ((oldD-d) `max` 0))
-> perform pm c (rest ((oldD `min` (oldD-d)) `max` 0))
-> perform pm c (cut (oldD-d) (rest oldD))
-> perform pm c (cut (oldD-d) (retro (rest oldD)))

dur (retro (remove d (rest oldD)))
-> dur (remove d (rest oldD))
-> (oldD-d) `max` 0
-> (oldD `min` (oldD-d)) `max` 0
-> dur (cut (oldD-d) (rest oldD))


Induction Step

let  d1 = dur m1
     d2 = dur m2
    rd1 = dur (remove d m1)
    rd2 = dur (remove d m2)
    d2  = d1 - (d1 - d2)

perform pm c (retro (remove d (m1 :=: m2)))
-> perform pm c (retro (remove d m1 :=: remove d m2))

rd1 > rd2  --> d1 > d2 && d1 > d  [Shown]
rd1 < rd2  --> d1 < d2 && d2 > d  [Same logic as above case, not shown]
rd1 == rd2 --> d < d1 && d < d2 && d1 == d2 || (d >= d1 && d >= d2)   [Shown]

if rd1 > rd2
-> perform pm c (retro (remove d m1) 
                 :=: (rest (rd1 - rd2) :+: retro (remove d m2)))
-> perform pm c (cut (d1 - d) (retro m1) 
                 :=: (rest (rd1 - rd2) :+: cut (d2 - d) (retro m2)))
  if d2 > d
     [In this case, rd1 - rd2 = d1 - d2]
  -> perform pm c (cut (d1 - d) (retro m1) 
                   :=: (rest (d1 - d2) :+: cut (d2 - d) (retro m2)))
  -> perform pm c (cut (d1 - d) (retro m1) 
                   :=: (rest (d1 - d2)
                      :+: cut (d2 + (d1 - d1) - d) (retro m2)))
  -> perform pm c (cut (d1 - d) (retro m1) 
                 :=: (rest (d1 - d2)
                      :+: cut (d1 - (d1 - d2) - d) (retro m2)))
  -> perform pm c (cut (d1 - d) (retro m1) 
                 :=: (rest (d1 - d2)
                      :+: cut (d1 - d - dur (rest (d1 - d2))) (retro m2)))
  -> perform pm c (cut (d1 - d) (retro m1) 
                 :=: (rest (d1 - d2)
                      :+: cut (d1 - d - dur (cut (d1 - d) rest (d1 - d2))) (retro m2)))
  -> perform pm c (cut (d1 - d) (retro m1) 
                 :=: (cut (d1 - d) (rest (d1 - d2) :+: retro m2))
  -> perform pm c (cut (d1 - d) (retro m1 :=: rest (d1 - d2) :+: retro m2))
  -> perform pm c (cut (d1 - d) (retro (m1 :=: m2)))
  -> perform pm c (cut (dur (m1 :=: m2) - d) (retro (m1 :=: m2)))

  if d2 <= d  --> d1-d < d1-d2 !!!
  ---
  Key Realization about rd1-rd2:
    max -> d1-d
    min -> d1-d  if d2<=d
           d1-d2 if d2 >d
  ---
  -> perform pm c (cut (d1 - d) (retro m1) 
                   :=: (rest (rd1 - rd2) :+: cut (d2 - d) (retro m2)))
  -> perform pm c (cut (d1 - d) (retro m1) 
                   `merge` perform pm c (rest (rd1 - rd2) :+: cut (d2 - d) (retro m2)))
  let c' = c{cTime = t + dur (rd1-rd2) * dt}
  since d2 <= d, rd1-rd2 = rd1 = d1 - d
  -> perform pm c (cut (d1 - d) (retro m1) 
                   `merge` perform pm c (rest (rd1 - rd2)) 
                           ++ perform pm c' (cut (d2 - d) (retro m2)))
  -> perform pm c (cut (d1 - d) (retro m1) 
                   `merge` [] 
                           ++ perform pm c' (cut (d2 - d) (retro m2)))
  -> perform pm c (cut (d1 - d) (retro m1) 
                   `merge` perform pm c (rest (d1 - d)) 
                           ++ perform pm c' (cut (d2 - d) (retro m2)))
  -> perform pm c (cut (d1 - d) (retro m1) 
                   `merge` perform pm c (rest (d1 - d) :+: cut (d2 - d) (retro m2)))
  -> perform pm c (cut (d1 - d) (retro m1) 
                   :=: (rest (d1 - d) :+: cut (d2 - d) (retro m2)))
  -> perform pm c (cut (d1 - d) (retro m1) 
                   :=: (rest (d1 - d) :+: cut (d2 - d) (retro m2)))
  -> perform pm c (cut (d1 - d) (retro m1) 
                   :=: (rest (d1 - d) :+: rest 0))
  -> perform pm c (cut (d1 - d) (retro m1) 
                   :=: (rest (d1 - d) :+: cut ((d1-d)-(d1-d)) (retro m2)))
  -> perform pm c (cut (d1 - d) (retro m1) 
                   :=: (rest (d1 - d) 
                       :+: cut ((d1-d) - dur (cut (d1-d) (rest (d1-d2)))) (retro m2)))
  -> perform pm c (cut (d1 - d) (retro m1) 
                   :=: cut (d1-d) (rest (d1 - d2) :+: retro m2))
  -> perform pm c (cut (d1-d) (retro m1 :=: (rest (d1-d2) :=: retro m2)))
  -> perform pm c (cut (d1-d) (retro (m1 :=: m2)))
  -> perform pm c (cut (dur (m1 :=: m2) - d) (retro (m1 :=: m2)))

if rd1 == rd2 --> d < d1 && d < d2 && d1 == d2  (case 1)
          || (d >= d1 && d >= d2)   (case 2)
  case 2...
  -> perform pm c ((rest 0 :+: retro (remove d m1)) :=: retro (remove d m2))
  -> perform pm c ((rest 0 :+: cut (d1-d) (retro m1)) :=: cut (d2-d) (retro m2))
  -> perform pm c ((cut (d1-d) (rest (d2-d1)) 
                      :+: cut (d1-d - dur (cut (d1-d) (rest (d2-d1))) (retro m1))) 
                    :=: cut (d2-d) (retro m2))
  -> perform pm c ((cut (d1-d) (rest (d2-d1)  :+: retro m1))
                    :=: cut (d2-d) (retro m2))
  -> perform pm c ((cut (d1-d) (rest (d2-d1)  :+: retro m1))
                    :=: rest 0)
  -> perform pm c ((cut (d1-d) (rest (d2-d1) :+: retro m1))
                    :=: cut (d1-d) (retro m2))
  -> perform pm c (cut ((max d1 d2)-d) ((rest (d2-d1) :+: retro m1) :=: retro m2))
  -> perform pm c (cut (dur (m1 :=: m2)-d) ((rest (d2-d1) :+: retro m1) :=: retro m2))
  -> perform pm c (cut (dur (m1 :=: m2)-d) (retro (m1 :=: m2)))

  case 1
  -> perform pm c ((rest 0 :+: retro (remove d m1)) :=: retro (remove d m2))
  -> perform pm c ((rest 0 :+: cut (d1-d) (retro m1)) :=: cut (d2-d) (retro m2))
  -> perform pm c ((cut (d1-d) (rest (d2-d1)) 
                      :+: cut (d1-d - dur (cut (d1-d) (rest (d2-d1))) (retro m1))) 
                    :=: cut (d2-d) (retro m2))
  -> perform pm c ((cut (d1-d) (rest (d2-d1)  :+: retro m1))
                    :=: cut (d2-d) (retro m2))
  -> perform pm c ((cut (d1-d) (rest (d2-d1)  :+: retro m1))
                    :=: cut (d1-d) (retro m2))
  -> perform pm c (cut ((max d1 d2)-d) ((rest (d2-d1) :+: retro m1) :=: retro m2))
  -> perform pm c (cut (dur (m1 :=: m2)-d) ((rest (d2-d1) :+: retro m1) :=: retro m2))
  -> perform pm c (cut (dur (m1 :=: m2)-d) (retro (m1 :=: m2)))


dur (retro (remove d (m1 :=: m2))) 
-> dur (retro (remove d m1 :=: remove d m2))
if rd1 > rd2 [rd1<rd2 is similar]
-> dur (retro (remove d m1) :=: (rest (rd1-rd2) :+: remove d m2))
-> dur (cut (d1 - d) (retro m1) 
        :=: (rest (rd1-rd2) :+: cut (d2 - d) (retro m2)))

-> dur (cut (d1 - d) (retro m1)) 
        `max` dur (rest (rd1-rd2) :+: cut (d2 - d) (retro m2))
  if d2>d
  -> dur (cut (d1 - d) (retro m1)) 
          `max` ((rd1-rd2) + min ((d2 - d) (dur (retro m2))))
  -> dur (cut (d1 - d) (retro m1)) 
          `max` ((max (d1-d) 0 - max (d2-d) 0) + min ((d2 - d) (dur (retro m2))))
  -> dur (cut (d1 - d) (retro m1)) 
          `max` ((max (d1-d) 0 - max (d2-d) 0) + (d2 - d))
  -> dur (cut (d1 - d) (retro m1)) 
          `max` (max (d1-d) 0)
  -> dur (cut (d1 - d) (retro m1)) 
          `max` (d1-d)
  -> (min (d1 - d) (dur (retro m1))) 
          `max` (d1-d)
  -> (d1 - d)
  -> (max d1 d2) - d
  -> min ((d1 `max` d2)-d) (max d1 d2))
  -> min ((d1 `max` d2)-d) (dur (m1 :=: m2))
  -> min ((d1 `max` d2)-d) (dur (retro (m1 :=: m2)))
  -> min (dur (m1 :=: m2) - d) (dur (retro (m1 :=: m2)))
  -> dur $ cut (dur (m1 :=: m2) - d) (retro (m1 :=: m2))
  if d2<=d
  -> dur (cut (d1 - d) (retro m1)) 
          `max` dur (rest rd1 :+: cut (d2 - d) (retro m2))
  -> dur (cut (d1 - d) (retro m1)) 
          `max` dur (rest rd1 :+: rest 0)
  -> dur (cut (d1 - d) (retro m1)) 
          `max` (d1-d)
  -> (min (d1 - d) d1) 
          `max` (d1-d)
  -> (d1 - d)
  -> (max d1 d2) - d
  -> min ((d1 `max` d2)-d) (max d1 d2))
  -> min ((d1 `max` d2)-d) (dur (m1 :=: m2))
  -> min ((d1 `max` d2)-d) (dur (retro (m1 :=: m2)))
  -> min (dur (m1 :=: m2) - d) (dur (retro (m1 :=: m2)))
  -> dur $ cut (dur (m1 :=: m2) - d) (retro (m1 :=: m2))


if rd1 == rd2
  2 cases: (1) d<d1 && d<d2 && d1 == d2 
           (2) d>=d1 && d>=d2
  (1)
-> dur (retro (remove d m1 :=: remove d m2))
-> dur ((rest (rd2-rd1) :+: retro (remove d m1)) :=: retro (remove d m2))
-> dur ((rest 0 :+: cut (d1-d) (retro m1)) :=: cut (d2-d) (retro m2))
-> dur (cut (d1-d) (rest 0 :+: retro m1) :=: cut (d2-d) (retro m2))
-> dur (cut (d1-d) (rest 0 :+: retro m1) :=: cut (d1-d) (retro m2))
-> dur (cut (d1-d) ((rest 0 :+: retro m1) :=: retro m2))
-> dur (cut ((d1 `max` d2)-d) (((d2-d1) :+: retro m1) :=: retro m2))
-> dur (cut ((dur (m1 :=: m2))-d) (retro (m1 :=: m2))) 
  (2)
-> dur (retro (remove d m1 :=: remove d m2))
-> dur ((rest (rd2-rd1) :+: retro (remove d m1)) :=: retro (remove d m2))
-> dur ((rest 0 :+: cut (d1-d) (retro m1)) :=: cut (d2-d) (retro m2))
-> dur ((cut (d1-d) (rest (d2-d1))
           :+: cut (d1-d - dur (cut (d1-d) (rest d2-d1))) (retro m1)) 
         :=: cut (d2-d) (retro m2))
-> dur (cut (d1-d) (rest (d2-d1) :+: retro m1) :=: cut (d2-d) (retro m2))
-> dur (cut (d1-d) (rest (d2-d1) :+: retro m1) :=: (rest 0))
-> dur (cut (d1-d) (rest (d2-d1) :+: retro m1) :=: cut (d1-d) (retro m2))
-> dur (cut (d1-d) ((rest (d2-d1) :+: retro m1) :=: retro m2))
-> dur (cut ((d1 `max` d2)-d) (((d2-d1) :+: retro m1) :=: retro m2))
-> dur (cut ((dur (m1 :=: m2))-d) (retro (m1 :=: m2))) 




retro (remove d (m1 :+: m2))
[Do not need to use perform pm c, and therefore do not need to prove duration equivalence.]
if d1 >=d
-> retro (remove d m1 :+: remove (d-d1) m2)
-> retro (remove (d-d1) m2) :+: retro (remove d m1)
-> cut (d2 - (d-d1)) (retro m2) :+: cut (d1-d) (retro m1)
-> cut (d1+d2 -d) (retro m2) :+: cut (d1-d) (retro m1)
-> cut (d1+d2 -d) (retro m2) :+: cut (d1+d2-d-d2) (retro m1)  [if d1>=d]
-> cut (d1+d2 -d) (retro m2) 
   :+: cut ((d1+d2-d) - dur (cut (d1+d2-d) (retro m2))) (retro m1)
-> cut (d1+d2-d) (retro m2 :+: retro m1)
-> cut (dur (m1 :+: m2)-d) (retro (m1 :+: m2))
if d1 < d
-> retro (remove d m1 :+: remove (d-d1) m2)
-> retro (rest 0 :+: remove (d-d1) m2)
-> cut (d2 - (d-d1)) (retro m2) :+: rest 0
-> cut (d2 - (d-d1)) (retro m2) :+: rest 0
-> cut (d2 - (d-d1)) (retro m2) :+: cut (d2-(d-d1) - (d2-(d-d1))) (retro m1)
-> cut (d2 - (d-d1)) (retro m2) 
   :+: cut (d2-(d-d1) - min (d2-(d-d1)) (dur (retro m2))) (retro m1)
-> cut (d2 - (d-d1)) (retro m2)
   :+: cut (d2-(d-d1) - dur (cut (d2-(d-d1)) (retro m2))) (retro m1)
-> cut (d1+d2-d) (retro m2 :+: retro m1)
-> cut (dur (m1 :+: m2)-d) (retro (m1 :+: m2))



retro (remove d (tempo r m1))
[Do not need to use perform pm c, and therefore do not need to prove duration equivalence.]
-> retro (tempo r (remove (d*r) m1))
-> tempo r (retro (remove (d*r) m1))
-> tempo r (cut (d1 - (d*r)) (retro m1))
-> tempo r (cut ((d1/r - d)*r) (retro m1))
-> cut (d1/r - d) (tempo r (retro m1))
-> cut (d1/r - d) (retro (tempo r m1))
-> cut (dur (tempo r m1) - d) (retro (tempo r m1))



retro (remove d (Modify c m1))
[Do not need to use perform pm c, and therefore do not need to prove duration equivalence.]
-> retro (Modify c (remove d m1))
-> Modify c (retro (remove d m1))
-> Modify c (cut (d1 - d) (retro m1))
-> cut (d1 - d) (Modify c (retro m1))
-> cut (d1 - d) (retro (Modify c m1))






Prove: cut d (retro m) ≡ retro (remove (dur m - d) m)
Proof by Structural Induction on m...


Base Case
[Do not need to use perform pm c, and therefore do not need to prove duration equivalence.]
NOTE
cut d (retro (note oldD p))
-> cut d (note oldD p)
if d == 0 || oldD == 0
if d == 0
-> rest 0
-> retro (rest 0)
-> retro (remove oldD (note oldD p))
-> retro (remove (oldD-0) (note oldD p))
if oldD == 0
-> note 0 p
-> retro (note 0 p)
-> retro (remove (0-d) (note oldD p))
-> retro (remove (oldD-d) (note oldD p))

if d>0 && oldD > 0
cut d (retro (note oldD p))
-> cut d (note oldD p)
if d<=oldD
-> note (max (min oldD d) 0) p
-> note (max d 0) p
-> retro (note (max (oldD-(oldD-d)) 0) p)
-> retro (remove (oldD-d) (note oldD p))
if d>oldD
-> note (max (min oldD d) 0) p
-> note (max oldD 0) p
-> note (max (oldD-0) 0) p
-> retro (note (max (oldD-0) 0) p)
-> retro (remove 0 (note oldD p))
-> retro (remove (oldD-d) (note oldD p))

REST
cut d (retro (rest oldD))
-> cut d (rest oldD)
if d<=oldD
-> rest (max (min oldD d) 0)
-> rest (max d 0)
-> retro (rest (max (oldD-(oldD-d)) 0))
-> retro (remove (oldD-d) (rest oldD))
if d>oldD
-> rest (max (min oldD d) 0)
-> rest (max oldD 0)
-> rest (max (oldD-0) 0)
-> retro (rest (max (oldD-0) 0))
-> retro (remove 0 (rest oldD))
-> retro (remove (oldD-d) (rest oldD))


Induction Step...
let d1 = dur m1
    d2 = dur m2

cut d (retro (m1 :=: m2))
if d1>d2 [Proof is very similar for d1<=d2 and is omitted]
-> cut d (retro m1 :=: (rest (d1-d2) :+: retro m2))
-> cut d retro m1 :=: cut d (rest (d1-d2) :+: retro m2)
let cutpad = cut d (rest (d1-d2))
-> cut d retro m1 
   :=: (cutpad :+: cut (d - dur cutpad) retro m2)
-> retro (remove (d1-d) m1)
   :=: (cutpad :+: retro (remove (d2 - (d - dur cutpad)) m2))
-> retro (remove (d1-d) m1)
   :=: (cutpad :+: retro (remove ((d2 + dur cutpad) - d) m2))
---
Show
dur cutpad = dur (remove (d1-d) m1) - dur (remove (d2 - (d - dur cutpad)) m2)

dur cutpad 
= dur $ cut d (rest (d1-d2))
= min d (d1-d2)

dur (remove (d1-d) m1) - dur (remove (d2 - (d - dur cutpad)) m2)
= (max (d1-(d1-d)) 0) - (max (d2 - (d2 - (d - dur cutpad))) 0)
= (max d 0) - (max (d2 - (d2 - (d - dur cutpad))) 0)
= (max d 0) - (max (d - dur cutpad) 0)
= (max d 0) - (max (d - (min d (d1-d2))) 0)
= (max d 0) - (d - (min d (d1-d2)))
= min d (d1-d2)
---
-> retro (remove (d1-d) m1 :=: remove ((d2 + dur cutpad) - d) m2)
-> retro (remove (d1-d) m1 :=: remove (d2 + (min d (d1-d2)) - d) m2)
-> retro (remove (d1-d) m1 :=: remove (d2 + (min 0 (d1-d2-d))) m2)
-> retro (remove (d1-d) m1 :=: remove (min d2 (d1-d)) m2)
-> retro (remove (d1-d) m1 :=: remove (d1-d) m2)*
-> retro (remove (d1-d) (m1 :=: m2))

* remove (min d2 (d1-d)) m2 == remove (d1-d) m2
max (d2 - (min d2 (d1-d))) 0
-> max (d2 + (max (-d2) (-(d1-d)))) 0
-> max (max 0 (d-d1+d2)) 0
-> max 0 (d-d1+d2))
-> max 0 (d2-(d1-d)))

[Do not need to use perform pm c, and therefore do not need to prove duration equivalence]





cut d (retro (m1 :+: m2))
-> cut d (retro m2 :+: retro m1)
-> cut d (retro m2) :+: cut (d - dur (cut d (retro m2))) m1
if d2>d
-> retro (remove (d2 - d) m2) :+: cut (d - dur (cut d (retro m2))) m1
-> retro (remove (d2 - d) m2) :+: rest 0
-> retro (remove (d2 - d) m2) :+: retro (rest 0)
-> retro (rest 0 :+: remove (d2 - d) m2)
-> retro (remove (d1+d2-d) m1 :+: remove (d2 - d) m2)
-> retro (remove (d1+d2-d) m1 :+: remove (d1+d2 - d -d1) m2)
-> retro (remove (d1+d2-d) (m1 :+: m2))
-> retro (remove (dur (m1:+:m2) - d) (m1 :+: m2))
if d2<=d
-> retro (remove (d2 - d) m2) :+: retro (remove (d1 - (d - dur (cut d (retro m2)))) m1)
-> retro (remove (d1 - (d - dur (cut d (retro m2)))) m1 :+: remove (d2 - d) m2)
-> retro (remove (d1 + dur (cut d (retro m2)) - d) m1 :+: remove (d2 - d) m2)
-> retro (remove (d1 + dur (retro m2) - d) m1 :+: remove (d2 - d) m2)
-> retro (remove (d1 + d2 - d) m1 :+: remove (d1+d2 - d -d1) m2)
-> retro (remove (d1+d2-d) (m1 :+: m2))
-> retro (remove (dur (m1:+:m2) - d) (m1 :+: m2))
[Do not need to use perform pm c, and therefore do not need to prove duration equivalence]



cut d (retro (tempo r m1))
-> cut d (tempo r (retro m1))
-> tempo r (cut (d*r) (retro m1))
-> tempo r (retro (remove (d1 - d*r) m1))
-> retro (tempo r (remove (d1 - d*r) m1))
-> retro (tempo r (remove ((d1/r - d)/r) m1))
-> retro (remove (dur m1/r - d) (tempo r m1))
-> retro (remove (dur (tempo r m1) - d) (tempo r m1))
[Do not need to use perform pm c, and therefore do not need to prove duration equivalence]



cut d (retro (Modify c m1))
-> cut d (Modify c (retro m1))
-> Modify c (cut d (retro m1))
-> Modify c (retro (remove (d1 - d) m1))
-> retro (Modify c (remove (d1 - d) m1))
-> retro (remove (d1 - d) (Modify c m1))
[Do not need to use perform pm c, and therefore do not need to prove duration equivalence]













Prove: remove d (retro m) ≡ retro (cut (dur m - d) m)
Proof by structural induction on m...
Base Case

Note
remove d (retro (note oldD p))
-> remove d (note oldD p)
if oldD>d
-> note (max (oldD-d) 0) p
-> note (oldD-d) p
-> note min (oldD (oldD-d)) p
-> note (max (min (oldD (oldD-d)) 0) p
-> retro (note (max (min (oldD (oldD-d)) 0) p)
-> retro (cut (oldD-d) (note oldD p))
if oldD<=d
-> rest 0
-> cut (oldD-d) (note oldD p)
-> retro (cut (oldD-d) (note oldD p))

Rest
remove d (retro (rest oldD))
-> remove d (rest oldD)
if oldD>d
-> rest (max (oldD-d) 0)
-> rest (oldD-d)
-> rest min (oldD (oldD-d))
-> rest (max (min (oldD (oldD-d)) 0)
-> retro (rest (max (min (oldD (oldD-d)) 0))
-> retro (cut (oldD-d) (rest oldD))
if oldD<=d
-> rest 0
-> cut (oldD-d) (rest oldD)
-> retro (cut (oldD-d) (rest oldD))


[Do not need to use perform pm c, and therefore do not need to prove duration equivalence]

Induction Step


remove d (retro (m1 :=: m2))
if d1>d2 [Proof for d1>=d2 is similar and is omitted]
-> remove d (retro m1 :=: (rest (d1-d2) :+: retro m2))
-> remove d (retro m1) :=: remove d (rest (d1-d2) :+: retro m2)
let rmvpad = remove d (rest (d1-d2))
-> retro (cut (d1-d) m1) :=: (rmvpad :+: remove (d - dur (rest (d1-d2))) (retro m2))
-> retro (cut (d1-d) m1) :=: (rmvpad :+: retro (cut (d2 - (d - dur (rest (d1-d2)))) m2))
-> retro (cut (d1-d) m1) :=: (rmvpad :+: retro (cut (d2 - d + dur (rest (d1-d2))) m2))
-> retro (cut (d1-d) m1) :=: (rmvpad :+: retro (cut (d2 - d + d1 - d2) m2))
-> retro (cut (d1-d) m1) :=: (rmvpad :+: retro (cut (d1-d) m2))
let somepad = rest x such that 
          x = dur (cut (d1-d) m1) - dur (cut (d1-d) m2)
-> retro (cut (d1-d) m1) :=: (somepad :+: retro (cut (d1-d) m2))
-> retro (cut (d1-d) m1 :=: cut (d1-d) m2)
-> retro (cut (d1-d) (m1 :=:m2))
-> retro (cut (max d1 d2 - d) (m1 :=:m2))
-> retro (cut (dur (m1 :=: m2) - d) (m1 :=:m2))
---
Prove: somepad = rmvpad

somepad
dur (cut (d1-d) m1) - dur (cut (d1-d) m2)
= min (d1-d) d1 - min (d1-d) d2
= (d1-d) - min (d1-d) d2

rmvpad
dur (remove d (rest (d1-d2)))
= max ((d1-d2)-d) 0
= max ((d1-d)-d2) 0

if (d1-d)>d2
somepad = (d1-d) - d2 = max ((d1-d)-d2) 0 = rmvpad

if (d1-d)<= d2
somepad = (d1-d) - (d1-d) = 0 = max ((d1-d)-d2) 0 = rmvpad
---
[Do not need to use perform pm c, and therefore do not need to prove duration equivalence]




remove d (retro (m1 :+: m2))
-> remove d (retro m2 :+: retro m1)
-> remove d (retro m2) :+: remove (d-d2) (retro m1)
-> retro (cut (d2-d) m2) :+: retro (cut (d1-(d-d2)) m1)
-> retro (cut (d1-(d-d2)) m1 :+: cut (d2-d) m2)
-> retro (cut (d1+d2-d) m1 :+: cut (d2-d) m2)
if d2>=d
-> retro (cut ((d1+d2)-d) m1 :+: cut ((d1+d2)-d-d1) m2)
-> retro (cut ((d1+d2)-d) m1 :+: cut ((d1+d2)-d-dur (cut ((d1+d2)-d) m1)) m2)
-> retro (cut (d1+d2-d) (m1 :+: m2))
-> retro (cut (dur (m1:+:m2)-d) (m1 :+: m2))
if d2<d
-> retro (cut (d1+d2-d) m1 :+: cut (d2-d) m2)
-> retro (cut (d1-(d-d2)) m1 :+: rest 0)
-> retro (cut (d1-(d-d2)) m1 :+: cut (d1-(d-d2) -(d1-(d-d2))) m2)
-> retro (cut (d1-(d-d2)) m1 
          :+: cut (d1-(d-d2) - dur (cut (d1-(d-d2)) m1)) m2)
-> retro (cut (d1-(d-d2)) (m1 :+: m2))
-> retro (cut (d1+d2-d) (m1 :+: m2))
-> retro (cut (dur (m1 :+: m2) - d) (m1 :+: m2))
[Do not need to use perform pm c, and therefore do not need to prove duration equivalence]

[I proved duration equivalence first, in order to
 gain intuition for the main proof above. I left it here.]
dur (remove d (retro (m1 :+: m2)))
-> dur (remove d (retro m2 :+: retro m1))
-> dur (remove d (retro m2) :+: remove (d-d2) (retro m1))
if d >= d2
-> dur (rest 0 :+: remove (d-d2) (retro m1))
-> dur (rest 0 :+: retro (cut (d1-(d-d2)) m1))
-> dur (rest 0) + dur (retro (cut (d1-(d-d2)) m1))
-> dur (cut (d1-(d-d2)) m1)
-> min (d1-(d-d2)) d1
-> d1+d2-d
-> min (d1+d2-d) (d1+d2)
-> dur (cut (d1+d2-d) (m1 :+: m2))
-> dur (cut (dur (m1 :+: m2)-d) (m1 :+: m2))
-> dur (retro (cut (dur (m1 :+: m2)-d) (m1 :+: m2)))
if d<d2
-> dur (remove d (retro m2) :+: remove (d-d2) (retro m1))
-> dur (remove d (retro m2) :+: retro m1)
-> dur (retro (cut (d2-d) m2) :+: retro m1)
-> dur (cut (d2-d) m2) + dur (retro m1)
-> min (d2-d) d2 + d1
-> d2-d + d1
-> min (d1+d2-d) (d1+d2)
-> dur (cut (d1+d2-d) (m1 :+: m2))
-> dur (cut (dur (m1 :+: m2)-d) (m1 :+: m2))
-> dur (retro (cut (dur (m1 :+: m2)-d) (m1 :+: m2)))


remove d (retro (tempo r m1))
-> remove d (tempo r (retro m1))
-> tempo r (remove (d*r) (retro m1))
-> tempo r (retro (cut (d1 - (d*r)) m1))
-> retro (tempo r (cut (d1 - (d*r)) m1))
-> retro (tempo r (cut ((d1/r - d)*r) m1))
-> retro (cut (d1/r - d) (tempo r m1))
-> retro (cut (dur (tempo r m1) - d) (tempo r m1))
[Do not need to use perform pm c, and therefore do not need to prove duration equivalence]


remove d (retro (Modify c m1))
-> remove d (Modify c (retro m1))
-> Modify c (remove d (retro m1))
-> Modify c (retro (cut (d1-d) m1))
-> retro (Modify c (cut (d1-d) m1))
-> retro (cut (d1-d) (Modify c m1))
[Do not need to use perform pm c, and therefore do not need to prove duration equivalence]

















Properties of dur


Prove: dur (retro m) = dur m
Proof by Induction on m...

Base Case
dur (retro (Prim m))
-> dur (Prim m)

Induction Step
dur (retro (m1 :+: m2))
-> dur (retro m2 :+: retro m1)
-> dur (retro m2) + dur (retro m1)
-> dur (retro m1) + dur (retro m2)
-> dur m1 + dur m2
-> dur (m1 :+: m2)

dur (retro (m1 :=: m2))
let d1 = dur m1
    d2 = dur m2
if d1 > d2
-> dur (retro m1 :=: (rest (d1-d2) :+: retro m2))
-> max (dur retro m1) (dur (rest (d1-d2) :+: retro m2))
-> max (dur m1) (dur (rest (d1-d2)) + dur (retro m2))
-> max (dur m1) (dur (rest (d1-d2)) + dur m2)
-> dur m1
-> max (dur m1) (dur m2)
-> dur (m1 :=: m2)
if d1>=d2
-> dur ((rest (d2-d1) :+: retro m1) :=: retro m2)
-> max (dur (rest (d2-d1) :+: retro m1)) (dur (retro m2))
-> max (dur (rest (d2-d1)) + dur (retro m1)) (dur (retro m2))
-> max (dur (rest (d2-d1)) + dur m1) (dur m2)
-> dur m2
-> max (dur m1) (dur m2)
-> dur (m1 :=: m2)

dur (retro (tempo r m))
-> dur (tempo r (retro m))
-> dur (retro m) / r
-> dur m / r
-> dur (tempo r m)

dur (retro (Modify c m))
-> dur (Modify c (retro m))
-> dur (retro m)
-> dur m



For all non-negative d [Not in the book, but required for the proof]
Prove: dur (cut d m) = min d (dur m)
Proof by Induction on m...

Base Case
dur (cut d (note oldD p))
if oldD > 0 && d > 0
-> dur (note (max (min oldD d) 0) p)
-> max (min oldD d) 0
-> min oldD d
-> min d oldD
-> min d (dur (note oldD p))
if oldD = 0 || d = 0
-> dur (rest 0)
-> 0
  if oldD = 0
  -> min d 0
  -> min d (dur (note oldD p))
  if d = 0
  -> min 0 oldD
  -> min d oldD
  -> min d (dur (note oldD p))

dur (cut d (rest oldD))
-> dur (rest (max (min oldD d) 0))
-> max (min oldD d) 0
-> min (max oldD 0) (max d 0)
-> min oldD d                  [assuming oldD >= 0 && d >= 0]
-> min d oldD
-> min d (dur (rest oldD))


Induction Step
dur (cut d (m1 :=: m2))
-> dur (cut d m1 :=: cut d m2)
-> dur (cut d m1) `max` dur (cut d m2)
-> min d (dur m1) `max` min d (dur m2)
-> d `min` ((dur m1) `max` (dur m2))
-> d `min` (dur (m1 :=: m2))
-> min d (dur (m1 :=: m2))

dur (cut d (m1 :+: m2))
-> dur (cut d m1 :+: cut (d - dur (cut d m1)) m2)
-> (dur (cut d m1)) + (dur (cut (d - dur (cut d m1)) m2))
-> min d (dur m1) + min (d - dur (cut d m1)) (dur m2)
if dur m1 <= d
-> dur m1 + min (d - dur (cut d m1)) (dur m2)
-> dur m1 + min (d - dur m1) (dur m2)
-> min d (dur m1 + dur m2)
if dur m1 > d
-> d + min (d - dur (cut d m1)) (dur m2)
-> d + min 0 (dur m2)
-> d
-> min d (dur m1 + dur m2)
-> min d (dur (m1 :+: m2))

dur (cut d (tempo r m))
-> dur (tempo r (cut (d*r) m))
-> dur (cut (d*r) m) / r
-> (min (d*r) (dur m)) / r
-> min d (dur m / r)
-> min d (dur (tempo r m))

dur (cut d (Modify c m))
-> dur (Modify c (cut d m))
-> dur (cut d m)
-> min d (dur m)
-> min d (dur (Modify c m))




Prove: dur (remove d m) = max 0 (dur m - d)
Proof by Induction

Base Case
dur (remove d (note oldD p))
if oldD > d
-> dur (note (oldD - d) p)
-> oldD - d
-> max 0 (oldD - d)
-> max 0 (dur (note oldD p) - d)
if oldD <= d
-> dur (rest 0)
-> 0
-> max 0 (oldD - d)
-> max 0 (dur (note oldD p) - d)

dur (remove d (rest d))
-> dur (rest (max (oldD-d) 0))
-> max (oldD-d) 0
-> max 0 (dur (rest oldD) - d)

Induction Step

dur (remove d (m1 :=: m2))
-> dur (remove d m1 :=: remove d m2)
-> max (dur (remove d m1)) (dur (remove d m2))
-> max (max 0 (dur m1 - d)) (max 0 (dur m2 - d))
-> max 0 (max (dur m1 - d) (dur m2 - d))
-> max 0 ((max (dur m1) (dur m2)) - d)
-> max 0 (dur (m1 :=: m2) - d)


dur (remove d (m1 :+: m2))
if m1 <= d
-> dur (remove d m1 :+: remove (d - dur m1) m2)
-> dur (remove d m1) + dur (remove (d - dur m1) m2)
-> max 0 (dur m1 - d) + max 0 (dur m2 - (d - dur m1))
-> max 0 (dur m1 - d) + max 0 (dur m2 - (d - dur m1))
-> max 0 (dur m2 - d + dur m1)
-> max 0 (dur m1 + dur m2 - d)
-> max 0 (dur (m1 :+: m2) - d)

if m1 > d
dur (remove d (m1 :+: m2))
-> dur (remove d m1 :+: remove (d - dur m1) m2)
-> dur (remove d m1 :+: m2)
-> dur (remove d m1) + dur m2
-> max 0 (dur m1 - d) + dur m2
-> dur m1 - d + dur m2
-> dur m1 + dur m2 - d
-> (dur m1 + dur m2) - d
-> max 0 ((dur m1 + dur m2) - d)
-> max 0 (dur (m1 :+: m2) - d)

dur (remove d (tempo r m))
-> dur (tempo r (remove (d*r) m))
-> dur (remove (d*r) m) / r
-> (max 0 (dur m - (d*r))) / r
-> (max 0 ((dur m - (d*r))/r))
-> (max 0 (dur m / r - d))
-> (max 0 (dur (tempo r m) - d))

dur (remove d (Modify c m))
-> dur (Modify c (remove d m))
-> dur (remove d m)
-> max 0 (dur m - d)
-> max 0 (dur (Modify c m) - d)
-}
