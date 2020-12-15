module Types where

import Euterpea


simple       :: Num a => a -> a -> a -> a
simple x y z = x * (y + z)



{-

EXERCISE 7.1: Prove that the instance of Music in the class Eq satisfies the laws of its
class. Also prove that the modified instance of Music in the class Ord satisfies the 
laws of its class.

EQ

Assume p1 == p2 == p3 ( == is an equivalence relation on the Primitive type )

Let    m1 = Prim p1
       m2 = Prim p2
       m3 = Prim p3

Let    ma, mb, mc, md, me, mf be arbitrary Music values

       ms = ma :+: mb
       ms' = mc :+: md
       ms'' = me :+: mf

       mp = ma :=: mb
       mp' = mc :=: md
       mp'' = me :=: mf

       mct = Modify c ma
       mct' = Modify c mb
       mct'' = Modify c mc

Where c is an arbitrary object in the Control datatype.

Reflexive:
  prim
      m1 == m1 is immediate... specifically, 
      Prim p1 = Prim p1 and from the instance declaration of Music for Eq
      p1 == p1
  :+:
     ms  ==  ms
     -> (ma == ma) ∧ (mb == mb)
     -> True
  :=:
     mp  ==  mp
     -> (ma == ma) ∧ (mb == mb)
     -> True
  Modify c
     mct ==  mct
     -> (c == c) ∧ (ma == ma)
     -> True
Thus == is reflexive on Music

Symmetric:
  prim
     Assume m1 == m2. Then
     Prim p1 = Prim p2 and from the instance declaration of Music for Eq
     p1 == p2
     p2 == p1 ( == is an equivalence on Primitives )
     Prim p2 == Prim p1
     Thus m2 == m1
  :+:
     Assume ms  ==  ms'
     ms  ==  ms'
     -> (ma :+: mb) == (mc :+: md)
     -> (ma == mc) ∧ (mb == md)
     -> (mc == ma) ∧ (md == mb)
     -> (mc :+: md) ∧ (ma :+: md)
     -> ms' = ms
  :+:
     Assume mp  ==  mp'
     mp  ==  mp'
     -> (ma :=: mb) == (mc :=: md)
     -> (ma == mc) ∧ (mb == md)
     -> (mc == ma) ∧ (md == mb)
     -> (mc :=: md) ∧ (ma :=: md)
     -> mp' = mp
  Modify c
     Assume mct ==  mct'
     mct == mct'
     -> (c == c) ∧ (ma == mb)
     -> (c == c) ∧ (mb == ma)
     -> mct' == mct
Thus == is symmetric on Music

Transitive:
  prim
     Assume m1 == m2 and m2 == m3. Then 
     Prim p1 == Prim p2 and Prim p2 == Prim p3
     p1 == p2 and p2 == p3. == is an equivalence on the Primitive type class so
     p1 == p3 and Prim p1 == Prim p3.
     Thus m1 == m3.
  :+:
     Assume ms == ms' and ms' == ms''.
     ms == ms''
     -> (ma :+: mb) == (me :+: mf)
     -> (ma == mc == me) ∧ (mb == md == mf) [assuming transitivity at some point]
  :=:
     Assume mp == mp' and mp' == mp''.
     mp == mp''
     -> (ma :=: mb) == (me :=: mf)
     -> (ma == mc == me) ∧ (mb == md == mf) [assuming transitivity at some point]
  Modify c
     Assume mct ==  mct' and mct' == mct''
     mct == mct''
     -> (c == c) ∧ (ma == me)
     -> (c == c) ∧ (ma == mc == me)
     -> mct == mct''
Thus == is transitive on Music
Thus == is an equivalence relation on Music

     
ORD

Assume p1 ≤ p2 ≤ p3 ( ≤ is a total order on the Primitive type )

Let    m1 = Prim p1
       m2 = Prim p2
       m3 = Prim p3

Let    ma, mb, mc, md, me, mf be arbitrary Music values

       ms = ma :+: mb
       ms' = mc :+: md
       ms'' = me :+: mf

       mp = ma :=: mb
       mp' = mc :=: md
       mp'' = me :=: mf

       mct = Modify c ma
       mct' = Modify c mb
       mct'' = Modify c mc

       Where c is an arbitrary object in the Control datatype.

Reflexivity:
  prim
      m1 ≤ m1
      -> p1 ≤ p1
      -> True
  :+:
      ms ≤ ms
      -> (ma ≤ ma) ∨ (ma ≤ ma) ∧ (mb ≤ mb)
      -> True
  :=:
      mp ≤ mp
      -> (ma ≤ ma) ∨ (ma ≤ ma) ∧ (mb ≤ mb)
      -> True
  Modify c
      mct ≤ mct
      -> (c ≤ c) ∨ (c == c) ∧ (ma ≤ ma)
      -> True
≤ is Reflexive on Music 

Transitivity:
  prim
    Assume m1 ≤ m2 and m2 ≤ m3 
    m1 ≤ m3
    -> p1 ≤ p3
    -> True since ≤ is a total order on Primitives
  :+:
    Assume ms ≤ ms' and ms' ≤ ms''
    ms ≤ ms''
    -> (ma ≤ me) ∨ (ma == me) ∧ (mb ≤ mf)
    From ma ≤ mc and mc ≤ me    mb ≤ md and md ≤ mf 
    -> True
    Transitive Closure
  :=:
    Assume mp ≤ mp' and mp' ≤ mp''
    mp ≤ mp''
    -> (ma ≤ me) ∨ (ma == me) ∧ (mb ≤ mf)
    From ma ≤ mc and mc ≤ me    mb ≤ md and md ≤ mf 
    -> True
  Modify c
    Assume mct ≤ mct' and mct' ≤ mct''
    mct ≤ mct''
    -> (c ≤ c) ∨ (c == c) ∧ (ma ≤ mc) 
    From c ≤ c  and   ma ≤ mb and mb ≤ mc 
    -> True
≤ is Transitive on Music

Antisymmetric:
  prim
    Assume m1 ≤ m2 and m2 ≤ m1 
    Then p1 ≤ p2 and p2 ≤ p1
    -> p1 == p2 since ≤ is a total order on Primitives
  :+:
    Assume ms ≤ ms' and ms' ≤ ms
    ms ≤ ms'
    -> (ma ≤ mc) ∨ ( (ma == mc) ∧ (mb ≤ md) )
    -> (ma == mc) ∧ (mb ≤ md)

    ms' ≤ ms
    -> (mc ≤ ma) ∨ ( (mc == ma) ∧ (md ≤ mb) )
    -> (mc == ma) ∧ (md ≤ mb)

    From ma == mc and md ≤ mb and mb ≤ md
    -> True
  :=:
    Assume mp ≤ mp' and mp' ≤ mp
    mp ≤ mp'
    -> (ma ≤ mc) ∨ ( (ma == mc) ∧ (mb ≤ md) )
    -> (ma == mc) ∧ (mb ≤ md)

    mp' ≤ mp
    -> (mc ≤ ma) ∨ ( (mc == ma) ∧ (md ≤ mb) )
    -> (mc == ma) ∧ (md ≤ mb)

    From ma == mc and md ≤ mb and mb ≤ md
    -> True
  :=:
    -> True
  Modify c
    Assume mct ≤ mct' and mct' ≤ mct
    mct ≤ mct'
    -> (c ≤ c) ∨ (c == c) ∧ (ma ≤ mb) 

    mct' ≤ mct
    -> (c ≤ c) ∨ (c == c) ∧ (mb ≤ ma) 

    From c ≤ c  and   ma ≤ mb and mb ≤ ma
    ->  True
≤ is Antisymmetric on Music

Thus ≤ is a total order on Music

-}

{-
EXERCISE 7.2: Write out appropriate instance declarations for the Color type
in the classes Eq, Ord, and Enum.
-}

data Color = Blue | Green | Red
  deriving Show

instance Eq Color where 
  Blue == Blue   = True
  Green == Green = True
  Red == Red     = True
  _ == _         = False


instance Ord Color where
  Blue <= _  = True
  Green <= Green = True
  Green <= Blue  = False
  Green <= Red   = True
  Red <= Red     = True
  Red <= _       = False


instance Enum Color where 
  toEnum 0 = Blue
  toEnum 1 = Green
  toEnum 2 = Red
  fromEnum Blue = 0
  fromEnum Green = 1
  fromEnum Red = 2
  
{-EXERCISE 7.3: 
Define a type class called Temporal whose members are types that can be interpreted as 
having temporal duration. Temporal should have three operations, namely:

durT :: Temporal a => a -> Dur
cutT :: Temporal a => Dur -> a -> a
removeT :: Temporal a => Dur -> a -> a

Then define instances of Temporal for the types Music and Primitive.  -}



class Temporal a where
  durT :: a -> Dur
  cutT :: Dur -> a -> a
  removeT :: Dur -> a -> a

instance Temporal (Music a) where
  durT = dur
  cutT = cut
  removeT = remove

instance Temporal (Primitive a) where 
  durT (Note d _)         = d
  durT (Rest d)           = d
  cutT d (Note oldD p)    = Note (min oldD d) p
  cutT d (Rest oldD)      = Rest (min oldD d)
  removeT d (Note oldD p) = Note (max (oldD - d) 0) p
  removeT d (Rest oldD)   = Rest (max (oldD - d) 0)

{-
EXERCISE 7.4: Functions are not members of the Eq class, because, in general, 
determining whether two functions are equal is undecideable. But functions whose 
domains are finite and can be completely enumerated can be tested for equality. We 
just need to test that each function, when applied to each element in the domain, 
returns the same result.

Define an instance of Eq for functions. For this to be possible, note that if the 
function type is a -> b, then:

 a must be enumerable
 a must be bounded
 b must be a member of the Eq class

These constraints must there for be part of the instance declaration
-}

instance (Enum a, Bounded a, Eq b) => Eq (a -> b) where
  f == g = all (\x -> f x == g x) domain
               where domain = [minBound .. maxBound]

enumPC :: PitchClass -> Int
enumPC pc = fromEnum pc
 
enumPC2 :: PitchClass -> Int
enumPC2 = toEnum . fromEnum


  
     
    




     





























