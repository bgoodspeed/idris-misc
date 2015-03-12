module Homomorphism

import Syntax.PreorderReasoning

--Thanks to David Christiansen from the Idris mailing list for fixing this.

data Hom : (a, b : Type) -> Semigroup a -> Semigroup b -> Type where
  MkHom : (actxt : Semigroup a, bctxt : Semigroup b) => (h : a -> b) -> 
          (preservesGroup : (a1 : a) -> (a2 : a) -> h ((<+>) @{actxt} a1 a2) = (<+>) @{bctxt} (h a1) (h a2)) -> Hom a b actxt bctxt


homRefl : (as : Semigroup a) => Hom a a as as
homRefl = MkHom id (\x,y => Refl) 

homTrans : (adict : Semigroup a, bdict : Semigroup b, cdict : Semigroup c) =>
           Hom a b adict bdict -> Hom b c bdict cdict -> Hom a c adict cdict
homTrans @{adict} @{bdict} @{cdict} (MkHom h preservesGroup) (MkHom h' preservesGroup') =
  MkHom @{adict} @{cdict} (\x => h' (h x)) 
                          (\something, another =>
                            (h' (h (something <+> another))) ={ ?prf1 }=
                            (h' (h something <+> h another)) ={ ?prf2 }=
                            (h' (h something) <+> h' (h another)) QED)


data MonoidHom : (a, b : Type) -> Semigroup a -> Semigroup b -> Monoid a -> Monoid b -> Type where
  MkMonoidHom : (actxt : Semigroup a, bctxt : Semigroup b, actxtM : Monoid a, bctxtM : Monoid b) => 
                (h : a -> b) ->
                (preservesGroup : (a1 : a) -> (a2 : a) -> h ((<+>) @{actxt} a1 a2) = (<+>) @{bctxt} (h a1) (h a2)) -> 
                (preservesNeutral : h (neutral @{actxtM}) = neutral @{bctxtM}) ->
                MonoidHom a b actxt bctxt actxtM bctxtM


monoidHomRefl : (as : Semigroup a, am : Monoid a) => MonoidHom a a as as am am
monoidHomRefl = MkMonoidHom id (\x,y => Refl) Refl

--MkMonoidHom @{actxt} @{cctxt} @{am} @{cm} (\x => h' (h x)) (\p,q => ?preservesGroupPf) ?preservesNeutralPf
monoidHomTrans : (as : Semigroup a, bs : Semigroup b, cs : Semigroup c, am : Monoid a, bm : Monoid b, cm : Monoid c) => 
                 MonoidHom a b as bs am bm -> MonoidHom b c bs cs bm cm -> MonoidHom a c as cs am cm
monoidHomTrans @{actxt} @{bctxt} @{cctxt} @{am} @{bm} @{cm} (MkMonoidHom h preservesGroup preservesNeutral) (MkMonoidHom h' preservesGroup' preservesNeutral') = 
  MkMonoidHom @{actxt} @{cctxt} @{am} @{cm} (\x => h' (h x)) 
                         (\p,q =>
                                (h' (h ((<+>) @{actxt} p q)))           ={ cong $ preservesGroup p q }=
                                (h' ((<+>) @{bctxt} (h p) (h q)))       ={ preservesGroup' (h p) (h q) }=
                                ((<+>) @{cctxt}  (h' (h p)) (h' (h q))) QED)
                         ?monoidIdentProof
                         
---------- Proofs ----------

Homomorphism.monoidIdentProof = proof
  intros
  compute
  rewrite sym preservesNeutral
  rewrite sym preservesNeutral'
  trivial


Homomorphism.prf2 = proof
  intros
  rewrite preservesGroup' (h something) (h another)
  trivial


Homomorphism.prf1 = proof
  intros
  rewrite preservesGroup something another 
  trivial


