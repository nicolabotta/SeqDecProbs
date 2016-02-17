> module NonNegQ

> -- import Data.Vect
> import Syntax.PreorderReasoning

> %default total

> -- %hide gcd

> ||| Any number which is smaller or equal zero is zero
> lteZeqZ : {n : Nat} -> LTE n Z -> n = Z
> lteZeqZ {n = Z}   _ = Refl
> lteZeqZ {n = S m} p = void (succNotLTEzero p)

> lteLemma1 : (m : Nat) -> (n : Nat) -> Not (LTE m n) -> LTE (S n) m
> lteLemma1  Z     Z    contra = void (contra LTEZero)
> lteLemma1  Z    (S n) contra = void (contra LTEZero)
> lteLemma1 (S m)  Z         _ = LTESucc LTEZero
> lteLemma1 (S m) (S n) contra = LTESucc (lteLemma1 m n contra') where
>   contra' : Not (LTE m n)
>   contra' = \ p => contra (LTESucc p)

> decLTE : (m : Nat) -> (n : Nat) -> Dec (LTE m n)
> decLTE Z _     = Yes LTEZero
> decLTE (S m) Z = No succNotLTEzero 
> decLTE (S m) (S n) with (decLTE m n)
>   | (Yes p) = Yes (LTESucc p)
>   | (No contra) = No (\ p => contra (fromLteSucc p))

> plusLemma1 : (m : Nat) -> (n : Nat) -> Not (m = Z) -> Not (n = Z) -> Not (m + n = Z)
> plusLemma1  Z     _    p q = void (p Refl) 
> plusLemma1  _     Z    p q = void (q Refl)
> plusLemma1 (S m) (S n) _ _ = SIsNotZ 

> multLemma1 : (m : Nat) -> (n : Nat) -> Not (m = Z) -> Not (n = Z) -> Not (m * n = Z)
> multLemma1  Z     _    p q = void (p Refl) 
> multLemma1  _     Z    p q = void (q Refl)
> multLemma1 (S m) (S n) _ _ = SIsNotZ 

> minusLemma1 : (m : Nat) -> (n : Nat) -> LTE m n -> m + (n - m) = n
> minusLemma1  Z       n  _ =
>     ( Z + (n - Z) )
>   ={ Refl }=
>     ( n - Z )
>   ={ minusZeroRight n }=
>     ( n           )
>   QED     
> minusLemma1    m   Z    p = 
>     ( m + (Z - m) )
>   ={ replace {x = m}
>              {y = Z}
>              {P = \ ZUZU => m + (Z - m) = ZUZU + (Z - ZUZU)}
>              (lteZeqZ p)
>              Refl }=
>     ( Z + (Z - Z) )
>   ={ Refl }=
>     ( Z           )
>   QED     
>     
> minusLemma1 (S m) (S n) (LTESucc p) = 
>     ( S m + (S n - S m) )
>   ={ Refl }=
>     ( S m + (n - m)     )
>   ={ Refl }=
>     ( S (m + (n - m))   )
>   ={ cong (minusLemma1 m n p) }=
>     ( S n               )
>   QED

> multZplusLemma1 : (m : Nat) -> (n : Nat) -> m * Z + n = n
> multZplusLemma1  Z    n = Refl
> multZplusLemma1 (S m) n = 
>     ( (S m) * Z + n )
>   ={ Refl }=
>     ( Z + m * Z + n )
>   ={ plusZeroLeftNeutral (m * Z + n) }=
>     ( m * Z + n     )
>   ={ multZplusLemma1 m n }=
>     ( n             )
>   QED

> divmod : Nat -> Nat -> Nat -> (Nat, Nat)
> divmod  Z       centre right = (Z, centre)
> divmod (S left) centre right with (decLTE centre right)
>   | Yes _ = (Z, centre)
>   | No  _ = (S (fst dm), (snd dm)) where
>       dm : (Nat, Nat)
>       dm = divmod left (centre - S right) right 

> divmodLemma1 : (left : Nat) -> (centre : Nat) -> (right : Nat) -> 
>                (S right) * (fst (divmod left centre right)) + snd (divmod left centre right) 
>                = 
>                centre
> divmodLemma1 Z centre right = 
>     ( (S right) * (fst (divmod Z centre right)) + snd (divmod Z centre right) )
>   ={ Refl }=
>     ( (S right) * (fst (Z, centre)) + snd (Z, centre)                         )
>   ={ Refl }=
>     ( (S right) * Z + centre                                                  )
>   ={ multZplusLemma1 (S right) centre }=
>     ( centre                                                                  )
>   QED
> divmodLemma1 (S left) centre right with (decLTE centre right)
>   | Yes _ = 
>         ( (S right) * (fst (Z, centre)) + snd (Z, centre) )
>       ={ Refl }=
>         ( (S right) * Z + centre                          )
>       ={ multZplusLemma1 (S right) centre }=
>         ( centre                                      )
>       QED
>   | No  contra =
>         ( (S right) * (S (fst (divmod left (centre - S right) right))) + snd (divmod left (centre - S right) right) )
>       ={ replace {a = Nat} 
>                  {x = (S right) * (S (fst (divmod left (centre - S right) right)))}
>                  {y = (S (fst (divmod left (centre - S right) right))) * (S right)}
>                  {P = \ ZUZU => (S right) * (S (fst (divmod left (centre - S right) right)))
>                                 + 
>                                 snd (divmod left (centre - S right) right)
>                                 =
>                                 ZUZU
>                                 +
>                                 snd (divmod left (centre - S right) right)}
>                  (multCommutative (S right) (S (fst (divmod left (centre - S right) right))))
>                  Refl }= 
>         ( (S (fst (divmod left (centre - S right) right))) * (S right) + snd (divmod left (centre - S right) right) )
>       ={ Refl }=
>         ( S right
>           +
>           (fst (divmod left (centre - S right) right)) * (S right) + snd (divmod left (centre - S right) right) )
>       ={ replace {a = Nat} 
>                  {x = (fst (divmod left (centre - S right) right)) * (S right)}
>                  {y = (S right) * (fst (divmod left (centre - S right) right))}
>                  {P = \ ZUZU => S right 
>                                 + 
>                                 (fst (divmod left (centre - S right) right)) * (S right) 
>                                 + 
>                                 snd (divmod left (centre - S right) right)
>                                 =
>                                 S right 
>                                 +
>                                 ZUZU
>                                 +
>                                 snd (divmod left (centre - S right) right)}
>                  (multCommutative (fst (divmod left (centre - S right) right)) (S right))
>                  Refl }= 
>         ( S right
>           +
>           (S right) * (fst (divmod left (centre - S right) right)) + snd (divmod left (centre - S right) right) )
>       {-
>       ={ replace {a = Nat}
>                  {x = (S right) * (fst (divmod left (centre - S right) right)) + 
>                                    snd (divmod left (centre - S right) right)}
>                  {y = (centre - S right)}
>                  {P = \ ZUZU => (S right)
>                                 +
>                                 (S right) * (fst (divmod left (centre - S right) right)) + 
>                                              snd (divmod left (centre - S right) right)
>                                 = 
>                                 (S right) 
>                                 + 
>                                 ZUZU}
>                  (divmodLemma1 left (centre - S right) right)
>                  Refl }=
>       ---}
>       ={ ?ZUZU }=
>         ( S right + (centre - S right)                                                                          )
>       ={ minusLemma1 (S right) centre (lteLemma1 centre right contra)}= 
>         ( centre )
>       QED

> divmodLemma2 : (m : Nat) -> (n : Nat) -> (S n) * (fst (divmod m m n)) + snd (divmod m m n) = m
> divmodLemma2 m n = divmodLemma1 m m n

> divmodNatNZ : (m : Nat) -> (n : Nat) -> Not (n = Z) -> (Nat, Nat)
> divmodNatNZ m  Z    p = void (p Refl)
> divmodNatNZ m (S n) p = divmod m m n 

> divNatNZ : (m : Nat) -> (n : Nat) -> Not (n = Z) -> Nat
> divNatNZ m n nnZ = fst (divmodNatNZ m n nnZ)

> modNatNZ : (m : Nat) -> (n : Nat) -> Not (n = Z) -> Nat
> modNatNZ m n nnZ = snd (divmodNatNZ m n nnZ)

> divmodNatNZLemma : (m : Nat) -> (n : Nat) -> (p : Not (n = Z)) -> 
>                    n * (NonNegQ.divNatNZ m n p) + NonNegQ.modNatNZ m n p = m
> divmodNatNZLemma m  Z    p = void (p Refl)
> divmodNatNZLemma m (S n) p = 
>     ( (S n) * (NonNegQ.divNatNZ m (S n) p) + NonNegQ.modNatNZ m (S n) p   )
>   ={ Refl }=
>     ( (S n) * (fst (divmodNatNZ m (S n) p)) + snd (divmodNatNZ m (S n) p) )
>   ={ Refl }=
>     ( (S n) * (fst (divmodNatNZ m (S n) p)) + snd (divmodNatNZ m (S n) p) )
>   ={ Refl }=
>     ( (S n) * (fst (divmod m m n)) + snd (divmod m m n)                   )
>   ={ divmodLemma2 m n }=
>     ( m                                                                   )
>   QED

> gcd : Nat -> Nat -> Nat 
> gcd m  Z    = m 
> gcd m (S n) = assert_total (NonNegQ.gcd (S n) (NonNegQ.modNatNZ m (S n) SIsNotZ))

> Divisor : (m : Nat) -> (n : Nat) -> Not (m = Z) -> Type
> Divisor m n nmZ = NonNegQ.modNatNZ n m nmZ = Z 

> divNatNZLemma1 : (m : Nat) -> (n : Nat) ->
>                  (nmZ : Not (m = Z)) -> (nnZ : Not (n = Z)) -> Divisor n m nnZ ->
>                  Not (NonNegQ.divNatNZ m n nnZ = Z)  

> gcdLemma1 : (m : Nat) -> (n : Nat) -> Not (m = Z) -> Not (n = Z) -> Not (NonNegQ.gcd m n = Z)

> -- gcdLemma2 : (m : Nat) -> (n : Nat) -> (p : Not (gcd m n = Z)) -> Divisor (gcd m n) m p

> gcdLemma3 : (m : Nat) -> (n : Nat) -> (p : Not (gcd m n = Z)) -> Divisor (NonNegQ.gcd m n) n p

> Coprime : Nat -> Nat -> Type
> Coprime m n = NonNegQ.gcd m n = S Z

> gcdLemma4 : (m : Nat) -> (n : Nat) -> (nmZ : Not (m = Z)) -> (nnZ : Not (n = Z)) -> 
>             Coprime (NonNegQ.divNatNZ m (gcd m n) (gcdLemma1 m n nmZ nnZ)) 
>                     (NonNegQ.divNatNZ n (gcd m n) (gcdLemma1 m n nmZ nnZ))


Non-negative rational numbers:

> data NonNegQ  :  Type where
>   MkNonNegQ  :  (m : Nat) -> (n : Nat) -> Not (n = Z) -> Coprime m n -> NonNegQ

> plusNonNegQ : NonNegQ -> NonNegQ -> NonNegQ
> plusNonNegQ r (MkNonNegQ Z n2 p2 q2) = r
> plusNonNegQ (MkNonNegQ Z n1 p1 q1) s = s
> plusNonNegQ (MkNonNegQ (S m1) n1 p1 q1) (MkNonNegQ (S m2) n2 p2 q2) = MkNonNegQ m n p q where
>   n'     : Nat
>   n'     = n1 * n2
>   nn'Z   : Not (n' = Z)
>   nn'Z   = multLemma1 n1 n2 p1 p2
>   m'     : Nat
>   m'     = (S m1) * n2 + (S m2) * n1
>   nm'Z   : Not (m' = Z)
>   nm'Z   = plusLemma1 ((S m1) * n2) ((S m2) * n1) (multLemma1 (S m1) n2 SIsNotZ p2) (multLemma1 (S m2) n1 SIsNotZ p1)
>   gcd'   : Nat
>   gcd'   = NonNegQ.gcd m' n'
>   ngcd'Z : Not (gcd' = Z)
>   ngcd'Z = gcdLemma1 m' n' nm'Z nn'Z
>   m      : Nat
>   m      = NonNegQ.divNatNZ m' gcd' ngcd'Z
>   n      : Nat
>   n      = NonNegQ.divNatNZ n' gcd' ngcd'Z
>   p      : Not (n = Z)
>   p      = divNatNZLemma1 n' gcd' nn'Z ngcd'Z (gcdLemma3 m' n' ngcd'Z)
>   q      : Coprime m n
>   q      = gcdLemma4 m' n' nm'Z nn'Z

> {-

> prod : (Num t) => Vect m t -> Vect m (Vect n t) -> Vect m (Vect n t)
> prod  Nil       _          = Nil
> prod (x :: xs) (ys :: yss) = (map ((*) x) ys) :: prod xs yss

> v : Vect 3 Nat
> v = [0,2,3]

> m : Vect 3 (Vect 2 Nat)
> m = [[1,2],[3,4],[5,6]]

> -}


--

> --{-



> instance Show NonNegQ where
>   show (MkNonNegQ m n p q) = "frac " ++ show m ++ " " ++ show n

> numerator : NonNegQ -> Nat
> numerator (MkNonNegQ m n p q) = m

> denominator : NonNegQ -> Nat
> denominator (MkNonNegQ m n p q) = n

> gcdLemma1 m  Z    p q h = p h
> gcdLemma1 m (S n) p q h with (decEq (NonNegQ.modNatNZ m (S n) SIsNotZ) Z)
>   gcdLemma1 m (S n) p q h | (Yes prf)   = res h where
>                              s1  : NonNegQ.gcd m (S n) = NonNegQ.gcd (S n) (NonNegQ.modNatNZ m (S n) SIsNotZ)
>                              s1  = Refl
>                              s2  : NonNegQ.gcd m (S n) = NonNegQ.gcd (S n) Z
>                              s2  = replace {P = \ z => NonNegQ.gcd m (S n) = NonNegQ.gcd (S n) z} prf s1
>                              s3  : NonNegQ.gcd (S n) Z = S n
>                              s3  = Refl
>                              s4  : NonNegQ.gcd m (S n) = S n
>                              s4  = trans s2 s3
>                              res : Not (NonNegQ.gcd m (S n) = Z)
>                              res = \ k => SIsNotZ (trans (sym s4) k)
>   gcdLemma1 m (S n) p q h | (No contra) = res h where
>                              m' : Nat
>                              m' = S n
>                              n' : Nat
>                              n' = NonNegQ.modNatNZ m (S n) SIsNotZ
>                              p' : Not (m' = Z)
>                              p' = SIsNotZ
>                              q' : Not (n' = Z)
>                              q' = contra
>                              res : Not (NonNegQ.gcd (S n) (NonNegQ.modNatNZ m (S n) SIsNotZ) = Z)
>                              res = assert_total (gcdLemma1 m' n' p' q')

> ---}
