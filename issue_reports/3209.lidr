> import Syntax.PreorderReasoning
> %default total
> multDistributesOverPlusRightEq : {x, y, z : Fraction} -> x * (y + z) `Eq` (x * y) + (x * z)
> multDistributesOverPlusRightEq {x = (m, d')} {y = (n, e')} {z = (o, f')} = 
>   let d       =  toNat d' in
>   let e       =  toNat e' in
>   let f       =  toNat f' in
>     ( (m * (n * f + o * e)) * (toNat ((d' * e') * (d' * f'))) )
>   ={ cong {f = \ ZUZU => (m * (n * f + o * e)) * ZUZU} toNatMultLemma }=
>     ( (m * (n * f + o * e)) * ((toNat (d' * e')) * (toNat (d' * f'))) )
>   ={ cong {f = \ ZUZU => (m * (n * f + o * e)) * (ZUZU * (toNat (d' * f')))} toNatMultLemma }=
>     ( (m * (n * f + o * e)) * ((d * e) * (toNat (d' * f'))) )  
>   ={ cong {f = \ ZUZU => (m * (n * f + o * e)) * ((d * e) * ZUZU)} toNatMultLemma }=
>     ( (m * (n * f + o * e)) * ((d * e) * (d * f)) )  
>   ={ cong {f = \ ZUZU => (m * (n * f + o * e)) * ZUZU} (multFlipCentre d e d f) }=
>     ( (m * (n * f + o * e)) * ((d * d) * (e * f)) )  
>   ={ cong {f = \ ZUZU => (m * (n * f + o * e)) * ZUZU} (sym (multAssociative d d (e * f))) }=
>     ( (m * (n * f + o * e)) * (d * (d * (e * f))) )  
>   ={ multAssociative (m * (n * f + o * e)) d (d * (e * f)) }=
>     ( ((m * (n * f + o * e)) * d) * (d * (e * f)) )  
>   ={ cong {f = \ ZUZU => (ZUZU * d) * (d * (e * f))} (multDistributesOverPlusRight m (n * f) (o * e)) }=
>     ( ((m * (n * f) + m * (o * e)) * d) * (d * (e * f)) )
>   ={ cong {f = \ ZUZU => ((ZUZU + m * (o * e)) * d) * (d * (e * f))} (multAssociative m n f) }=
>     ( (((m * n) * f + m * (o * e)) * d) * (d * (e * f)) )
>   ={ cong {f = \ ZUZU => (((m * n) * f + ZUZU) * d) * (d * (e * f))} (multAssociative m o e) }=  
>     ( (((m * n) * f + (m * o) * e) * d) * (d * (e * f)) )
>   ={ cong {f = \ ZUZU => ZUZU * (d * (e * f))} (multDistributesOverPlusLeft ((m * n) * f) ((m * o) * e) d)}=  
>     ( (((m * n) * f) * d + ((m * o) * e) * d) * (d * (e * f)) )
>   ={ cong {f = \ ZUZU => (ZUZU + ((m * o) * e) * d) * (d * (e * f))} (sym (multAssociative (m * n) f d)) }=
>     ( ((m * n) * (f * d) + ((m * o) * e) * d) * (d * (e * f)) )
>   ={ cong {f = \ ZUZU => ((m * n) * (f * d) + ZUZU) * (d * (e * f))} (sym (multAssociative (m * o) e d)) }=  
>     ( ((m * n) * (f * d) + (m * o) * (e * d)) * (d * (e * f)) )
>   ={ cong {f = \ ZUZU => ((m * n) * (f * d) + (m * o) * ZUZU) * (d * (e * f))} (multCommutative e d) }=
>     ( ((m * n) * (f * d) + (m * o) * (d * e)) * (d * (e * f)) )
>   ={ cong {f = \ ZUZU => ((m * n) * ZUZU + (m * o) * (d * e)) * (d * (e * f))} (multCommutative f d) }=
>     ( ((m * n) * (d * f) + (m * o) * (d * e)) * (d * (e * f)) )
>   ={ cong {f = \ ZUZU => ((m * n) * (d * f) + (m * o) * (d * e)) * (d * ZUZU)} (sym toNatMultLemma) }=  
>     ( ((m * n) * (d * f) + (m * o) * (d * e)) * (d * (toNat (e' * f'))) )
>   ={ cong {f = \ ZUZU => ((m * n) * (d * f) + (m * o) * (d * e)) * ZUZU}  (sym toNatMultLemma) }=  
>     ( ((m * n) * (d * f) + (m * o) * (d * e)) * (toNat (d' * (e' * f'))) )
>   ={ cong {f = \ ZUZU => ((m * n) * (d * f) + (m * o) * ZUZU) * (toNat (d' * (e' * f')))} 
>            (sym toNatMultLemma) }=
>     ( ((m * n) * (d * f) + (m * o) * (toNat (d' * e'))) * (toNat (d' * (e' * f'))) )
>   ={ cong {f = \ ZUZU => ((m * n) * ZUZU + (m * o) * (toNat (d' * e'))) * (toNat (d' * (e' * f')))} 
>            (sym toNatMultLemma) }=
>     ( ((m * n) * (toNat (d' * f')) + (m * o) * (toNat (d' * e'))) * (toNat (d' * (e' * f'))) )
>   QED


