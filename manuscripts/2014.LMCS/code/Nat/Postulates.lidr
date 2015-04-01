> module Postulates

> -- postulate Sid_preserves_LT : so (S left < right) -> so (left < right)
> Sid_preserves_LT : so (S left < right) -> so (left < right)
> Sid_preserves_LT _ = believe_me oh

> postulate injectiveS : {m : Nat} -> {n : Nat} -> so (S m == S n) -> so (m == n)
> -- injectiveS = believe_me oh

> postulate injectiveS' : {m : Nat} -> {n : Nat} -> so (m /= n) -> so (S m /= S n)
> -- injectiveS' = believe_me oh

> monotoneS : {m : Nat} -> {n : Nat} -> so (m < n) -> so (S m < S n)
> monotoneS mLTn = believe_me oh

> postulate ZltSn : {n : Nat} -> so (Z < S n)
> -- ZltSn = believe_me oh

> postulate lemma1 : {b : Nat} -> so (Z <= b)
> -- lemma1 = believe_me True

> postulate lemma2 : {a : Nat} -> {b : Nat} -> so (S a <= b) -> so (a <= b)
> -- lemma2 SaLTEb = believe_me oh

> postulate lemma3 : {a : Nat} -> {b : Nat} -> so (a < b) -> so (S a <= b)
> -- lemma3 aLTb = believe_me oh

> postulate lemma4 : {a : Nat} -> {b : Nat} -> so (S a <= b) -> so (a < b)
> -- lemma4 SaLTEb = believe_me oh

> lemma5 : {a : Nat} -> {b : Nat} -> so (S a < S b) -> so (a < b)
> lemma5 SaLTSb = believe_me oh

> lemma6 : {a : Nat} -> {b : Nat} -> so (a <= b) -> so (a < S b)
> lemma6 aLTEb = believe_me True

> lemma7 : {m : Nat} -> {n : Nat} -> so (m <= n) -> so (m /= n) -> so (m < n)
> lemma7 mLTEn mNEQn = believe_me True

TODO: there might be theorems in the prelude that can be used in place
of the above lemmas, check this


