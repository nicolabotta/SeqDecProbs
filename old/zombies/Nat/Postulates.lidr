> module Postulates

> import Data.So

> %default total

> -- postulate Sid_preserves_LT : So (S left < right) -> So (left < right)
> Sid_preserves_LT : So (S left < right) -> So (left < right)
> Sid_preserves_LT _ = believe_me Oh

> postulate injectiveS : {m : Nat} -> {n : Nat} -> So (S m == S n) -> So (m == n)
> -- injectiveS = believe_me Oh

> postulate injectiveS' : {m : Nat} -> {n : Nat} -> So (m /= n) -> So (S m /= S n)
> -- injectiveS' = believe_me Oh

> monotoneS : {m : Nat} -> {n : Nat} -> So (m < n) -> So (S m < S n)
> monotoneS mLTn = believe_me Oh

> postulate ZltSn : {n : Nat} -> So (Z < S n)
> -- ZltSn = believe_me Oh

> postulate lemma1 : {b : Nat} -> So (Z <= b)
> -- lemma1 = believe_me True

> postulate lemma2 : {a : Nat} -> {b : Nat} -> So (S a <= b) -> So (a <= b)
> -- lemma2 SaLTEb = believe_me Oh

> postulate lemma3 : {a : Nat} -> {b : Nat} -> So (a < b) -> So (S a <= b)
> -- lemma3 aLTb = believe_me Oh

> postulate lemma4 : {a : Nat} -> {b : Nat} -> So (S a <= b) -> So (a < b)
> -- lemma4 SaLTEb = believe_me Oh

> lemma5 : {a : Nat} -> {b : Nat} -> So (S a < S b) -> So (a < b)
> lemma5 SaLTSb = believe_me Oh

> lemma6 : {a : Nat} -> {b : Nat} -> So (a <= b) -> So (a < S b)
> lemma6 aLTEb = believe_me True

> lemma7 : {m : Nat} -> {n : Nat} -> So (m <= n) -> So (m /= n) -> So (m < n)
> lemma7 mLTEn mNEQn = believe_me True

TODO: there might be theorems in the prelude that can be used in place
of the above lemmas, check this


