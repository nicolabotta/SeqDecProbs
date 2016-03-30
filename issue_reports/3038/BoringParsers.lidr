> module BoringParsers

> %access export

> public export
> A : Type

> public export
> ParserA : Type
> ParserA = List Char -> Either String (A, List Char)

> public export
> Parser : Type
> Parser = List Char -> Either String ((), List Char)

> skipWhile : (Char -> Bool) -> Parser
> skipWhile p [] = Right ((), [])
> skipWhile p (c :: cs) =
>   if p c then skipWhile p cs else Right ((), c :: cs)

> -- wtf: why a
> lexeme : ParserA -> ParserA
> lexeme     p cs = do (val, rest) <- p cs
>                      (_, rest') <- skipWhile (\x => x == ' ' || x == '\t' || x == '\n' || x == '\r') rest
>                      return (val, rest')
