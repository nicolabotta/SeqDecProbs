module Main

import Effect.State
import Effect.StdIO
import Effect.Exception
import Effect.Random

data Ty = TyInt | TyBool | TyUnit | TyFun Ty Ty

interpTy : Ty -> Type
interpTy TyInt       = Int
interpTy TyBool      = Bool
interpTy TyUnit      = ()
interpTy (TyFun s t) = interpTy s -> interpTy t

using (G : Vect Ty n)

  data Env : Vect Ty n -> Type where
      Nil  : Env Nil
      (::) : interpTy a -> Env G -> Env (a :: G)

  data HasType : (i : Fin n) -> Vect Ty n -> Ty -> Type where
      stop : HasType fO (t :: G) t
      pop  : HasType k G t -> HasType (fS k) (u :: G) t

  lookup : HasType i G t -> Env G -> interpTy t
  lookup stop    (x :: xs) = x
  lookup (pop k) (x :: xs) = lookup k xs

  update : HasType i G t -> Env G -> interpTy t -> Env G
  update stop    (x :: xs) y = y :: xs 
  update (pop k) (x :: xs) y = x :: update k xs y
  
  data Expr : Vect Ty n -> Ty -> Type where
     Val : interpTy a -> Expr G a
     Var : HasType i G t -> Expr G t
     Rnd : Expr G TyInt -> Expr G TyInt
     Op  : (interpTy a -> interpTy b -> interpTy c) ->
            Expr G a -> Expr G b -> Expr G c

  (+) : Expr G TyInt -> Expr G TyInt -> Expr G TyInt
  (+) = Op (+)

  (<) : Expr G TyInt -> Expr G TyInt -> Expr G TyBool
  (<) = Op (<)

  eval : Expr G t -> Eff m [RND, STATE (Env G)] (interpTy t)
  eval (Val x) = return x
  eval (Var i) = do env <- get
                    return (lookup i env) 
  eval (Rnd upper) = do r <- eval upper
                        rndInt 0 r
  eval (Op op x y) = [| op (eval x) (eval y) |]

  fromInteger : Int -> Expr G TyInt
  fromInteger = Val

  implicit MkVar : HasType i G t -> Expr G t
  MkVar = Var

  infix 5 :=

  data Imp    : Vect Ty n -> Ty -> Type where
       Let    : Expr G t -> Imp (t :: G) u -> Imp G u
       (:=)   : HasType i G t -> Expr G t -> Imp G t
       Print  : Expr G TyInt -> Imp G TyUnit
 
       For    : Imp G i -> -- initialise
                Imp G TyBool -> -- test
                Imp G x -> -- increment
                Imp G t -> -- body
                Imp G TyUnit

       (>>=)  : Imp G a -> (interpTy a -> Imp G b) -> Imp G b 
       Return : Expr G t -> Imp G t
    
 
  implicit Ret : Expr G t -> Imp G t
  Ret = Return


  interp : Imp G t -> Eff IO [STDIO, RND, STATE (Env G)] (interpTy t)
  interp (Let e sc) 
       = do e' <- eval e
            env <- get
            putM (e' :: env)
            res <- interp sc
            (_ :: env') <- get
            putM env'
            return res
  interp (v := val) 
       = do val' <- eval val
            update (\env => update v env val')
            return val'
  interp (Print x) 
       = do e <- eval x
            putStrLn (show e)
  interp (For init test inc body)
       = do interp init; forLoop 
    where forLoop = do tval <- interp test
                       if (not tval) then return ()
                              else do interp body
                                      interp inc
                                      forLoop 
  interp (prog >>= k)
       = do res <- interp prog
            interp (k res)
  interp (Return v) = eval v
 
  dsl imp
       let = Let
       variable = id
       index_first = stop
       index_next = pop

small : Imp [] TyUnit
small = Let (Val 42) (do Print (Var stop)
                         stop := Op (+) (Var stop) 1
                         Print (Var stop))

count : Imp [] TyUnit
count = imp (do let x = 0
                For (x := 0) (x < 10) (x := x + 1)
                    (do Print (x + 1)
                        Print (Rnd (x + 1))))

main : IO ()
main = run [(), 5678, Main.Nil] (interp count)
