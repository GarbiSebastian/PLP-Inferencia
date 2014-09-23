module TypeInference (TypingJudgment, Result(..), inferType)

where

import Data.List(intersect)
import Exp
import Type
import Unification

------------
-- Errors --
------------
data Result a = OK a | Error String


--------------------
-- Type Inference --
--------------------
type TypingJudgment = (Env, AnnotExp, Type)


inferType :: PlainExp -> Result TypingJudgment
inferType e = case infer' e 0 of
    OK (_, tj) -> OK tj
    Error s -> Error s


infer' :: PlainExp -> Int -> Result (Int, TypingJudgment)
infer' (VarExp x)  n = OK (n+1, (extendE emptyEnv x (TVar n),VarExp x,TVar n))
infer' (ZeroExp)   n = OK (n, (emptyEnv, ZeroExp, TNat))
infer' (TrueExp)   n = OK (n, (emptyEnv, TrueExp, TBool))
infer' (FalseExp)  n = OK (n, (emptyEnv, FalseExp, TBool))
infer' (SuccExp e) n = case infer' e  n of
						OK (n' , (env',e',t')) -> 
							case mgu [ (t', TNat) ] of
								UOK subst -> 
									OK (n', (
										subst <.> env',
										subst <.> SuccExp e',
										TNat
										))
								UError t1 t2 -> 
									uError t1 t2
						Error s ->
							Error s
infer' (PredExp e) n = case infer' e  n of
						OK (n' , (env',e',t')) -> 
							case mgu [ (t', TNat) ] of
								UOK subst -> 
									OK (n', (
										subst <.> env',
										subst <.> PredExp e',
										TNat
										))
								UError t1 t2 -> 
									uError t1 t2
						Error s ->
							Error s
infer' (IsZeroExp e) n = case infer' e  n of
						OK (n' , (env',e',t')) -> 
							case mgu [ (t', TNat) ] of
								UOK subst -> 
									OK (n', (
										subst <.> env',
										subst <.> IsZeroExp e',
										TBool
										))
								UError t1 t2 -> 
									uError t1 t2
						Error s ->
							Error s







--------------------------------
-- YAPA: Error de unificacion --
--------------------------------
uError :: Type -> Type -> Result (Int, a)
uError t1 t2 = Error $ "Cannot unify " ++ show t1 ++ " and " ++ show t2
