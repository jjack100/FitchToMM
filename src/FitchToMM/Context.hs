module FitchToMM.Context where
import FitchToMM.Parser (Wff)

data Context
  = AbsContext {ctxWffs :: [Wff]}
  | RelContext {ctxWffs :: [Wff]}
  deriving (Show, Eq, Ord)

unconsCtx :: Context -> Maybe (Wff, Context)
unconsCtx (AbsContext []) = Nothing
unconsCtx (AbsContext (wff : rest)) = Just (wff, AbsContext rest)
unconsCtx (RelContext []) = Nothing
unconsCtx (RelContext (wff : rest)) = Just (wff, RelContext rest)

nullCtx :: Context -> Bool
nullCtx = null . ctxWffs

-- Push a new assumption to the context stack
assume :: Context -> Wff -> Context
assume (RelContext ctx) assumption = RelContext $ assumption : ctx
assume (AbsContext ctx) assumption = AbsContext $ assumption : ctx