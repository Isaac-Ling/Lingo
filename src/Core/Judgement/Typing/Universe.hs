module Core.Judgement.Typing.Universe where

import Core.Term
import Core.Error
import Core.Judgement.Utils
import Core.Judgement.Context
import Core.Judgement.Evaluation
import Core.Judgement.Typing.Inference

checkUnivConstraintsSatisfiable :: UnivConstraints -> CanError ()
checkUnivConstraintsSatisfiable csts = case csts of
  [] -> return ()
  _  -> return ()
