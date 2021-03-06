
module Agda.TypeChecking.Records where

import Agda.Syntax.Internal
-- import Agda.Syntax.Abstract.Name
import qualified Agda.Syntax.Concrete.Name as C
import Agda.TypeChecking.Monad

isRecord :: HasConstInfo m => QName -> m (Maybe Defn)
isEtaRecord :: HasConstInfo m => QName -> m Bool
getRecordFieldNames :: QName -> TCM [Arg C.Name]
etaContractRecord :: HasConstInfo m => QName -> ConHead -> Args -> m Term
isGeneratedRecordConstructor :: QName -> TCM Bool
