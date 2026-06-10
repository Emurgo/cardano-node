module Cardano.ReCon.LTL.ContinuousFormula (
    ContinuousFormula(..)
  , retract
  , interp
  , eval) where

import           Cardano.ReCon.Common.Types (BinRel (..), IntValue, VariableIdentifier)
import           Cardano.ReCon.Integer.Polynomial.Term (IntTerm (..))
import           Cardano.ReCon.LTL.Formula (Event (..), Formula, OnMissingKey (..), PropConstraint (..),
                   TextTerm, TextValue)
import qualified Cardano.ReCon.LTL.Formula as F
import           Cardano.ReCon.LTL.Internal.IR.HomogeneousFormula (HomogeneousFormula)
import qualified Cardano.ReCon.LTL.Internal.IR.HomogeneousFormula as H

import           Control.Monad.Reader (Reader, asks)
import           Data.Map.Strict (lookup)
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as Text
import           Prelude hiding (lookup)

-- | Default name: φ.
--
--   The continuous counterpart of 'Formula': all temporal connectives are
--   absent.  A 'ContinuousFormula' is evaluated against a /single/ event
--   (or time unit) rather than a sequence, making it a purely propositional /
--   first-order assertion about the present moment.
data ContinuousFormula ty =

   -------------- Atomic ---------------
     -- | ty c̄
     Atom ty (Set PropConstraint)
   -------------------------------------

   ------------ Connective -------------
     -- | φ ∨ ψ
   | Or (ContinuousFormula ty) (ContinuousFormula ty)
     -- | φ ∧ ψ
   | And (ContinuousFormula ty) (ContinuousFormula ty)
     -- | ¬ φ
   | Not (ContinuousFormula ty)
     -- | φ ⇒ ψ
   | Implies (ContinuousFormula ty) (ContinuousFormula ty)
     -- | ⊤
   | Top
     -- | ⊥
   | Bottom
   -------------------------------------

   ----------- Event property ----------
     -- | ∀x ∈ ℤ. φ  —  x ranges over all integers
   | PropIntForall  VariableIdentifier (ContinuousFormula ty)
     -- | ∀x ∈ Text. φ  —  x ranges over all strings
   | PropTextForall VariableIdentifier (ContinuousFormula ty)
     -- | ∀x ∈ v̄. φ  —  x ranges over the given integers
   | PropIntForallN  VariableIdentifier (Set IntValue)  (ContinuousFormula ty)
     -- | ∀x ∈ v̄. φ  —  x ranges over the given strings
   | PropTextForallN VariableIdentifier (Set TextValue) (ContinuousFormula ty)
     -- | ∃x ∈ ℤ. φ  —  x ranges over all integers
   | PropIntExists  VariableIdentifier (ContinuousFormula ty)
     -- | ∃x ∈ Text. φ  —  x ranges over all strings
   | PropTextExists VariableIdentifier (ContinuousFormula ty)
     -- | ∃x ∈ v̄. φ  —  x ranges over the given integers
   | PropIntExistsN  VariableIdentifier (Set IntValue)  (ContinuousFormula ty)
     -- | ∃x ∈ v̄. φ  —  x ranges over the given strings
   | PropTextExistsN VariableIdentifier (Set TextValue) (ContinuousFormula ty)
     -- | t rel t  (integer)
   | PropIntBinRel BinRel IntTerm IntTerm
     -- | t = v  (text)
   | PropTextEq TextTerm TextValue
   -------------------------------------
   deriving (Show, Eq, Ord)

-- | Retract a 'Formula' into a 'ContinuousFormula', returning 'Nothing' if
--   the formula contains any temporal connective.
retract :: Formula event ty -> Maybe (ContinuousFormula ty)
retract (F.Forall {})            = Nothing
retract (F.ForallN {})           = Nothing
retract (F.ExistsN {})           = Nothing
retract (F.Next {})              = Nothing
retract (F.NextN {})             = Nothing
retract (F.UntilN {})            = Nothing
retract (F.Atom ty cs)           = Just (Atom ty cs)
retract (F.Or phi psi)           = Or      <$> retract phi <*> retract psi
retract (F.And phi psi)          = And     <$> retract phi <*> retract psi
retract (F.Not phi)              = Not     <$> retract phi
retract (F.Implies phi psi)      = Implies <$> retract phi <*> retract psi
retract F.Top                    = Just Top
retract F.Bottom                 = Just Bottom
retract (F.PropIntForall  x phi)        = PropIntForall  x     <$> retract phi
retract (F.PropTextForall x phi)        = PropTextForall x     <$> retract phi
retract (F.PropIntForallN  x dom phi)   = PropIntForallN  x dom <$> retract phi
retract (F.PropTextForallN x dom phi)   = PropTextForallN x dom <$> retract phi
retract (F.PropIntExists  x phi)        = PropIntExists  x     <$> retract phi
retract (F.PropTextExists x phi)        = PropTextExists x     <$> retract phi
retract (F.PropIntExistsN  x dom phi)   = PropIntExistsN  x dom <$> retract phi
retract (F.PropTextExistsN x dom phi)   = PropTextExistsN x dom <$> retract phi
retract (F.PropIntBinRel rel _ t1 t2)   = Just (PropIntBinRel rel t1 t2)
retract (F.PropTextEq _ t v)            = Just (PropTextEq t v)

-- | Decide (e ⊧ φ).
eval :: (Event event ty, Eq ty) => ContinuousFormula ty -> event -> Reader OnMissingKey Bool
eval phi e = H.eval <$> interp phi e

-- | Algorithm for (e ⊧ φ): checks each 'Atom' against the event type and
--   substitutes property constraints with the event's concrete values,
--   yielding a 'HomogeneousFormula' ready for decision.
interp :: (Event event ty, Eq ty) => ContinuousFormula ty -> event -> Reader OnMissingKey HomogeneousFormula
interp phi e = go phi
  where
    go (Atom ty cs)
      | ofTy e ty = foldr H.And H.Top <$> traverse (evalConstraint ty) (Set.toList cs)
      | otherwise = pure H.Bottom
    go (Or phi' psi)      = H.Or      <$> go phi' <*> go psi
    go (And phi' psi)     = H.And     <$> go phi' <*> go psi
    go (Not phi')         = H.Not     <$> go phi'
    go (Implies phi' psi) = H.Implies <$> go phi' <*> go psi
    go Top                = pure H.Top
    go Bottom             = pure H.Bottom
    go (PropIntForall  x phi')       = H.PropIntForall  x <$> go phi'
    go (PropTextForall x phi')       = H.PropTextForall x <$> go phi'
    go (PropIntForallN  x dom phi')  = H.PropIntForallN  x dom <$> go phi'
    go (PropTextForallN x dom phi')  = H.PropTextForallN x dom <$> go phi'
    go (PropIntExists  x phi')       = H.PropIntExists  x <$> go phi'
    go (PropTextExists x phi')       = H.PropTextExists x <$> go phi'
    go (PropIntExistsN  x dom phi')  = H.PropIntExistsN  x dom <$> go phi'
    go (PropTextExistsN x dom phi')  = H.PropTextExistsN x dom <$> go phi'
    go (PropIntBinRel rel t1 t2)     = pure $ H.PropIntBinRel rel t1 t2
    go (PropTextEq t v)              = pure $ H.PropTextEq t v

    evalConstraint ty (IntPropConstraint key t) =
      case lookup key (intProps e ty) of
        Just v  -> pure $ H.PropIntBinRel Eq t (IntConst v)
        Nothing -> missingKey key
    evalConstraint ty (TextPropConstraint key t) =
      case lookup key (textProps e ty) of
        Just v  -> pure $ H.PropTextEq t v
        Nothing -> missingKey key

    missingKey key = asks $ \case
      BottomOnMissingKey -> H.Bottom
      CrashOnMissingKey  -> error $ "Missing key: " <> Text.unpack key
