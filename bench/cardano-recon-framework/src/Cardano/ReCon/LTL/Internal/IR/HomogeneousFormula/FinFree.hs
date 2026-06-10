module Cardano.ReCon.LTL.Internal.IR.HomogeneousFormula.FinFree (
    FinFree(..)
  , Extended(..)
  , substInt
  , substText
  , lower
  , eval
  ) where

import           Cardano.ReCon.Common.Types (BinRel (..))
import           Cardano.ReCon.LTL.Formula (IntTerm (..), IntValue, TextTerm (..), VariableIdentifier)
import           Cardano.ReCon.LTL.Internal.Subst (substIntTerm)
import qualified Cardano.ReCon.Presburger.Decide as PD
import qualified Cardano.ReCon.Presburger.Formula as P

import           Data.Functor ((<&>))
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text)

-- | An extended value: either a concrete value or a placeholder distinct from all concrete values.
data Extended a = Val a | Placeholder deriving (Show, Ord, Eq)

-- | `HomogeneousFormula` with all finite-domain quantifiers already eliminated.
--   Only infinite-domain (unbounded) quantifiers remain.
data FinFree =
   ------------ Connective -------------
     Or FinFree FinFree
   | And FinFree FinFree
   | Not FinFree
   | Implies FinFree FinFree
   | Top
   | Bottom
   -------------------------------------

   ----------- Event property ----------
   | PropIntForall  VariableIdentifier FinFree
   | PropTextForall VariableIdentifier FinFree
   | PropIntExists  VariableIdentifier FinFree
   | PropTextExists VariableIdentifier FinFree
   | PropIntBinRel BinRel IntTerm  IntTerm
   | PropTextEq    TextTerm  Text
   deriving (Show, Eq, Ord)
   -------------------------------------

-- ---------------------------------------------------------------------------
-- Value accumulation (used by lower to eliminate text quantifiers)
-- ---------------------------------------------------------------------------

textValuesAccum :: Set Text -> VariableIdentifier -> FinFree -> Set Text
textValuesAccum acc x (Or phi psi)      = textValuesAccum (textValuesAccum acc x phi) x psi
textValuesAccum acc x (And phi psi)     = textValuesAccum (textValuesAccum acc x phi) x psi
textValuesAccum acc x (Not phi)         = textValuesAccum acc x phi
textValuesAccum acc x (Implies phi psi) = textValuesAccum (textValuesAccum acc x phi) x psi
textValuesAccum acc _ Top               = acc
textValuesAccum acc _ Bottom            = acc
textValuesAccum acc _ (PropIntBinRel {})                    = acc
textValuesAccum acc _ (PropTextEq (TextConst _) _)         = acc
textValuesAccum acc x (PropTextEq (TextVar x') v) | x == x' = Set.insert v acc
textValuesAccum acc _ (PropTextEq (TextVar _) _)           = acc
textValuesAccum acc x (PropIntForall  x' phi) | x /= x' = textValuesAccum acc x phi
textValuesAccum acc _ (PropIntForall  _ _)               = acc
textValuesAccum acc x (PropTextForall x' phi) | x /= x' = textValuesAccum acc x phi
textValuesAccum acc _ (PropTextForall _ _)               = acc
textValuesAccum acc x (PropIntExists  x' phi) | x /= x' = textValuesAccum acc x phi
textValuesAccum acc _ (PropIntExists  _ _)               = acc
textValuesAccum acc x (PropTextExists x' phi) | x /= x' = textValuesAccum acc x phi
textValuesAccum acc _ (PropTextExists _ _)               = acc

textValues :: VariableIdentifier -> FinFree -> Set Text
textValues = textValuesAccum Set.empty

-- ---------------------------------------------------------------------------
-- Capture-avoiding substitution
-- ---------------------------------------------------------------------------

-- | φ[v / x]  (integer substitution)
substInt :: IntValue -> VariableIdentifier -> FinFree -> FinFree
substInt v x (And phi psi)     = And (substInt v x phi) (substInt v x psi)
substInt v x (Or phi psi)      = Or (substInt v x phi) (substInt v x psi)
substInt v x (Implies phi psi) = Implies (substInt v x phi) (substInt v x psi)
substInt v x (Not phi)         = Not (substInt v x phi)
substInt _ _ Bottom            = Bottom
substInt _ _ Top               = Top
substInt v x (PropIntBinRel rel lhs rhs) = PropIntBinRel rel (substIntTerm v x lhs) (substIntTerm v x rhs)
substInt _ _ (PropTextEq t rhs)          = PropTextEq t rhs
substInt v x (PropIntForall  x' phi) | x /= x' = PropIntForall  x' (substInt v x phi)
substInt _ _ (PropIntForall  x' phi)            = PropIntForall  x' phi
substInt v x (PropTextForall x' phi) | x /= x' = PropTextForall x' (substInt v x phi)
substInt _ _ (PropTextForall x' phi)            = PropTextForall x' phi
substInt v x (PropIntExists  x' phi) | x /= x' = PropIntExists  x' (substInt v x phi)
substInt _ _ (PropIntExists  x' phi)            = PropIntExists  x' phi
substInt v x (PropTextExists x' phi) | x /= x' = PropTextExists x' (substInt v x phi)
substInt _ _ (PropTextExists x' phi)            = PropTextExists x' phi

-- | φ[v / x]  (text substitution)
substText :: Extended Text -> VariableIdentifier -> FinFree -> FinFree
substText v x (And phi psi)     = And (substText v x phi) (substText v x psi)
substText v x (Or phi psi)      = Or (substText v x phi) (substText v x psi)
substText v x (Implies phi psi) = Implies (substText v x phi) (substText v x psi)
substText v x (Not phi)         = Not (substText v x phi)
substText _ _ Bottom            = Bottom
substText _ _ Top               = Top
substText _ _ (PropIntBinRel rel lhs rhs)    = PropIntBinRel rel lhs rhs
substText _ _ (PropTextEq (TextConst c) rhs) = PropTextEq (TextConst c) rhs
-- (x = v)[☐ / x] = ⊥ — placeholder is distinct from all strings
substText Placeholder x (PropTextEq (TextVar x') _) | x == x' = Bottom
substText (Val v) x (PropTextEq (TextVar x') rhs)   | x == x' = PropTextEq (TextConst v) rhs
substText _ _ (PropTextEq (TextVar x') rhs)                    = PropTextEq (TextVar x') rhs
substText v x (PropIntForall  x' phi) | x /= x' = PropIntForall  x' (substText v x phi)
substText _ _ (PropIntForall  x' phi)            = PropIntForall  x' phi
substText v x (PropTextForall x' phi) | x /= x' = PropTextForall x' (substText v x phi)
substText _ _ (PropTextForall x' phi)            = PropTextForall x' phi
substText v x (PropIntExists  x' phi) | x /= x' = PropIntExists  x' (substText v x phi)
substText _ _ (PropIntExists  x' phi)            = PropIntExists  x' phi
substText v x (PropTextExists x' phi) | x /= x' = PropTextExists x' (substText v x phi)
substText _ _ (PropTextExists x' phi)            = PropTextExists x' phi

-- ---------------------------------------------------------------------------
-- Lowering to Presburger.Formula
-- ---------------------------------------------------------------------------

-- | Lower a `FinFree` to 'P.Formula' by eliminating all text quantifiers and
--   evaluating ground `PropTextEq` atoms.
--
--   Text universals unfold to a conjunction (⊤ for empty domain);
--   text existentials unfold to a disjunction (⊥ for empty domain).
--
--   @'eval' = 'PD.eval' . 'lower'@
lower :: FinFree -> P.Formula
lower (Or phi psi)      = P.Or (lower phi) (lower psi)
lower (And phi psi)     = P.And (lower phi) (lower psi)
lower (Not phi)         = P.Not (lower phi)
lower (Implies phi psi) = P.Implies (lower phi) (lower psi)
lower Top               = P.Top
lower Bottom            = P.Bottom
lower (PropIntForall x phi) = P.IntForall x (lower phi)
lower (PropIntExists x phi) = P.IntExists x (lower phi)
lower (PropIntBinRel rel lhs rhs) = P.IntBinRel rel lhs rhs
-- Ground text equations are folded directly to ⊤/⊥:
lower (PropTextEq (TextConst lhs) rhs)
  | lhs == rhs = P.Top
  | otherwise  = P.Bottom
lower (PropTextEq (TextVar x) _) = error $ "lower: free text variable " <> show x
-- ⟦∀x ∈ Text. φ⟧ ≡ φ[☐/x] ∧ φ[v₁/x] ∧ ...  (⊤ when dom is empty)
lower (PropTextForall x phi) =
  let vals = Set.toList (textValues x phi)
  in foldr P.And P.Top
       (lower (substText Placeholder x phi) : (vals <&> \v -> lower (substText (Val v) x phi)))
-- ⟦∃x ∈ Text. φ⟧ ≡ φ[☐/x] ∨ φ[v₁/x] ∨ ...  (⊥ when dom is empty)
lower (PropTextExists x phi) =
  let vals = Set.toList (textValues x phi)
  in foldr P.Or P.Bottom
       (lower (substText Placeholder x phi) : (vals <&> \v -> lower (substText (Val v) x phi)))

-- | Evaluate the `FinFree` onto `Bool`.
eval :: FinFree -> Bool
eval = PD.eval . lower
