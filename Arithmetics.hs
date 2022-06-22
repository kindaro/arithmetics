module Arithmetics where

import Prelude qualified
import Data.Functor.Foldable
import Data.Fix
import Data.Vector.Sized
import GHC.TypeNats
import Prelude (Bool(..), Foldable (..), Num (..), Show (..), Semigroup (..), error, Functor (..), Int, Eq, otherwise, Maybe (..), Ord (..), Applicative (..), Monoid (mconcat))
import Data.Functor.Classes
import Generic.Data
import Prelude.Unicode
import Data.String
import Data.Text (Text)
import Data.Type.Equality
import Data.Function
import Type.Reflection
import Data.Proxy
import Control.Applicative.Unicode
import Debug.Trace
import Data.Monoid.Unicode
import Data.Text qualified as Text
import Data.List.NonEmpty qualified as NonEmpty

(▵) ∷ (input → left) → (input → right) → input → (left, right)
function ▵ gunction = \ input → (function input, gunction input)
infixr 7 ▵

pattern E ∷ Vector 0 value
pattern E ← (null → True) where E = empty

pattern (:>) ∷ value → Vector length value → Vector (1 + length) value
pattern value :> values ← (head ▵ tail → (value, values)) where value :> values = value `cons` values
infixr 5 :>

pattern (:∎) ∷ value → value → Vector 2 value
pattern one :∎ other ← (head ▵ last → (one, other)) where one :∎ other = one :> singleton other
infixr 5 :∎

data Wender constant variable recursion where
  Constant ∷ constant → Wender constant variable recursion
  Variable ∷ variable → Wender constant variable recursion
  Operator ∷ KnownNat arity ⇒ Operator arity → Vector arity recursion → Wender constant variable recursion

deriving instance Functor (Wender constant variable)

data Operator arity where
  Add ∷ Operator 2
  Multiply ∷ Operator 2
  Negate ∷ Operator 1
  Invert ∷ Operator 1

deriving instance Eq (Operator arity)

type Expression constant variable = Fix (Wender constant variable)

type family Unfix value = result | result → value where Unfix (Fix value) = value (Fix value)

pattern (:×) ∷ Expression constant variable → Expression constant variable → Expression constant variable
pattern one :× other = Fix (Operator Multiply (one :∎ other))
infixl 7 :×

pattern (:+) ∷ Expression constant variable → Expression constant variable → Expression constant variable
pattern one :+ other = Fix (Operator Add (one :∎ other))
infixl 6 :+

pattern C :: constant -> Fix (Wender constant variable)
pattern C constant = Fix (Constant constant)

pattern V :: variable -> Fix (Wender constant variable)
pattern V variable = Fix (Variable variable)

parenthesize ∷ (Monoid text, IsString text) ⇒ text → text
parenthesize text = "(" ⊕ text ⊕ ")"

showVariables ∷ [Text] → Text
showVariables = mconcat ∘ fmap (showOne ∘ (NonEmpty.head ▵ Prelude.length)) ∘ NonEmpty.group
  where
    showOne ∷ (Text, Int) → Text
    showOne (variable, 1) = variable
    showOne (variable, power) = variable ⊕ (toSuperscript ∘ Text.pack ∘ show) power
    toSuperscript = Text.map \ character → case character of
      '0' → '⁰'
      '1' → '¹'
      '2' → '²'
      '3' → '³'
      '4' → '⁴'
      '5' → '⁵'
      '6' → '⁶'
      '7' → '⁷'
      '8' → '⁸'
      '9' → '⁹'
      anyOtherCharacter → anyOtherCharacter

instance {-# overlapping #-} Show constant ⇒ Show (Expression constant Text) where
  show (C number :× (fold stringifyVariableGroup → Just labels)) = show number ⊕ Text.unpack (showVariables labels)
  show (fold stringifyVariableGroup → Just labels) = Text.unpack (showVariables labels)
  show (one :+ other) = parenthesize do show one ⊕ "  +  " ⊕ show other
  show (one :× other) = parenthesize do show one ⊕ " × " ⊕ show other
  show (Fix (Constant constant)) = show constant
  show (Fix (Variable variable)) = show variable
  show _ = error "not implemented"

instance Num constant ⇒ Num (Expression constant variable) where
  one + other = one :+ other
  one * other = one :× other
  fromInteger = Fix ∘ Constant ∘ fromInteger
  negate = Fix ∘ Operator Negate ∘ singleton

instance {-# overlapping #-} (Eq constant, Eq variable) ⇒ Eq (Expression constant variable) where
  Fix one == Fix other = one ≡ other

equate ∷ (Typeable α, Typeable β) ⇒ α → β → Maybe (α :~: β)
equate α β = testEquality (typeOf α) (typeOf β)

proxify ∷ f α → Proxy α
proxify _ = Proxy

operate ∷ Num number ⇒ Operator 2 → number → number → number
operate Add x y = x + y
operate Multiply x y = x × y

instance (Eq constant, Eq variable, Eq recursion) ⇒ Eq (Wender constant variable recursion) where
  Constant one == Constant other = one ≡ other
  Variable one == Variable other = one ≡ other
  Operator operator vector == Operator surgeon point = case equate operator surgeon of
    Just Refl → vector ≡ point
    Nothing → False
  _ == _ = False

instance IsString (Expression constant Text) where
  fromString = Fix ∘ Variable ∘ fromString

isVariableGroup ∷ Base (Expression number variable) Bool → Bool
isVariableGroup (Operator Multiply (e :∎ e')) = e ∧ e'
isVariableGroup (Variable _) = True
isVariableGroup _ = False

isVariableGroupWithConstant :: Expression number variable -> Bool
isVariableGroupWithConstant (C _ :× e) = fold isVariableGroup e
isVariableGroupWithConstant e = fold isVariableGroup e

stringifyVariableGroup ∷ Base (Expression number variable) (Maybe [variable]) → Maybe [variable]
stringifyVariableGroup (Operator Multiply (e :∎ e')) = pure (⊕) ⊛ e ⊛ e'
stringifyVariableGroup (Variable text) = (Just ∘ pure) text
stringifyVariableGroup _ = Nothing

stringifyVariableGroupWithConstant :: Expression number variable -> Maybe [variable]
stringifyVariableGroupWithConstant (C _ :× e) = fold stringifyVariableGroup e
stringifyVariableGroupWithConstant e = fold stringifyVariableGroup e

normalize ∷ (Num number, Ord variable) ⇒ Unfix (Expression number variable) → Expression number variable

-- Reassociate expressions of form _1 + 2 + x_ as _(1 + 2) + x_ to make them
-- amenable to reduction.
normalize
  ( Operator operator@(equate (Proxy ∷ Proxy 2) ∘ proxify → Just Refl)
    ( C one :∎ Fix
      ( Operator surgeon@(equate (Proxy ∷ Proxy 2) ∘ proxify → Just Refl)
        ( C other :∎ remainder ) ) ) )
  | operator ≡ surgeon = trace "reasociate constants" do Fix (Operator operator (Fix (Operator operator (C one :∎ C other)) :∎ remainder))

-- Commute expressions, moving constants to the left.
normalize
  ( Operator operator@(equate (Proxy ∷ Proxy 2) ∘ proxify → Just Refl)
    ( V v :∎ Fix
      ( Operator surgeon@(equate (Proxy ∷ Proxy 2) ∘ proxify → Just Refl)
        ( C c :∎ remainder ) ) ) )
  | operator ≡ surgeon = trace "commute" do Fix (Operator operator (Fix (Operator operator (C c :∎ V v)) :∎ remainder))

-- Reassociate all other expressions to the right.
normalize
  ( Operator operator@(equate (Proxy ∷ Proxy 2) ∘ proxify → Just Refl)
    ( Fix ( Operator surgeon@(equate (Proxy ∷ Proxy 2) ∘ proxify → Just Refl) (one :∎ other) ) :∎ remainder ) )
  | operator ≡ surgeon = trace "reassociate" do Fix (Operator operator (one :∎ Fix (Operator operator (other :∎ remainder))))

-- Reduce constant expressions.
normalize
  ( Operator operator@(equate (Proxy ∷ Proxy 2) ∘ proxify → Just Refl)
    ( C one :∎ C other ) ) = trace "operate" do C (operate operator one other)

normalize expression = case Fix expression of

-- Distribute multiplication over addition on the left.
  multiple :× (salmon :+ trout)
    → trace "distribute left" do (multiple :× salmon) :+ (multiple :× trout)

-- Distribute multiplication over addition on the right.
  (salmon :+ trout) :× multiple
    → trace "distribute right" do (salmon :× multiple) :+ (trout :× multiple)

-- Gather constants on the left.
  (subexpression :+ constant@(C _)) → trace "constant1" do constant :+ subexpression
  (subexpression :× constant@(C _)) → trace "constant2" do constant :× subexpression

-- Sort variable groups.
  V v :× (V w :× e) | w < v → trace "sort" do V w :× (V v :× e)

  e₁@(stringifyVariableGroupWithConstant → Just t₁) :+
    ( e₂@(stringifyVariableGroupWithConstant → Just t₂) :+ e₃ ) | t₂ < t₁ → trace "sort2" do e₂ :+ (e₁ :+ e₃)

  e₁@(stringifyVariableGroupWithConstant → Just t₁) :+
    e₂@(stringifyVariableGroupWithConstant → Just t₂) | t₂ < t₁ → trace "sort3" do e₂ :+ e₁

-- Gather like terms.
  C c₁ :× v₁@(fold stringifyVariableGroup → Just t₁) :+ (C c₂ :× v₂@(fold stringifyVariableGroup → Just t₂) :+ e)
    | t₁ ≡ t₂ → trace "gather1" do (C c₁ :+ C c₂) :× v₁ :+ e
  C c₁ :× v₁@(fold stringifyVariableGroup → Just t₁) :+ C c₂ :× v₂@(fold stringifyVariableGroup → Just t₂)
    | t₁ ≡ t₂ → trace "gather2" do (C c₁ :+ C c₂) :× v₁

-- If nothing applies, do nothing.
  _ → Fix expression

converge :: Eq a => [a] -> [a]
converge = convergeBy (≡)

fixate :: Eq a => (a -> a) -> a -> a
fixate f = Prelude.last ∘ converge ∘ Prelude.iterate f

convergeBy :: (a -> a -> Bool) -> [a] -> [a]
convergeBy _ [ ] = [ ]
convergeBy _ [x] = [x]
convergeBy eq (x: xs@(y: _))
    | x `eq` y = [x]
    | otherwise = x: convergeBy eq xs
