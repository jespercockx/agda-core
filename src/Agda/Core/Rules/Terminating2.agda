open import Agda.Core.Prelude
open import Agda.Core.Name
open import Agda.Core.Syntax
open import Agda.Core.Syntax.TerminationUtils

module Agda.Core.Rules.Terminating2
    {{@0 globals : Globals}}
    {{@0 sig     : Signature}}
  where

private open module @0 G = Globals globals

private variable
  @0 x      : Name
  @0 α      : Scope Name
  @0 rβ     : RScope Name
  @0 u v    : Term α
  @0 a b c  : Type α
  @0 k l    : Sort α

Program = List FunDefinition
