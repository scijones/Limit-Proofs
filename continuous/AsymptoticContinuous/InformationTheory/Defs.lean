/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import Mathlib.Data.Real.Basic

/-!
# Information-Theoretic Primitives

Opaque definitions for the measure-theoretic information quantities.
-/

set_option autoImplicit false

axiom RandomVariable : Type
axiom Entropy : RandomVariable â†’ â„
axiom ConditionalEntropy : RandomVariable â†’ RandomVariable â†’ â„
axiom MutualInformation : RandomVariable â†’ RandomVariable â†’ â„
axiom ConditionalMutualInformation : RandomVariable â†’ RandomVariable â†’ RandomVariable â†’ â„
axiom JointRV : RandomVariable â†’ RandomVariable â†’ RandomVariable

notation "H(" X ")" => Entropy X
notation "H(" X "|" Y ")" => ConditionalEntropy X Y
notation "I(" X ";" Y ")" => MutualInformation X Y
notation "I(" X ";" Y "|" Z ")" => ConditionalMutualInformation X Y Z
