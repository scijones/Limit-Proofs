/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import Mathlib.Data.Real.Basic

/-!
# Information-Theoretic Primitives

Opaque constants for the measure-theoretic information quantities.

NOTE: `Entropy`, `ConditionalEntropy`, and `JointRV` are vocabulary
only — no load-bearing proof uses them.  For continuous variables
differential entropy can be negative, so all quantitative axioms and
system fields are stated in mutual-information (capacity) form, which
is non-negative and well-behaved for arbitrary random variables. -/

set_option autoImplicit false

axiom RandomVariable : Type
axiom Entropy : RandomVariable → ℝ
axiom ConditionalEntropy : RandomVariable → RandomVariable → ℝ
axiom MutualInformation : RandomVariable → RandomVariable → ℝ
axiom ConditionalMutualInformation : RandomVariable → RandomVariable → RandomVariable → ℝ
axiom JointRV : RandomVariable → RandomVariable → RandomVariable

notation "H(" X ")" => Entropy X
notation "H(" X "|" Y ")" => ConditionalEntropy X Y
notation "I(" X ";" Y ")" => MutualInformation X Y
notation "I(" X ";" Y "|" Z ")" => ConditionalMutualInformation X Y Z
