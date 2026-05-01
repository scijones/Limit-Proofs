/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticContinuous.InformationTheory.Defs

/-!
# Information-Theoretic Axioms

The data processing inequality and entropy subadditivity.
-/

set_option autoImplicit false

axiom IsMarkovChain (X Y Z W : RandomVariable) : Prop

axiom data_processing_inequality :
  ∀ (X Y Z W : RandomVariable),
    IsMarkovChain X Y Z W →
    I(X ; Z | W) ≤ I(X ; Y | W)

axiom mi_le_conditional_entropy :
  ∀ (X Y Z : RandomVariable),
    I(X ; Y | Z) ≤ ConditionalEntropy Y Z

axiom subadditivity_entropy :
  ∀ (X Y Z : RandomVariable),
    ConditionalEntropy (JointRV X Y) Z ≤
      ConditionalEntropy X Z + ConditionalEntropy Y Z
