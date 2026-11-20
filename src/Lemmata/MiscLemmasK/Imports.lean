import Mathlib

namespace Bl.SecondBlockLemmaL

theorem goal1 :
  ∀ {E : Type} [inst : Field.{0} E] [inst_1 : NumberField.{0} E] (ℓ : Nat) [hℓ : Fact (Nat.Prime ℓ)]
  {Q : Ideal.{0} (NumberField.RingOfIntegers.{0} E)},
  Ideal.IsPrime.{0} Q →
    Ne.{1} Q Bot.bot.{0} →
      Not (Membership.mem.{0, 0} Q (Nat.cast.{0} ℓ)) →
        Eq.{1} (padicValNat ℓ (DFunLike.coe.{1, 1, 1} Ideal.absNorm.{0} Q)) 0 := by sorry

















end Bl.SecondBlockLemmaL
