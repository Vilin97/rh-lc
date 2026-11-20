import Mathlib

namespace Bl.FirstBlockLemmaL

theorem goal1 :
  ∀ (ℓ : Nat) [Fact (Nat.Prime ℓ)] (s : Multiset.{0} Nat),
  (∀ (x : Nat), Membership.mem.{0, 0} s x → Ne.{1} x 0) →
    Eq.{1} (padicValNat ℓ (Multiset.prod.{0} s)) (Multiset.sum.{0} (Multiset.map.{0, 0} (padicValNat ℓ) s)) := by sorry












end Bl.FirstBlockLemmaL
