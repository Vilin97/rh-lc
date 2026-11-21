module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowCharEqZeroOfKillsVerschiebung

@[expose] public section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.pow_char_eq_zero_of_kills_verschiebung :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0)
      (G : PDivGroup p R) (n : ℕ) (χ : CartierDual R ((frobTwist h G).A n)),
      (∀ a : G.A n, χ ((verschiebung h G).app n a) = 0) → χ ^ p = 0 :=
  @GlobalTheory.PDivGroup.pow_char_eq_zero_of_verschiebung
