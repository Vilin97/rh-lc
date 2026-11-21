module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleLiftingLineBundleTransitionUnits
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwZ
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneralLinearGroupDetMapFinOne

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cocycle_lifting_lineBundle_transition_units : ∀ (q : ℕ) (C : Shv ℤ) (qb : C ⟶ Gm) (E : Spc) (L : E ⟶ ofCat (glCat 1)), Inv q E → (∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U))) → ∃ a : Cocycle ((chains ℤ).obj E) (sgl C) 1, ∀ (U : Scheme.{0}) (x : Sx E 1 U), ∃ c : Sec C U, Sec.map qb c = unitSec (lineUnit L x) ∧ ev a.1 1 0 (by simp) U x = Sec.map (sglι C) c := by
  first | exact @GlobalTheory.EtC.KumPic.lift_cocycle | exact GlobalTheory.EtC.KumPic.lift_cocycle | (intros; apply GlobalTheory.EtC.KumPic.lift_cocycle <;> assumption)
