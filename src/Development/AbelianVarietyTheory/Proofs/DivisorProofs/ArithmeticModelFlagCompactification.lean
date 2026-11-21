module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentBasisOfSplitTorsion

@[expose] public section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

section SlopeTestRemainingChoices

private theorem sp_sp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

private theorem dual_eps {K K' : Type} [CommRing K] [CommRing K'] (ψ : K →+* K') (a : K) {Y : Scheme.{0}}
    (v : Sp (DualNumber K) ⟶ Y) :
    spMap (dualMap ψ) ≫ spMap (epsMul a) ≫ v = spMap (epsMul (ψ a)) ≫ spMap (dualMap ψ) ≫ v := by
  rw [← Category.assoc, ← Category.assoc, sp_sp, sp_sp]
  congr 2
  refine RingHom.ext fun z => ?_
  ext <;> simp [Formalism.L2.Pj.GlobalTheory.CompanionTheory.Ar.dualMap, epsMul, TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map, smul_eq_mul, _root_.mul_comm]

private theorem map_inv_nat {K K' : Type} [CommRing K] [CommRing K'] (ψ : K →+* K') (N : ℕ) (h : IsUnit (N : K)) :
    ψ (Ring.inverse (N : K)) = Ring.inverse (N : K') := by
  have h' : IsUnit (N : K') := by simpa using h.map ψ
  apply h'.mul_left_cancel
  rw [Ring.mul_inverse_cancel _ h', ← map_natCast ψ, ← map_mul, Ring.mul_inverse_cancel _ h, map_one]

private theorem unit_nat {K L : Type} [CommRing K] [Field L] [CharZero L] (y : Sp K ⟶ Sp L) {N : ℕ} (hN : N ≠ 0) :
    IsUnit (N : K) := by
  have h : IsUnit (N : L) := (Nat.cast_ne_zero.2 hN).isUnit
  simpa using h.map (Spec.preimage y).hom

private theorem exists_int {A C : Type} [CommRing A] [NormedField C] [IsUltrametricDist C] (f : A →+* C)
    (h : ∀ a, ‖f a‖ ≤ 1) : ∃ j : A →+* ↥(intO C), (intO C).subtype.comp j = f :=
  ⟨f.codRestrict _ h, rfl⟩

private theorem ev_comp {A K : Type} [CommRing A] [CommRing K] {X : Scheme.{0}} {U : X.Opens} (s : A →+* K)
    (xt : Sp A ⟶ X) (hxt : ⊤ ≤ xt ⁻¹ᵁ U) (y : Sp K ⟶ X) (hy : ⊤ ≤ y ⁻¹ᵁ U) (h : spMap s ≫ xt = y) :
    TangentOrigin.evalPt y U hy = s.comp (TangentOrigin.evalPt xt U hxt) := by
  subst h
  exact RingHom.ext fun f => TangentOrigin.evalPt_spMap_comp _ xt U hxt hy f

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

variable {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)

private theorem over_base {K F : Type} [CommRing K] [Field F] (e : F ≃+* c.F) (y : Sp K ⟶ gen Z) (ψ : F →+* K)
    (h : y ≫ genStr Z ≫ spMap e.toRingHom = spMap ψ) :
    y ≫ genι Z ≫ Z.s = spMap ((ψ.comp e.symm.toRingHom).comp β) := by
  have h1 : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _ := by
    rw [sp_sp, show e.toRingHom.comp e.symm.toRingHom = RingHom.id _ from RingHom.ext fun a => e.apply_symm_apply a]
    exact Spec.map_id _
  have h2 : y ≫ genStr Z = spMap (ψ.comp e.symm.toRingHom) := by
    rw [← sp_sp, ← h, Category.assoc, Category.assoc, h1, Category.comp_id]
  rw [← sp_sp, ← h2, Category.assoc]
  exact congrArg (y ≫ ·) Limits.pullback.condition

end SlopeTestRemainingChoices
