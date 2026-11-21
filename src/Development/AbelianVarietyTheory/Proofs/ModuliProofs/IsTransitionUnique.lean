module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.SiegelFamilyZetaUnit
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DominatesLiftUnique
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleIffOfIsReduced
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.TransitionUnique

open GlobalTheory.ModelCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem isReduced_XF (Xo : Moduli D l) (c : Coeff l) : IsReduced (Xo.XF c) :=
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) inferInstance).1

theorem map_unique {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {S : Scheme.{0}} [IsReduced S]
    {t : SAB H S} {r r' : S ⟶ Xo.XF c} (ν : SABMap t Y.oF.t r) (ν' : SABMap t Y.oF.t r')
    (hr : r ≫ pullback.snd _ _ = r' ≫ pullback.snd _ _)
    (hM : ∀ a, ∃ x : 𝟙_ (Over S) ⟶ t.G,
      x.left ≫ ν.φ = r ≫ (Y.oF.eta a).left ∧ x.left ≫ ν'.φ = r' ≫ (Y.oF.eta a).left)
    (hA : ∀ a, ∃ x : 𝟙_ (Over S) ⟶ t.G,
      x.left ≫ ν.φ = r ≫ (Y.oF.etaA a).left ∧ x.left ≫ ν'.φ = r' ≫ (Y.oF.etaA a).left) : r = r' := by
  let o := objOfSABMap Y.oF ν
  let n : ObjMap o Y.oF r := objMapOfSABMap Y.oF ν
  let n' : ObjMap o Y.oF r' := ⟨ν', fun a => by
      obtain ⟨x, h, h'⟩ := hM a
      exact (congrArg (fun z => z.left ≫ ν'.φ) (sec_eq_secPull ν h)).symm.trans h', fun a => by
      obtain ⟨x, h, h'⟩ := hA a
      exact (congrArg (fun z => z.left ≫ ν'.φ) (sec_eq_secPull ν h)).symm.trans h'⟩
  obtain ⟨k, -⟩ := ObjComp.objMap_comp Y.m0 n
  obtain ⟨k', -⟩ := ObjComp.objMap_comp Y.m0 n'
  refine pullback.hom_ext ((Xo.rep S _ ‹_› o).unique ⟨Category.assoc _ _ _, ⟨k⟩⟩ ⟨?_, ⟨k'⟩⟩) hr
  rw [Category.assoc, pullback.condition, ← Category.assoc, ← hr, Category.assoc]

end GlobalTheory.TransitionUnique
