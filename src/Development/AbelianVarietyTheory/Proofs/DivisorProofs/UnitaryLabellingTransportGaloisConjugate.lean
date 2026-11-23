module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalLabAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFibre
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsUnitaryClassicalTraitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupLabellingTransportGaloisConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedPointOverLabelPowRNEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecializesIsLocalization
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelQuotientRepresentsReduced
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjUniversalTripleIdentification

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPoinc.UGalTrans

open GlobalTheory.CechPic GlobalTheory.Poinc.GalTrans

theorem exists_twist_along_genericAutomorphism {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S S' : ThetaSys o Ω} (ρ : S.Real)
    (ρ' : S'.Real) (l' : S.Gam → S'.Gam) (h' : USame ρ ρ' l' (RingHom.id _)) (σ τ : Ω →+* Ω)
    (hτ : τ.comp σ = RingHom.id _) (hσ : σ.comp τ = RingHom.id _) (a : S.Gam → S.Gam)
    (P₀ : PolAV (Sp Ω)) (b : P₀.A.left ⟶ ρ.P.A.left) (t : P₀.A.left ⟶ P₀.A.left)
    (hb : IsGrpPullback P₀.A ρ.P.A (spMap S.R.val.toRingHom) b)
    (ht : IsGrpPullback P₀.A P₀.A (spMap σ) t) (lb : LBIso P₀.L (ρ.P.L.pull b)) (lt : LBIso P₀.L (P₀.L.pull t))
    (hp : ∀ x (w w' : Sp Ω ⟶ P₀.A.left), w ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt x).left →
      w' ≫ t = spMap σ ≫ w → w' ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt (a x)).left)
    {B : Scheme.{0}} {v : Sp Ω ⟶ B} {r : B ⟶ Sp S'.R} (hv : v ≫ r = spMap S'.R.val.toRingHom)
    (G : Over B) [GrpObj G] (α : G.left ⟶ ρ'.P.A.left) (hα : IsGrpPullback G ρ'.P.A r α)
    {Y : Scheme.{0}} (N : LB Y) (hN : N.IsLB) (β : G.left ⟶ Y) (hL : LBIso (ρ'.P.L.pull α) (N.pull β)) :
    ∃ (P₁ : PolAV (Sp Ω)) (e : P₁.A.left ⟶ P₀.A.left) (j : P₀.A.left ⟶ P₁.A.left) (k₀ : P₁.A.left ⟶ G.left),
      IsGrpPullback P₁.A P₀.A (spMap σ) e ∧ IsGrpPullback P₀.A P₁.A (spMap τ) j ∧ IsGrpPullback P₁.A G v k₀ ∧
      e ≫ j = 𝟙 _ ∧ LBIso (ρ.P.L.pull b) (N.pull (j ≫ k₀ ≫ β)) ∧
      ∀ x (w : Sp Ω ⟶ P₀.A.left), w ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt x).left →
        ∃ w₀ : Sp Ω ⟶ P₁.A.left, w₀ ≫ P₁.A.hom = 𝟙 _ ∧ w₀ ≫ e = spMap σ ≫ w ∧
          w₀ ≫ k₀ ≫ α = spMap S'.R.val.toRingHom ≫ (ρ'.pt (l' (a x))).left := by
  obtain ⟨P₁, a₁, a₁', ha₁, ha₁', la₁, la₁', hp₁⟩ := h'
  rw [RingHom.id_comp] at ha₁ hp₁
  have := mono_val S.R S.frac
  have : Mono b := (MorphismProperty.monomorphisms Scheme).of_isPullback hb.1.flip (.infer_property _)
  obtain ⟨κ, hκ, lκ, eκ⟩ := exists_factor ρ.P P₀ P₁ (Category.id_comp _) hb ha₁ lb la₁
  have hid : spMap (RingHom.id Ω) = 𝟙 (Sp Ω) := by simp [spMap]
  have e₁ : spMap τ ≫ spMap σ = 𝟙 (Sp Ω) := (sp_comp hτ).trans hid
  have e₂ : spMap σ ≫ spMap τ = 𝟙 (Sp Ω) := (sp_comp hσ).trans hid
  have he : IsGrpPullback P₁.A P₀.A (spMap σ) (κ ≫ t) := (hκ.comp ht).congr (Category.id_comp _) rfl
  have le := lb_comp P₁.isLB P₀.isLB P₀.isLB lκ lt
  have : IsIso (spMap σ) := ⟨_, e₂, e₁⟩
  have : Mono (κ ≫ t) := (MorphismProperty.monomorphisms Scheme).of_isPullback he.1.flip (.infer_property _)
  have : IsMonHom (Iso.refl P₀.A).hom := inferInstanceAs (IsMonHom (𝟙 P₀.A))
  obtain ⟨j, hj, lj, ej⟩ := exists_factor P₀ P₁ P₀ (ψ := 𝟙 _) e₁ he (isGrpPullback_of_iso (Iso.refl P₀.A)) le
    ((iso_iff P₀.isLB P₀.isLB _).2 (by rw [GlobalTheory.CechPic.pull_id]; try rfl))
  have w₁ : a₁' ≫ ρ'.P.A.hom = (P₁.A.hom ≫ v) ≫ r := by rw [ha₁'.1.w, Category.assoc, hv]
  have k₁ := hα.1.lift_fst _ _ w₁
  have k₂ := hα.1.lift_snd _ _ w₁
  generalize hα.1.lift _ _ w₁ = k₀ at k₁ k₂
  have hs : ∀ x, (ρ.pt x).left ≫ ρ.P.A.hom = 𝟙 _ := fun x => Over.w (ρ.pt x)
  refine ⟨P₁, κ ≫ t, j, k₀, he, hj, hα.cancel (ha₁'.congr hv.symm k₁.symm) k₂, ?_, ?_, fun x w hw => ?_⟩
  · rw [← cancel_mono (κ ≫ t), Category.assoc, ej, Category.comp_id, Category.id_comp]
  · have c₁ := (iso_iff (pull_isLB ρ'.P.isLB α) hN β).1 hL
    rw [cls_pull ρ'.P.isLB] at c₁
    rw [iso_iff (pull_isLB ρ.P.isLB b) hN, cls_pull ρ.P.isLB, ← (iso_iff P₀.isLB ρ.P.isLB _).1 lb,
      (iso_iff P₀.isLB P₁.isLB _).1 lj, (iso_iff P₁.isLB ρ'.P.isLB _).1 la₁', ← k₁, pull_comp, pull_comp, pull_comp, c₁]
  · obtain ⟨u, f₁, f₁'⟩ := hp₁ (a x)
    have k₃ : w ≫ P₀.A.hom = 𝟙 _ := by
      rw [← cancel_mono (spMap S.R.val.toRingHom), Category.assoc, ← hb.1.w, reassoc_of% hw, hs]
      simp
    have c₂ : (spMap σ ≫ w) ≫ P₀.A.hom = 𝟙 _ ≫ spMap σ := by rw [Category.assoc, k₃]; simp
    have k₄ := ht.1.lift_fst _ _ c₂
    generalize ht.1.lift _ _ c₂ = w' at k₄
    have k₅ : u ≫ κ = w' := by
      rw [← cancel_mono b, Category.assoc, eκ, f₁, hp x w w' hw k₄]
    refine ⟨u, ?_, by rw [reassoc_of% k₅, k₄], by rw [k₁, f₁']⟩
    rw [← cancel_mono (spMap S.R.val.toRingHom), Category.assoc, ← ha₁.1.w, reassoc_of% f₁, hs]
    simp

theorem exists_conj_uWit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X₁ : USetup C) (D : UDeep X₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (a : D.X.S.Gam ≃+ D.X.S.Gam), D.GalLab σ a → ∀ (c₀ : D.X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra D.X.o₁ D.X.Ω₁) (fg : R'.FG) (frac : ∀ x : D.X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * D.X.S.th x ∈ R') (hev : ∀ x k, c₀ * D.X.S.ev x k ∈ R') (ρ' : (D.X.S.rechart c₀ hc R' fg frac hth hev).Real) (u' : Sp (ratHull R') ⟶ Xo.XF cf), USame D.X.ρ ρ' (fun x => x) (RingHom.id _) → spMap (ratHull R').val.toRingHom ≫ u' = D.X.uΩ → ∀ (G : Over (Sp (ratHull R'))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat R')) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) → ∃ (wi : UWit D.X) (W₀ : Over (Sp D.X.Ω₁)) (_ : GrpObj W₀) (e : W₀.left ⟶ wi.G.left) (k₀ : W₀.left ⟶ G.left), IsGrpPullback W₀ wi.G (spMap (σ : D.X.Ω₁ →+* D.X.Ω₁)) e ∧ IsGrpPullback W₀ G (spMap (ratHull R').val.toRingHom) k₀ ∧ e ≫ wi.β = k₀ ≫ β ∧ ∀ x (w : Sp D.X.Ω₁ ⟶ wi.G.left), w ≫ wi.α = spMap D.X.S.R.val.toRingHom ≫ (D.X.ρ.pt x).left → ∃ w₀ : Sp D.X.Ω₁ ⟶ W₀.left, w₀ ≫ W₀.hom = 𝟙 _ ∧ w₀ ≫ e = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ w ∧ w₀ ≫ k₀ ≫ α = spMap R'.val.toRingHom ≫ (ρ'.pt (a x)).left := by
  intro E _ _ _ H Dw l Xo cf C X₁ D σ a hG c₀ hc R' fg frac hth hev ρ' u' hs hu G _ α β hα hβ hL
  obtain ⟨P₀, b, t, hb, ht, lb, lt, hp⟩ := hG
  obtain ⟨P₁, e, j, k₀, he, hj, hk, ej, hL', hpt⟩ := exists_twist_along_genericAutomorphism D.X.ρ ρ' _ hs (σ : D.X.Ω₁ →+* D.X.Ω₁)
    (σ.symm : D.X.Ω₁ →+* D.X.Ω₁) (RingHom.ext fun x => σ.symm_apply_apply x) (RingHom.ext fun x => σ.apply_symm_apply x)
    a P₀ b t hb ht lb lt hp (spMap_val_toRat R') G α hα _ Xo.univ.t.PP.isLB β hL
  have h₁ : spMap (σ.symm : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.uΩ = D.X.uΩ := by
    rw [D.pt, ← Category.assoc, sp_comp (RingHom.ext fun x => σ.symm.commutes x)]
  have hβ' : IsGrpPullback P₀.A Xo.univ.t.G (D.X.uΩ ≫ pullback.fst _ _) (j ≫ k₀ ≫ β) :=
    (hj.comp (hk.comp hβ)).congr (by rw [← Category.assoc _ u', hu, ← Category.assoc, h₁]) rfl
  exact ⟨{ G := P₀.A, α := b, β := j ≫ k₀ ≫ β, hα := hb, hβ := hβ', hL := hL' }, P₁.A, inferInstance, e, k₀, he, hk,
    by rw [reassoc_of% ej], hpt⟩

end GlobalTheory.UPoinc.UGalTrans
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjUniversalTripleIdentificationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_conj_universalTriple_identification : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X₁ : USetup C) (D : UDeep X₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (a : D.X.S.Gam ≃+ D.X.S.Gam), D.GalLab σ a → ∀ (c₀ : D.X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra D.X.o₁ D.X.Ω₁) (fg : R'.FG) (frac : ∀ x : D.X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * D.X.S.th x ∈ R') (hev : ∀ x k, c₀ * D.X.S.ev x k ∈ R') (ρ' : (D.X.S.rechart c₀ hc R' fg frac hth hev).Real) (u' : Sp (ratHull R') ⟶ Xo.XF cf), USame D.X.ρ ρ' (fun x => x) (RingHom.id _) → spMap (ratHull R').val.toRingHom ≫ u' = D.X.uΩ → ∀ (G : Over (Sp (ratHull R'))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat R')) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) → ∃ (wi : UWit D.X) (W₀ : Over (Sp D.X.Ω₁)) (_ : GrpObj W₀) (e : W₀.left ⟶ wi.G.left) (k₀ : W₀.left ⟶ G.left), IsGrpPullback W₀ wi.G (spMap (σ : D.X.Ω₁ →+* D.X.Ω₁)) e ∧ IsGrpPullback W₀ G (spMap (ratHull R').val.toRingHom) k₀ ∧ e ≫ wi.β = k₀ ≫ β ∧ ∀ x (w : Sp D.X.Ω₁ ⟶ wi.G.left), w ≫ wi.α = spMap D.X.S.R.val.toRingHom ≫ (D.X.ρ.pt x).left → ∃ w₀ : Sp D.X.Ω₁ ⟶ W₀.left, w₀ ≫ W₀.hom = 𝟙 _ ∧ w₀ ≫ e = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ w ∧ w₀ ≫ k₀ ≫ α = spMap R'.val.toRingHom ≫ (ρ'.pt (a x)).left := by
  first | exact @GlobalTheory.UPoinc.UGalTrans.exists_conj_uWit | exact GlobalTheory.UPoinc.UGalTrans.exists_conj_uWit | (intros; apply GlobalTheory.UPoinc.UGalTrans.exists_conj_uWit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRechartingsCommonGeometricFibre

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPoinc.USpreadU

open GlobalTheory.Poinc.GalTrans GlobalTheory.CechPic

theorem exists_model {O Ω R' R'' : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O]
    [IsIntegrallyClosed O] [Field Ω] [Algebra O Ω] [IsFractionRing O Ω] [CommRing R'] [CommRing R'']
    (f' : R' →+* O) (f'' : R'' →+* O) (P' : PolAV (Sp R')) (P'' : PolAV (Sp R'')) (Q : PolAV (Sp Ω))
    {b' : Q.A.left ⟶ P'.A.left} {b'' : Q.A.left ⟶ P''.A.left}
    (hb' : IsGrpPullback Q.A P'.A (spMap ((algebraMap O Ω).comp f')) b')
    (hb'' : IsGrpPullback Q.A P''.A (spMap ((algebraMap O Ω).comp f'')) b'')
    (l' : LBIso Q.L (P'.L.pull b')) (l'' : LBIso Q.L (P''.L.pull b'')) :
    ∃ (B : PolAV (Sp O)) (c' : B.A.left ⟶ P'.A.left) (c'' : B.A.left ⟶ P''.A.left) (j : Q.A.left ⟶ B.A.left),
      IsGrpPullback B.A P'.A (spMap f') c' ∧ IsGrpPullback B.A P''.A (spMap f'') c'' ∧
      LBIso B.L (P'.L.pull c') ∧ LBIso B.L (P''.L.pull c'') ∧
      IsGrpPullback Q.A B.A (spMap (algebraMap O Ω)) j ∧ j ≫ c' = b' ∧ j ≫ c'' = b'' ∧
      ∀ (t' : Sp R' ⟶ P'.A.left) (t'' : Sp R'' ⟶ P''.A.left) (w : Sp Ω ⟶ Q.A.left), t' ≫ P'.A.hom = 𝟙 _ →
        t'' ≫ P''.A.hom = 𝟙 _ → w ≫ Q.A.hom = 𝟙 _ → w ≫ b' = spMap ((algebraMap O Ω).comp f') ≫ t' →
        w ≫ b'' = spMap ((algebraMap O Ω).comp f'') ≫ t'' →
        ∃ w₀ : Sp O ⟶ B.A.left, w₀ ≫ B.A.hom = 𝟙 _ ∧ w₀ ≫ c' = spMap f' ≫ t' ∧ w₀ ≫ c'' = spMap f'' ≫ t'' := by
  obtain ⟨B, c', -, hc', lc'⟩ := GlobalTheory.PureType.exists_baseChange GlobalTheory.polBaseChange_holds (spMap f') P'
  obtain ⟨B₂, c₂, -, hc₂, lc₂⟩ := GlobalTheory.PureType.exists_baseChange GlobalTheory.polBaseChange_holds (spMap f'') P''
  obtain ⟨j, hj, lj, ej⟩ := exists_factor P' B Q (sp_comp rfl) hc' hb' lc' l'
  obtain ⟨j₂, hj₂, lj₂, ej₂⟩ := exists_factor P'' B₂ Q (sp_comp rfl) hc₂ hb'' lc₂ l''
  obtain ⟨E, hE, lE, eE⟩ := exists_iso B B₂ Q hj hj₂ lj lj₂
  have hc'' : IsGrpPullback B.A P''.A (spMap f'') (E ≫ c₂) := (hE.comp hc₂).congr (Category.id_comp _) rfl
  have lc'' := lb_comp B.isLB B₂.isLB P''.isLB lE lc₂
  have ej'' : j ≫ E ≫ c₂ = b'' := by rw [← Category.assoc, eE, ej₂]
  generalize E ≫ c₂ = c'' at hc'' lc'' ej''
  obtain ⟨_, _⟩ : QuasiCompact (spMap (algebraMap O Ω)) ∧ IsSchemeTheoreticallyDominant (spMap (algebraMap O Ω)) :=
    ExtUnique.spec_fractionRing O Ω
  have := P''.isAb.proper
  refine ⟨B, c', c'', j, hc', hc'', lc', lc'', hj, ej, ej'', fun t' t'' w ht' ht'' hw e' e'' => ?_⟩
  have w₁ : (spMap f' ≫ t') ≫ P'.A.hom = 𝟙 _ ≫ spMap f' := by rw [Category.assoc, ht']; simp
  have k₁ := hc'.1.lift_fst _ _ w₁
  have k₂ := hc'.1.lift_snd _ _ w₁
  generalize hc'.1.lift _ _ w₁ = t at k₁ k₂
  have a₁ : spMap (algebraMap O Ω) ≫ t = w ≫ j := hc'.1.hom_ext
    (by rw [Category.assoc, k₁, Category.assoc, ej, e', ← Category.assoc, sp_comp rfl])
    (by rw [Category.assoc, k₂, Category.assoc, hj.1.w, reassoc_of% hw, Category.comp_id])
  have a₂ : t ≫ c'' = spMap f'' ≫ t'' := ExtUnique.hom_ext_of_dominant P''.A.hom
    (by rw [Category.assoc, hc''.1.w, reassoc_of% k₂, Category.assoc, ht'', Category.comp_id])
    (spMap (algebraMap O Ω))
    (by rw [reassoc_of% a₁, ej'', e'', ← Category.assoc, sp_comp rfl])
  exact ⟨t, k₂, k₁, a₂⟩

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (σ : X.Ω₁ →+* X.Ω₁) (s : X.M.Z ⟶ X.M.Z), X.M.pt ≫ s = spMap σ ≫ X.M.pt → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (PadicAlgCl p) ⟶ X.M.Z) (S' S'' : ThetaSys X.o₁ X.Ω₁) (ρ' : S'.Real) (ρ'' : S''.Real), S'.R ≤ X.M.O (y (closedPoint (PadicAlgCl p))) → S''.R ≤ X.M.O ((y ≫ s) (closedPoint (PadicAlgCl p))) → ∀ (y₀ : S'.R →+* PadicAlgCl p) (y₁ : S''.R →+* PadicAlgCl p), (∀ a : S'.R, y₀ a = X.M.val y a) → (∀ a : S''.R, y₁ a = X.M.val (y ≫ s) a) → ∀ (u : ρ'.UTest p y₀) (u₁ : ρ''.UTest p y₁) (u' : Sp (ratHull S'.R) ⟶ Xo.XF cf) (u'' : Sp (ratHull S''.R) ⟶ Xo.XF cf) (G : Over (Sp (ratHull S'.R))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left) (G'' : Over (Sp (ratHull S''.R))) (_ : GrpObj G'') (α'' : G''.left ⟶ ρ''.P.A.left) (β'' : G''.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat S'.R)) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) → IsGrpPullback G'' ρ''.P.A (spMap (toRat S''.R)) α'' → IsGrpPullback G'' Xo.univ.t.G (u'' ≫ pullback.fst _ _) β'' → LBIso (ρ''.P.L.pull α'') (Xo.univ.t.PP.L.pull β'') → ∀ (W₀ : Over (Sp X.Ω₁)) (_ : GrpObj W₀) (k₀ : W₀.left ⟶ G.left) (k₀'' : W₀.left ⟶ G''.left), IsGrpPullback W₀ G (spMap (ratHull S'.R).val.toRingHom) k₀ → IsGrpPullback W₀ G'' (spMap (σ.comp (ratHull S''.R).val.toRingHom)) k₀'' → k₀ ≫ β = k₀'' ≫ β'' → ∃ (P₀ : PolAV (Sp (PadicAlgCl p))) (a : P₀.A.left ⟶ u.A.A.left) (a' : P₀.A.left ⟶ u₁.A.A.left), IsGrpPullback P₀.A u.A.A (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))) a ∧ IsGrpPullback P₀.A u₁.A.A (spMap (algebraMap (FractionRing u₁.V) (PadicAlgCl p))) a' ∧ LBIso P₀.L (u.A.L.pull a) ∧ LBIso P₀.L (u₁.A.L.pull a') ∧ (∀ (k' : S'.Gam) (k'' : S''.Gam) (w : Sp X.Ω₁ ⟶ W₀.left), w ≫ W₀.hom = 𝟙 _ → w ≫ k₀ ≫ α = spMap S'.R.val.toRingHom ≫ (ρ'.pt k').left → w ≫ k₀'' ≫ α'' = spMap (σ.comp S''.R.val.toRingHom) ≫ (ρ''.pt k'').left → ∃ (v : Sp (PadicAlgCl p) ⟶ P₀.A.left) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (x' : TFK (R := u₁.V) (PadicAlgCl p) ⟶ u₁.A.A), v ≫ P₀.A.hom = 𝟙 _ ∧ v ≫ a = x.left ∧ v ≫ a' = x'.left ∧ x.left ≫ u.φ = spMap y₀ ≫ (ρ'.pt k').left ∧ x'.left ≫ u₁.φ = spMap y₁ ≫ (ρ''.pt k'').left) ∧ ∀ (v : Sp (PadicAlgCl p) ⟶ P₀.A.left) (g : Sp (PadicAlgCl p) ⟶ G.left) (h : Sp (PadicAlgCl p) ⟶ G''.left), v ≫ P₀.A.hom = 𝟙 _ → g ≫ α = v ≫ a ≫ u.φ → h ≫ α'' = v ≫ a' ≫ u₁.φ → g ≫ β = h ≫ β'' := by
  intro E _ _ _ H Dw l Xo cf C X σ s hs p _ y S' S'' ρ' ρ'' h' h'' y₀ y₁ hy₀ hy₁ u u₁ u' u'' G _ α β G'' _ α'' β'' hα hβ hL hα'' hβ'' hL'' W₀ _ k₀ k₀'' hk₀ hk₀'' hkb
  haveI := X.ar.char
  set z := y (closedPoint (PadicAlgCl p)) with hz
  have hyz : Set.range y = {z} := RatModel.range_eq_singleton y _
  haveI : IsDedekindDomain X.o₁ := ArithBase.ded (Ω := X.Ω₁)
  haveI : IsNoetherianRing (X.M.O z) := X.M.isNoetherianRing_O z
  haveI : IsIntegrallyClosed (X.M.Z.presheaf.stalk z) := X.normal.isIntegrallyClosed_stalk z
  haveI : IsIntegrallyClosed (X.M.O z) := IsIntegrallyClosed.of_equiv (X.M.stalkEquiv z)

  have hU : ∀ n : ℤ, n ≠ 0 → IsUnit (n : X.M.O z) := fun n hn => by
    rw [← RatModel.val_ne_zero_iff hyz]
    have e := map_intCast (RatModel.valHom y z hyz) n
    rw [RatModel.valHom_apply] at e
    rw [e]
    exact Int.cast_ne_zero.2 hn
  have hmem : ∀ {x : X.Ω₁} (n : ℤ), n ≠ 0 → (n : X.Ω₁) * x ∈ X.M.O z → x ∈ X.M.O z := fun {x} n hn h => by
    obtain ⟨w, hw⟩ := hU n hn
    have e1 : (((w⁻¹ : (X.M.O z)ˣ) : X.M.O z) : X.Ω₁) * (n : X.Ω₁) = 1 := by
      have := congrArg (fun t : X.M.O z => (t : X.Ω₁)) w.inv_mul
      simpa [hw] using this
    have : x = (((w⁻¹ : (X.M.O z)ˣ) : X.M.O z) : X.Ω₁) * ((n : X.Ω₁) * x) := by rw [← mul_assoc, e1, one_mul]
    rw [this]; exact mul_mem (SetLike.coe_mem _) h
  have hR' : ratHull S'.R ≤ X.M.O z := fun x hx => by
    obtain ⟨n, hn, h⟩ := mem_ratHull.1 hx
    exact hmem n hn (h' h)
  have hR'' : ∀ x ∈ ratHull S''.R, σ x ∈ X.M.O z := fun x hx => by
    obtain ⟨n, hn, h⟩ := mem_ratHull.1 hx
    refine hmem n hn ?_
    have := map_mem_O hs (h'' h)
    rwa [map_mul, map_intCast] at this
  let f'Q : ratHull S'.R →+* X.M.O z := (Subalgebra.inclusion hR').toRingHom
  let f''Q : ratHull S''.R →+* X.M.O z := (σ.comp (ratHull S''.R).val.toRingHom).codRestrict (X.M.O z) fun x => hR'' x x.2
  let f' : S'.R →+* X.M.O z := f'Q.comp (toRat S'.R)
  let f'' : S''.R →+* X.M.O z := f''Q.comp (toRat S''.R)

  obtain ⟨Q, c, hc, lc⟩ := exists_pol_baseChange ρ'.P (spMap S'.R.val.toRingHom)
  have hW : IsGrpPullback W₀ ρ'.P.A (spMap S'.R.val.toRingHom) (k₀ ≫ α) :=
    (hk₀.comp hα).congr (spMap_val_toRat S'.R) rfl
  have ec : hW.1.lift c Q.A.hom hc.1.w ≫ k₀ ≫ α = c := hW.1.lift_fst _ _ _
  have ew : hW.1.lift c Q.A.hom hc.1.w ≫ W₀.hom = Q.A.hom := hW.1.lift_snd _ _ _
  generalize hW.1.lift c Q.A.hom hc.1.w = e at ec ew
  have he : IsGrpPullback Q.A W₀ (𝟙 _) e :=
    hW.cancel (hc.congr (Category.id_comp _).symm ec.symm) (by rw [ew, Category.comp_id])
  have hb'' : IsGrpPullback Q.A ρ''.P.A (spMap (σ.comp S''.R.val.toRingHom)) (e ≫ k₀'' ≫ α'') :=
    (he.comp (hk₀''.comp hα'')).congr (by rw [Category.id_comp]; exact sp_comp (RingHom.ext fun _ => rfl)) rfl
  have iso_iff {X Y : Scheme.{0}} {L : LB X} {M : LB Y} (hL : L.IsLB) (hM : M.IsLB) (φ : X ⟶ Y) :
      LBIso L (M.pull φ) ↔ cls L hL = GlobalTheory.CechPic.pull φ (cls M hM) := by
    rw [← cls_pull hM φ (pull_isLB hM φ)]
    exact (cls_eq_iff hL _).symm
  have hA : GlobalTheory.CechPic.pull α (cls ρ'.P.L ρ'.P.isLB) = GlobalTheory.CechPic.pull β (cls _ Xo.univ.t.PP.isLB) := by
    rw [← cls_pull ρ'.P.isLB α (pull_isLB ρ'.P.isLB α)]
    exact (iso_iff (pull_isLB ρ'.P.isLB α) Xo.univ.t.PP.isLB β).1 hL
  have hA'' : GlobalTheory.CechPic.pull α'' (cls ρ''.P.L ρ''.P.isLB) = GlobalTheory.CechPic.pull β'' (cls _ Xo.univ.t.PP.isLB) := by
    rw [← cls_pull ρ''.P.isLB α'' (pull_isLB ρ''.P.isLB α'')]
    exact (iso_iff (pull_isLB ρ''.P.isLB α'') Xo.univ.t.PP.isLB β'').1 hL''
  have hk : GlobalTheory.CechPic.pull k₀ (GlobalTheory.CechPic.pull β (cls _ Xo.univ.t.PP.isLB)) = GlobalTheory.CechPic.pull k₀'' (GlobalTheory.CechPic.pull β'' (cls _ Xo.univ.t.PP.isLB)) := by
    rw [← pull_comp, ← pull_comp, hkb]
  have lb'' : LBIso Q.L (ρ''.P.L.pull (e ≫ k₀'' ≫ α'')) := by
    rw [iso_iff Q.isLB ρ''.P.isLB, (iso_iff Q.isLB ρ'.P.isLB _).1 lc, ← ec]
    simp only [pull_comp]
    rw [hA, hA'', hk]

  obtain ⟨B, c', c'', j, hc', hc'', lc', lc'', hj, ej', ej'', ht⟩ :=
    exists_model f' f'' ρ'.P ρ''.P Q (b' := c) (b'' := e ≫ k₀'' ≫ α'') hc hb'' lc lb''

  let v : X.M.O z →+* PadicAlgCl p := RatModel.valHom y z hyz
  have e₀ : v.comp f' = y₀ := RingHom.ext fun x => (hy₀ x).symm
  have e₁ : v.comp f'' = y₁ := RingHom.ext fun x => ((hy₁ x).trans (val_comp hs y _ (h'' x.2))).symm
  obtain ⟨P₀, d, hd, ld⟩ := exists_pol_baseChange B (spMap v)
  have hd' : IsGrpPullback P₀.A ρ'.P.A (spMap y₀) (d ≫ c') := (hd.comp hc').congr (sp_comp e₀) rfl
  have hd'' : IsGrpPullback P₀.A ρ''.P.A (spMap y₁) (d ≫ c'') := (hd.comp hc'').congr (sp_comp e₁) rfl
  obtain ⟨a, ha, la, ea, xa⟩ := exists_to_test u P₀ hd' (lb_comp P₀.isLB B.isLB ρ'.P.isLB ld lc')
  obtain ⟨a', ha', la', ea', xa'⟩ := exists_to_test u₁ P₀ hd'' (lb_comp P₀.isLB B.isLB ρ''.P.isLB ld lc'')
  refine ⟨P₀, a, a', ha, ha', la, la', fun k' k'' w hw c1 c2 => ?_, fun v₁ g h hv₁ hg hh => ?_⟩
  · have ww : w ≫ W₀.hom = 𝟙 _ ≫ 𝟙 _ := by rw [hw]; simp
    have q1 : he.1.lift w (𝟙 _) ww ≫ e = w := he.1.lift_fst _ _ _
    have q2 : he.1.lift w (𝟙 _) ww ≫ Q.A.hom = 𝟙 _ := he.1.lift_snd _ _ _
    generalize he.1.lift w (𝟙 _) ww = wQ at q1 q2
    obtain ⟨w₀, hw₀, g', g''⟩ := ht (ρ'.pt k').left (ρ''.pt k'').left wQ (Over.w (ρ'.pt k')) (Over.w (ρ''.pt k''))
      q2 (by rw [← ec, reassoc_of% q1, c1]; rfl) (by rw [reassoc_of% q1, c2]; rfl)
    have w₂ : (spMap v ≫ w₀) ≫ B.A.hom = 𝟙 _ ≫ spMap v := by rw [Category.assoc, hw₀]; simp
    have r1 : hd.1.lift _ _ w₂ ≫ d = spMap v ≫ w₀ := hd.1.lift_fst _ _ _
    have r2 : hd.1.lift _ _ w₂ ≫ P₀.A.hom = 𝟙 _ := hd.1.lift_snd _ _ _
    generalize hd.1.lift _ _ w₂ = wK at r1 r2
    obtain ⟨x, hx⟩ := xa wK r2
    obtain ⟨x', hx'⟩ := xa' wK r2
    refine ⟨wK, x, x', r2, hx, hx', ?_, ?_⟩
    · rw [← hx, Category.assoc, ea, reassoc_of% r1, g', ← Category.assoc, sp_comp e₀]
    · rw [← hx', Category.assoc, ea', reassoc_of% r1, g'', ← Category.assoc, sp_comp e₁]

  ·
    have wm' : c' ≫ ρ'.P.A.hom = (B.A.hom ≫ spMap f'Q) ≫ spMap (toRat S'.R) := by
      rw [Category.assoc, sp_comp rfl]; exact hc'.1.w
    have wm'' : c'' ≫ ρ''.P.A.hom = (B.A.hom ≫ spMap f''Q) ≫ spMap (toRat S''.R) := by
      rw [Category.assoc, sp_comp rfl]; exact hc''.1.w
    have m1 : hα.1.lift c' _ wm' ≫ α = c' := hα.1.lift_fst _ _ _
    have m2 : hα.1.lift c' _ wm' ≫ G.hom = B.A.hom ≫ spMap f'Q := hα.1.lift_snd _ _ _
    have m1'' : hα''.1.lift c'' _ wm'' ≫ α'' = c'' := hα''.1.lift_fst _ _ _
    have m2'' : hα''.1.lift c'' _ wm'' ≫ G''.hom = B.A.hom ≫ spMap f''Q := hα''.1.lift_snd _ _ _
    generalize hα.1.lift c' _ wm' = m' at m1 m2
    generalize hα''.1.lift c'' _ wm'' = m'' at m1'' m2''
    have key : m' ≫ β = m'' ≫ β'' := by
      haveI := Xo.univ.proper
      haveI : IsSeparated Xo.s := GlobalTheory.LevelQuotRep.isSeparated_of_qproj Xo.qproj
      obtain ⟨_, _⟩ : QuasiCompact (spMap (algebraMap (X.M.O z) X.Ω₁)) ∧
          IsSchemeTheoreticallyDominant (spMap (algebraMap (X.M.O z) X.Ω₁)) :=
        ExtUnique.spec_fractionRing (X.M.O z) X.Ω₁
      haveI := B.isAb.smooth
      haveI : IsSchemeTheoreticallyDominant j := .of_isPullback hj.1.flip
      refine ExtUnique.hom_ext_of_dominant (Xo.univ.t.G.hom ≫ Xo.s ≫ terminal.from _) (terminal.hom_ext _ _) j ?_
      have n1a : (j ≫ m') ≫ α = (e ≫ k₀) ≫ α := by rw [Category.assoc, m1, ej', Category.assoc, ec]
      have n1b : (j ≫ m') ≫ G.hom = (e ≫ k₀) ≫ G.hom := by
        rw [Category.assoc, m2, reassoc_of% hj.1.w, Category.assoc, hk₀.1.w, reassoc_of% ew]
        exact congrArg (Q.A.hom ≫ ·) (sp_comp (RingHom.ext fun _ => rfl))
      have n1 : j ≫ m' = e ≫ k₀ := hα.1.hom_ext n1a n1b
      have n2a : (j ≫ m'') ≫ α'' = (e ≫ k₀'') ≫ α'' := by rw [Category.assoc, m1'', ej'', Category.assoc]
      have n2b : (j ≫ m'') ≫ G''.hom = (e ≫ k₀'') ≫ G''.hom := by
        rw [Category.assoc, m2'', reassoc_of% hj.1.w, Category.assoc, hk₀''.1.w, reassoc_of% ew]
        exact congrArg (Q.A.hom ≫ ·) (sp_comp (RingHom.ext fun _ => rfl))
      have n2 : j ≫ m'' = e ≫ k₀'' := hα''.1.hom_ext n2a n2b
      rw [reassoc_of% n1, reassoc_of% n2, hkb]
    have hg' : g ≫ α = v₁ ≫ d ≫ c' := by rw [hg, ea]
    have hh' : h ≫ α'' = v₁ ≫ d ≫ c'' := by rw [hh, ea']
    have g1 : g = v₁ ≫ d ≫ m' := hα.1.hom_ext (by rw [hg', Category.assoc, Category.assoc, m1])
      ((existsUnique_ratPoint S'.R (g ≫ α ≫ ρ'.P.A.hom)).unique (by rw [Category.assoc, hα.1.w])
        (by simp only [Category.assoc]; rw [← hα.1.w, reassoc_of% m1, ← reassoc_of% hg']))
    have h1 : h = v₁ ≫ d ≫ m'' := hα''.1.hom_ext (by rw [hh', Category.assoc, Category.assoc, m1''])
      ((existsUnique_ratPoint S''.R (h ≫ α'' ≫ ρ''.P.A.hom)).unique (by rw [Category.assoc, hα''.1.w])
        (by simp only [Category.assoc]; rw [← hα''.1.w, reassoc_of% m1'', ← reassoc_of% hh']))
    rw [g1, h1]; simp only [Category.assoc, key]

end GlobalTheory.UPoinc.USpreadU
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRechartingsCommonGeometricFibreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.unitaryRechartings_common_geometricFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (σ : X.Ω₁ →+* X.Ω₁) (s : X.M.Z ⟶ X.M.Z), X.M.pt ≫ s = spMap σ ≫ X.M.pt → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (PadicAlgCl p) ⟶ X.M.Z) (S' S'' : ThetaSys X.o₁ X.Ω₁) (ρ' : S'.Real) (ρ'' : S''.Real), S'.R ≤ X.M.O (y (closedPoint (PadicAlgCl p))) → S''.R ≤ X.M.O ((y ≫ s) (closedPoint (PadicAlgCl p))) → ∀ (y₀ : S'.R →+* PadicAlgCl p) (y₁ : S''.R →+* PadicAlgCl p), (∀ a : S'.R, y₀ a = X.M.val y a) → (∀ a : S''.R, y₁ a = X.M.val (y ≫ s) a) → ∀ (u : ρ'.UTest p y₀) (u₁ : ρ''.UTest p y₁) (u' : Sp (ratHull S'.R) ⟶ Xo.XF cf) (u'' : Sp (ratHull S''.R) ⟶ Xo.XF cf) (G : Over (Sp (ratHull S'.R))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left) (G'' : Over (Sp (ratHull S''.R))) (_ : GrpObj G'') (α'' : G''.left ⟶ ρ''.P.A.left) (β'' : G''.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat S'.R)) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) → IsGrpPullback G'' ρ''.P.A (spMap (toRat S''.R)) α'' → IsGrpPullback G'' Xo.univ.t.G (u'' ≫ pullback.fst _ _) β'' → LBIso (ρ''.P.L.pull α'') (Xo.univ.t.PP.L.pull β'') → ∀ (W₀ : Over (Sp X.Ω₁)) (_ : GrpObj W₀) (k₀ : W₀.left ⟶ G.left) (k₀'' : W₀.left ⟶ G''.left), IsGrpPullback W₀ G (spMap (ratHull S'.R).val.toRingHom) k₀ → IsGrpPullback W₀ G'' (spMap (σ.comp (ratHull S''.R).val.toRingHom)) k₀'' → k₀ ≫ β = k₀'' ≫ β'' → ∃ (P₀ : PolAV (Sp (PadicAlgCl p))) (a : P₀.A.left ⟶ u.A.A.left) (a' : P₀.A.left ⟶ u₁.A.A.left), IsGrpPullback P₀.A u.A.A (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))) a ∧ IsGrpPullback P₀.A u₁.A.A (spMap (algebraMap (FractionRing u₁.V) (PadicAlgCl p))) a' ∧ LBIso P₀.L (u.A.L.pull a) ∧ LBIso P₀.L (u₁.A.L.pull a') ∧ (∀ (k' : S'.Gam) (k'' : S''.Gam) (w : Sp X.Ω₁ ⟶ W₀.left), w ≫ W₀.hom = 𝟙 _ → w ≫ k₀ ≫ α = spMap S'.R.val.toRingHom ≫ (ρ'.pt k').left → w ≫ k₀'' ≫ α'' = spMap (σ.comp S''.R.val.toRingHom) ≫ (ρ''.pt k'').left → ∃ (v : Sp (PadicAlgCl p) ⟶ P₀.A.left) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (x' : TFK (R := u₁.V) (PadicAlgCl p) ⟶ u₁.A.A), v ≫ P₀.A.hom = 𝟙 _ ∧ v ≫ a = x.left ∧ v ≫ a' = x'.left ∧ x.left ≫ u.φ = spMap y₀ ≫ (ρ'.pt k').left ∧ x'.left ≫ u₁.φ = spMap y₁ ≫ (ρ''.pt k'').left) ∧ ∀ (v : Sp (PadicAlgCl p) ⟶ P₀.A.left) (g : Sp (PadicAlgCl p) ⟶ G.left) (h : Sp (PadicAlgCl p) ⟶ G''.left), v ≫ P₀.A.hom = 𝟙 _ → g ≫ α = v ≫ a ≫ u.φ → h ≫ α'' = v ≫ a' ≫ u₁.φ → g ≫ β = h ≫ β'' := by
  first | exact @GlobalTheory.UPoinc.USpreadU.main | exact GlobalTheory.UPoinc.USpreadU.main | (intros; apply GlobalTheory.UPoinc.USpreadU.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLabellingTransportGaloisConjugate

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPoinc.UGalTrans

theorem exists_lift_rat {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CharZero Ω] {R : Subalgebra o Ω}
    {P : PolAV (Sp R)} {G : Over (Sp (ratHull R))} [GrpObj G] {α : G.left ⟶ P.A.left}
    (hα : IsGrpPullback G P.A (spMap (toRat R)) α) {K : Type} [Field K] [CharZero K] (q : Sp K ⟶ P.A.left) :
    ∃ g : Sp K ⟶ G.left, g ≫ α = q := by
  obtain ⟨x', hx', -⟩ := existsUnique_ratPoint R (q ≫ P.A.hom)
  exact ⟨hα.1.lift q x' hx'.symm, hα.1.lift_fst _ _ _⟩


theorem isLab_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X₁ : USetup C) (D : UDeep X₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (s : D.X.M.Z ⟶ D.X.M.Z), D.X.M.pt ≫ s = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.M.pt → ∀ a : D.X.S.Gam ≃+ D.X.S.Gam, D.GalLab σ a → (∀ x, a (D.lab x) = D.lab x) → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (ct : UCTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y) (h' : (y ≫ s) ≫ D.q = ct.y) (yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X), UIsLab D.X (D.lift ct y h) yy → UIsLab D.X (D.lift ct (y ≫ s) h') (yy.comp a.toAddMonoidHom) := by
  intro E _ _ _ H Dw hpq l Xo cf C X₁ D σ s hs a hG _ p _ z₁ ct y h h' yy hy
  haveI : CharZero D.X.Ω₁ := D.X.ar.char
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', u', hS, -, hu', hR, G, _, α, β, hα, hβ, hL, y₀, hy₀, u, lb, j, hq, hyy,
    hall⟩ := hy
  obtain ⟨wi, W₀, _, e, k₀, he, hk₀, heβ, htw⟩ :=
    GlobalTheory.T.exists_conj_universalTriple_identification E H Dw l Xo cf C X₁ D σ a hG c₀ hc R' fg frac hth hev ρ' u' hS hu' G _ α β hα hβ hL
  obtain ⟨yy₁, hW⟩ := GlobalTheory.T.exists_labels_unitaryClassicalTrait E H Dw hpq l Xo cf C D.X wi p _ (D.lift ct (y ≫ s) h')
  obtain ⟨c₁, hc₁, R'', fg₁, frac₁, hth₁, hev₁, ρ'', u'', hS₁, hi₁, hu₁, hR₁, G'', _, α'', β'', hα'', hβ'', hL'',
    ⟨m'', hm'', hmβ, hmt⟩, y₁, hy₁, u₁, lb₁, j₁, -, -, -⟩ := hW
  have hk'' : IsGrpPullback W₀ G'' (spMap ((σ : D.X.Ω₁ →+* D.X.Ω₁).comp (ratHull R'').val.toRingHom)) (e ≫ m'') :=
    (he.comp hm'').congr (GalTrans.sp_comp rfl) rfl
  have hββ : k₀ ≫ β = (e ≫ m'') ≫ β'' := by rw [Category.assoc, hmβ, heβ]
  obtain ⟨P₀, ka, ka', hka, hka', lka, lka', htor, hβeq⟩ := GlobalTheory.T.unitaryRechartings_common_geometricFibre E H Dw l Xo cf C D.X (σ : D.X.Ω₁ →+* D.X.Ω₁) s hs p
    (gPt p ≫ y) _ _ ρ' ρ'' hR (by rw [Category.assoc]; exact hR₁) y₀ y₁ hy₀ (by rw [Category.assoc]; exact hy₁) u u₁ u'
    u'' G _ α β G'' _ α'' β'' hα hβ hL hα'' hβ'' hL'' W₀ _ k₀ (e ≫ m'') hk₀ hk'' hββ
  obtain ⟨ee, hqe, hlab, hback⟩ := GalTrans.compare u u₁ lb lb₁ P₀ ka ka' hka hka' lka lka'
  have hrN : 1 ≤ D.X.S.r * D.X.S.N := Nat.mul_pos D.X.S.r_pos (by have := D.X.S.N_ge; omega)
  refine ⟨c₁, hc₁, R'', fg₁, frac₁, hth₁, hev₁, ρ'', u'', hS₁, hi₁, hu₁, hR₁, G'', _, α'', β'', hα'', hβ'', hL'', y₁, hy₁,
    u₁, lb₁, ee.symm.trans j, fun χ => ?_, fun x χ hχ => ?_, fun m A pk' pk₂' x' x₂' w w₂ hm hQ' hQ₂' hw hw₂ hA => ?_⟩
  · rw [← ee.apply_symm_apply χ, hqe, ee.apply_symm_apply]
    exact hq (ee.symm χ)
  · obtain ⟨w, hw1, hw2⟩ := hmt x
    obtain ⟨w₀, hw₀, hw₀e, hw₀k⟩ := htw x w hw1
    have c'' : w₀ ≫ (e ≫ m'') ≫ α'' =
        spMap ((σ : D.X.Ω₁ →+* D.X.Ω₁).comp R''.val.toRingHom) ≫ (ρ''.pt x).left := by
      rw [Category.assoc, reassoc_of% hw₀e, hw2, ← Category.assoc, GalTrans.sp_comp rfl]
    obtain ⟨v, xo, xo', hv, hva, hva', hx, hx'⟩ := htor (a x) x w₀ hw₀ hw₀k c''
    obtain ⟨pk, pk', hQ, hQ', hcm⟩ := hlab _ xo xo' v hrN
      (GlobalTheory.LabelTorsion.pow_eq_one_of_over_label _ ρ' p y₀ u _ xo hx)
      (GlobalTheory.LabelTorsion.pow_eq_one_of_over_label _ ρ'' p y₁ u₁ _ xo' hx') hv hva hva'
    refine (hyy (a x) pk.y (lb.yy_eq _ pk xo hQ hx)).trans (GalTrans.cm_mk ?_)
    have c2 : CongMod (D.X.S.r * D.X.S.N) χ pk'.y := GalTrans.cm_of_mk (hχ.symm.trans (lb₁.yy_eq x pk' xo' hQ' hx'))
    simpa using GalTrans.cm_symm (GalTrans.cm_map (ee.symm.trans j).toAddMonoidHom (GalTrans.cm_trans c2 hcm))
  · obtain ⟨pk, xo, vo, hQ, -, hvo, hvoa, hvoa', c1⟩ := hback m pk' x' hm hQ'
    obtain ⟨pk₂, xo₂, vo₂, hQ₂, -, hvo₂, hvo₂a, hvo₂a', c2⟩ := hback m pk₂' x₂' hm hQ₂'
    obtain ⟨g, hg⟩ := exists_lift_rat hα (xo.left ≫ u.φ)
    obtain ⟨g₂, hg₂⟩ := exists_lift_rat hα (xo₂.left ≫ u.φ)
    have e1 : g ≫ β = w ≫ β'' := hβeq vo g w hvo (by rw [hg, ← hvoa, Category.assoc])
      (by rw [hw, ← hvoa', Category.assoc])
    have e2 : g₂ ≫ β = w₂ ≫ β'' := hβeq vo₂ g₂ w₂ hvo₂ (by rw [hg₂, ← hvo₂a, Category.assoc])
      (by rw [hw₂, ← hvo₂a', Category.assoc])
    have hA' : g₂ ≫ β = g ≫ β ≫ (Xo.univ.t.act.act A).left := by
      rw [e2, hA, ← Category.assoc, ← e1, Category.assoc]
    have c3 := hall m A pk pk₂ xo xo₂ g g₂ hm hQ hQ₂ hg hg₂ hA'
    have c4 : CongMod m ((ee.symm.trans j) pk₂'.y) (j pk₂.y) := by
      have := GalTrans.cm_map (ee.symm.trans j).toAddMonoidHom c2
      rwa [show (ee.symm.trans j).toAddMonoidHom (ee pk₂.y) = j pk₂.y from
        congrArg j (ee.symm_apply_apply pk₂.y)] at this
    have c5 : CongMod m ((ee.symm.trans j) pk'.y) (j pk.y) := by
      have := GalTrans.cm_map (ee.symm.trans j).toAddMonoidHom c1
      rwa [show (ee.symm.trans j).toAddMonoidHom (ee pk.y) = j pk.y from
        congrArg j (ee.symm_apply_apply pk.y)] at this
    have c6 : CongMod m (A • j pk.y) (A • (ee.symm.trans j) pk'.y) :=
      GalTrans.cm_symm (GalTrans.cm_map (DistribSMul.toAddMonoidHom _ A) c5)
    exact GalTrans.cm_trans c4 (GalTrans.cm_trans c3 c6)

end GlobalTheory.UPoinc.UGalTrans
end
end
end
