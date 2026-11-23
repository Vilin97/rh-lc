module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefLineBundleOfBaseChangeFieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingComplexEmbeddedFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingNumberFieldTwist
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolAVDescendsToCountableSubfield
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetIsProjOverDescends
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeDescentSmoothDimension
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonLineBundleCohomologyProjBaseChangeIfStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaKeyRuleExistsOfAlgebraicInvariants
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenConnectedComponentOfNoetherianSpace

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBigLineBundlePullbackFieldExtensionIff

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

namespace GlobalTheory.BigFieldChange

theorem isBig_pull_iff : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k)
    (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → IsProjOver q →
    topologicalKrullDim X = topologicalKrullDim Y → ∀ L : LB Y, L.IsLB →
    ((letI := algebraΓOfHom q; IsBig E (L.pull π)) ↔ (letI := algebraΓOfHom p; IsBig k L)) := by
  intro k E _ _ _ Y X p q π H hp hq hd L hL
  letI := algebraΓOfHom p
  letI := algebraΓOfHom q
  have : IsProper p := by
    obtain ⟨N, i, hi, e⟩ := hp
    have := isProper_str k N
    rw [← e]
    infer_instance
  have hL' := LB.isLB_pull hL π
  have e : ∀ m : ℕ, lbH0 E (lbPow (L.pull π) m) = lbH0 k (lbPow L m) := fun m => by
    rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow hL' m) (LB.isLB_pull (isLB_lbPow hL m) π)
      (by rw [cls_lbPow hL', cls_pull hL, cls_pull (isLB_lbPow hL m), cls_lbPow hL, map_nsmul])]
    exact FieldChangeInter.hdim_pull H (isLB_lbPow hL m) 0
  constructor
  · intro h
    obtain ⟨D, hD, c, hc, hm⟩ := h.3
    exact ⟨hL, fun m => finite_coh_zero_twist_of_isProjOver (f := p) (fun _ => rfl) hp (isLB_lbPow hL m),
      D, hd.symm.trans hD, c, hc, hm.mono fun m hm => hm.trans_eq (congrArg _ (e m))⟩
  · intro h
    obtain ⟨D, hD, c, hc, hm⟩ := h.3
    exact ⟨hL', fun m => finite_coh_zero_twist_of_isProjOver (f := q) (fun _ => rfl) hq (isLB_lbPow hL' m),
      D, hd.trans hD, c, hc, hm.mono fun m hm => hm.trans_eq (congrArg _ (e m).symm)⟩

end GlobalTheory.BigFieldChange
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBigLineBundlePullbackFieldExtensionIffStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

theorem _root_.GlobalTheory.T.isBigLineBundle_pullback_fieldExtension_iff : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → IsProjOver q → topologicalKrullDim X = topologicalKrullDim Y → ∀ L : LB Y, L.IsLB → ((letI := algebraΓOfHom q; IsBig E (L.pull π)) ↔ (letI := algebraΓOfHom p; IsBig k L)) := by
  first | exact @GlobalTheory.BigFieldChange.isBig_pull_iff | exact GlobalTheory.BigFieldChange.isBig_pull_iff | (intros; apply GlobalTheory.BigFieldChange.isBig_pull_iff <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveLineBundleDescendsToCountableSubfield

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

namespace GlobalTheory.ProjCountableDescent


open GlobalTheory.PolCountableDescent in
theorem projLB_descends_to_countable_subfield : ∀ (K : Type) [Field K] (X : Scheme.{0}) (p : X ⟶ Sp K), IsProjOver p → ∀ (L : LB X), L.IsLB → ∃ (K₁ : Subfield K) (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (ψ : X ⟶ X₁) (L₁ : LB X₁), Countable K₁ ∧ IsProjOver p₁ ∧ IsPullback ψ p p₁ (spMap (algebraMap K₁ K)) ∧ L₁.IsLB ∧ LBIso L (L₁.pull ψ) := by
  intro K _ X p hp L hL
  classical
  obtain ⟨s₀, H₀⟩ := GlobalTheory.exists_finset_isProjOver_descends K ⊥ X p hp
  let K₀ : Subfield K := Subfield.closure (s₀ : Set K)
  obtain ⟨X₀, p₀, φ, hp₀, sq⟩ := H₀ K₀ bot_le Subfield.subset_closure
  have : IsProper p₀ := by
    obtain ⟨N, i, hi, rfl⟩ := hp₀
    have := isProper_str K₀ N
    infer_instance
  obtain ⟨s₂, H₂⟩ := GlobalTheory.LBDescent.exists_lb_subfield K K₀ X₀ X p₀ p φ L hL sq
  let s : Finset K := s₀ ∪ s₂
  let K₁ : Subfield K := Subfield.closure (s : Set K)
  have h : K₀ ≤ K₁ := Subfield.closure_mono (Finset.coe_subset.2 (fun y hy => by simp [s, hy]))
  let inc := spMap (Subfield.inclusion h)
  have sq₁ : IsPullback (pullback.fst p₀ inc) (pullback.snd p₀ inc) p₀ inc := IsPullback.of_hasPullback p₀ inc
  let ψ : X ⟶ pullback p₀ inc := sq₁.lift φ (p ≫ spMap K₁.subtype)
    (by rw [Category.assoc, spMap_subtype_comp h, sq.w])
  have hψ₁ : ψ ≫ pullback.fst p₀ inc = φ := sq₁.lift_fst _ _ _
  have hψ₂ : ψ ≫ pullback.snd p₀ inc = p ≫ spMap K₁.subtype := sq₁.lift_snd _ _ _
  obtain ⟨L₁, hL₁, hI⟩ := H₂ K₁ h (subset_closure_of_subset (fun y hy => by simp [s, hy])) _ _ _ ψ
    sq₁ hψ₁ hψ₂
  refine ⟨K₁, _, pullback.snd p₀ inc, ψ, L₁, countable_closure s,
    ProjSpace.isProjOver_pullback_snd _ hp₀, ?_, hL₁, hI⟩
  refine IsPullback.of_right (t := sq₁) ?_ hψ₂
  have e : spMap (algebraMap K₁ K) ≫ inc = spMap K₀.subtype := spMap_subtype_comp h
  rw [hψ₁, e]
  exact sq

end GlobalTheory.ProjCountableDescent
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveLineBundleDescendsToCountableSubfieldStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

theorem _root_.GlobalTheory.T.projectiveLineBundle_descends_to_countable_subfield : ∀ (K : Type) [Field K] (X : Scheme.{0}) (p : X ⟶ Sp K), IsProjOver p → ∀ (L : LB X), L.IsLB → ∃ (K₁ : Subfield K) (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (ψ : X ⟶ X₁) (L₁ : LB X₁), Countable K₁ ∧ IsProjOver p₁ ∧ IsPullback ψ p p₁ (spMap (algebraMap K₁ K)) ∧ L₁.IsLB ∧ LBIso L (L₁.pull ψ) := by
  first | exact @GlobalTheory.ProjCountableDescent.projLB_descends_to_countable_subfield | exact GlobalTheory.ProjCountableDescent.projLB_descends_to_countable_subfield | (intros; apply GlobalTheory.ProjCountableDescent.projLB_descends_to_countable_subfield <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelDimGeomConnectedDescendFieldExtension

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

namespace GlobalTheory.FieldDescentSm

theorem smoothOfRelativeDimension_and_geometricallyConnected_descend : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → ∀ D : ℕ, Nonempty X → SmoothOfRelativeDimension D q → GeometricallyConnected q → SmoothOfRelativeDimension D p ∧ GeometricallyConnected p := by
  intro k E _ _ _ Y X p q π H D hX hD hq
  have hf := GlobalTheory.FieldDescentAb.fpqc_spMap (algebraMap k E)
  have hsq : Smooth q := SmoothOfRelativeDimension.smooth D q
  have hsm : Smooth p :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) H.flip hf hsq
  have hp : GeometricallyConnected p :=
    GlobalTheory.FieldDescentAb.geometricallyConnected_of_isPullback (algebraMap k E) H
  refine ⟨?_, hp⟩
  have hc : ConnectedSpace Y :=
    hp.geometrically_connectedSpace (𝟙 _) (𝟙 Y) p (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨x⟩ := hX
  obtain ⟨D', hD'⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_dim_of_preconnected p (π x)
  have h' : SmoothOfRelativeDimension D' q :=
    (smoothOfRelativeDimension_isStableUnderBaseChange D').of_isPullback H hD'
  rw [ReciprocityTheory.ChartRestriction.G.H1.dim_unique q hD h' x]
  exact hD'

end GlobalTheory.FieldDescentSm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelDimGeomConnectedDescendFieldExtensionStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

theorem _root_.GlobalTheory.T.smoothOfRelDim_geomConnected_descend_fieldExtension : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → ∀ D : ℕ, Nonempty X → SmoothOfRelativeDimension D q → GeometricallyConnected q → SmoothOfRelativeDimension D p ∧ GeometricallyConnected p := by
  first | exact @GlobalTheory.FieldDescentSm.smoothOfRelativeDimension_and_geometricallyConnected_descend | exact GlobalTheory.FieldDescentSm.smoothOfRelativeDimension_and_geometricallyConnected_descend | (intros; apply GlobalTheory.FieldDescentSm.smoothOfRelativeDimension_and_geometricallyConnected_descend <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegOfNadelVanishingPair

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

namespace GlobalTheory.KVFromPair

theorem subsingleton_coh_twist (hN : GlobalTheory.Published.NefNumerics) (hV : GlobalTheory.Published.NadelVanishingPair)
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ) [hs : SmoothOfRelativeDimension D p] (hp : IsProjOver p)
    (K : CanonLB p D) (N : LB X) (h₁ : letI := algebraΓOfHom p; IsNef k N)
    (h₂ : letI := algebraΓOfHom p; IsBig k N) (q : ℕ) (hq : 0 < q) :
    Subsingleton (coh (twist (GlobalTheory.structureModule X) (tens K.bundle N)) q) := by
  have hNl : N.IsLB := by
    letI := algebraΓOfHom p
    exact h₁.isLB
  obtain ⟨K₁, X₁, p₁, ψ, L₁, hc, hp₁, H, hL₁, e⟩ := GlobalTheory.T.projectiveLineBundle_descends_to_countable_subfield k X p hp N hNl
  have hsm : Smooth p := SmoothOfRelativeDimension.smooth D p
  have hg : GeometricallyConnected p := GlobalTheory.geometricallyConnected_of_isAlgClosed p
  obtain ⟨hs₁, hg₁⟩ := GlobalTheory.T.smoothOfRelDim_geomConnected_descend_fieldExtension K₁ k X₁ X p₁ p ψ H D inferInstance hs hg
  have hne : Nonempty X₁ := ⟨ψ (Classical.arbitrary X)⟩
  have hP := LB.isLB_pull hL₁ ψ
  have ec : cls N hNl = cls (L₁.pull ψ) hP := (cls_eq_iff _ _).2 e
  have n₁ := GlobalTheory.T.isNefLineBundle_of_baseChange_field K₁ k X₁ X p₁ p ψ H hp₁ L₁ hL₁ (by
    letI := algebraΓOfHom p
    exact h₁.of_cls_eq hP ec.symm)
  have b₁ := (GlobalTheory.T.isBigLineBundle_pullback_fieldExtension_iff K₁ k X₁ X p₁ p ψ H hp₁ hp
    ((GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth p D hs).trans
      (GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth p₁ D hs₁).symm) L₁ hL₁).1 (by
    letI := algebraΓOfHom p
    exact h₂.of_cls_eq hP ec.symm)
  let C : CanonLB p₁ D := CanonLB.all p₁ D
  have v₁ := GlobalTheory.T.kawamataViehweg_vanishing_complexEmbeddedField hN hV K₁ (GlobalTheory.KeyHouse.nonempty_ringHom_complex K₁) X₁ p₁ D hp₁ hg₁
    C L₁ n₁ b₁ q hq
  have hT := isLB_tens C.isLB hL₁
  have v := (GlobalTheory.T.subsingleton_lineBundleCohomology_projBaseChange_iff K₁ k X₁ X p₁ p ψ H hp₁ hp _ hT q).2 v₁
  have eK : cls K.bundle K.isLB = cls (C.bundle.pull ψ) (LB.isLB_pull C.isLB ψ) := by
    obtain ⟨w, hw, -⟩ := canonLB_baseChange K₁ k _ X₁ X p₁ p ψ D H C K
    exact (cls_eq_iff _ _).2 ⟨w, hw⟩
  obtain ⟨i⟩ := nonempty_twist_iso_of_cls_eq (GlobalTheory.structureModule X) (isLB_tens K.isLB hNl)
    (LB.isLB_pull hT ψ) (by
      rw [cls_tens K.isLB hNl, cls_pull hT, cls_tens C.isLB hL₁, map_add (f := _), eK, ec,
        cls_pull C.isLB, cls_pull hL₁])
  exact (cohOn.mapIso Γ(X, ⊤) ⊤ q i).toEquiv.subsingleton_congr.2 v

theorem kawamataViehweg_of_nadelVanishingPair :
    GlobalTheory.Published.NefNumerics → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.KawamataViehweg := by
  intro hN hV k _ _ _ X a _ D hs hp K N h₁ h₂ q hq
  have ha : a = algebraΓOfHom (strHom k X) := Algebra.algebra_ext _ _ (algebraMap_eq_strHom k X)
  have v := subsingleton_coh_twist hN hV k X (strHom k X) D hp K N (ha ▸ h₁) (ha ▸ h₂) q hq
  exact (cohOn.mapIso Γ(X, ⊤) ⊤ q (Twist.unitTwistIso _)).toEquiv.subsingleton_congr.1 v

end GlobalTheory.KVFromPair
end
end
