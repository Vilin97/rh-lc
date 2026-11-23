module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Mathlib.AlgebraicGeometry.Noetherian
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoNhdOfStalkBaseChange

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.StalkLBIso

set_option backward.isDefEq.respectTransparency false

theorem lbIso_pull_iff {X Y : Scheme.{0}} {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) (f : Y ⟶ X) :
    LBIso (A.pull f) (B.pull f) ↔
      CechPic.pull f (CechPic.cls A hA) = CechPic.pull f (CechPic.cls B hB) := by
  rw [← CechPic.cls_pull hA f (pull_isLB hA f), ← CechPic.cls_pull hB f (pull_isLB hB f)]
  exact (CechPic.cls_eq_iff _ _).symm

theorem exists_lbIso_nhd : ∀ {S X : Scheme.{0}} [IsLocallyNoetherian S] (h : X ⟶ S) [QuasiCompact h]
    [QuasiSeparated h] (x : S) (A B : LB X), A.IsLB → B.IsLB →
    LBIso (A.pull (pullback.fst h (S.fromSpecStalk x))) (B.pull (pullback.fst h (S.fromSpecStalk x))) →
    ∃ W : S.Opens, x ∈ W ∧ LBIso (A.pull (h ⁻¹ᵁ W).ι) (B.pull (h ⁻¹ᵁ W).ι) := by
  intro S X _ h _ _ x A B hA hB hAB

  have hpb : IsPullback (pullback.fst h (S.fromSpecStalk x)) (pullback.snd h (S.fromSpecStalk x)) h
      (S.fromSpecStalk x) := IsPullback.of_hasPullback _ _
  have hc := (GlobalTheory.StalkLimit.nonempty_isLimit hpb).some
  obtain ⟨V₀⟩ : Nonempty (GlobalTheory.StalkLimit.AffNhd x) := IsCofiltered.nonempty
  have : IsAffine V₀.1.toScheme := V₀.2.2
  have : CompactSpace ((GlobalTheory.StalkLimit.diagram x h).obj V₀) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd h V₀.1.ι)
  have : QuasiSeparatedSpace ((GlobalTheory.StalkLimit.diagram x h).obj V₀) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd h V₀.1.ι)

  have h0 : LBIso ((A.pull (pullback.fst h V₀.1.ι)).pull ((GlobalTheory.StalkLimit.cone hpb).π.app V₀))
      ((B.pull (pullback.fst h V₀.1.ι)).pull ((GlobalTheory.StalkLimit.cone hpb).π.app V₀)) := by
    rw [lbIso_pull_iff (pull_isLB hA _) (pull_isLB hB _), CechPic.cls_pull hA, CechPic.cls_pull hB,
      ← CechPic.pull_comp, ← CechPic.pull_comp, GlobalTheory.StalkLimit.cone_π_fst, ← lbIso_pull_iff hA hB]
    exact hAB

  obtain ⟨j, f, hj⟩ := GlobalTheory.exists_lbIso_of_isLimit (GlobalTheory.StalkLimit.diagram x h)
    (fun V => (GlobalTheory.StalkLimit.cone hpb).π.app V) (fun f => (GlobalTheory.StalkLimit.cone hpb).w f) hc
    (A.pull (pullback.fst h V₀.1.ι)) (B.pull (pullback.fst h V₀.1.ι)) (pull_isLB hA _) (pull_isLB hB _) h0
  have hj' : CechPic.pull (pullback.fst h j.1.ι) (CechPic.cls A hA) =
      CechPic.pull (pullback.fst h j.1.ι) (CechPic.cls B hB) := by
    rw [lbIso_pull_iff (pull_isLB hA _) (pull_isLB hB _), CechPic.cls_pull hA, CechPic.cls_pull hB,
      ← CechPic.pull_comp, ← CechPic.pull_comp, GlobalTheory.StalkLimit.diagram_map_fst] at hj
    exact hj

  refine ⟨j.1, j.2.1, ?_⟩
  rw [lbIso_pull_iff hA hB, ← pullbackRestrictIsoRestrict_inv_fst, CechPic.pull_comp, CechPic.pull_comp, hj']

end GlobalTheory.StalkLBIso
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoNhdOfStalkBaseChangeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_lineBundleIso_nhd_of_stalk_baseChange : ∀ {S X : Scheme.{0}} [IsLocallyNoetherian S] (h : X ⟶ S) [QuasiCompact h] [QuasiSeparated h] (x : S) (A B : LB X), A.IsLB → B.IsLB → LBIso (A.pull (pullback.fst h (S.fromSpecStalk x))) (B.pull (pullback.fst h (S.fromSpecStalk x))) → ∃ W : S.Opens, x ∈ W ∧ LBIso (A.pull (h ⁻¹ᵁ W).ι) (B.pull (h ⁻¹ᵁ W).ι) := by
  first | exact @GlobalTheory.StalkLBIso.exists_lbIso_nhd | exact GlobalTheory.StalkLBIso.exists_lbIso_nhd | (intros; apply GlobalTheory.StalkLBIso.exists_lbIso_nhd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleNhdOfStalkBaseChange

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.StalkLB

set_option backward.isDefEq.respectTransparency false

theorem exists_lb_nhd : ∀ {S X : Scheme.{0}} [IsLocallyNoetherian S] (h : X ⟶ S) [QuasiCompact h]
    [QuasiSeparated h] (x : S) (N : LB (pullback h (S.fromSpecStalk x))), N.IsLB →
    ∃ W : S.Opens, x ∈ W ∧ ∃ N' : LB ↑(h ⁻¹ᵁ W), N'.IsLB ∧
      ∀ a : pullback h (S.fromSpecStalk x) ⟶ ↑(h ⁻¹ᵁ W),
        a ≫ (h ⁻¹ᵁ W).ι = pullback.fst h (S.fromSpecStalk x) → LBIso (N'.pull a) N := by
  intro S X _ h _ _ x N hN
  have hpb := IsPullback.of_hasPullback h (S.fromSpecStalk x)
  have hlim : IsLimit (GlobalTheory.schemeConeOfFamily (GlobalTheory.StalkLimit.diagram x h)
      (fun V => (GlobalTheory.StalkLimit.cone hpb).π.app V) (fun f => (GlobalTheory.StalkLimit.cone hpb).w f)) :=
    (GlobalTheory.StalkLimit.nonempty_isLimit hpb).some
  have hcpt : ∀ V : GlobalTheory.StalkLimit.AffNhd x, CompactSpace ((GlobalTheory.StalkLimit.diagram x h).obj V) := by
    intro V
    haveI : IsAffine V.1.toScheme := V.2.2
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd h V.1.ι)
  have hqs : ∀ V : GlobalTheory.StalkLimit.AffNhd x,
      QuasiSeparatedSpace ((GlobalTheory.StalkLimit.diagram x h).obj V) := by
    intro V
    haveI : IsAffine V.1.toScheme := V.2.2
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd h V.1.ι)
  obtain ⟨j, M, hM, -, hall⟩ := GlobalTheory.LBLimit.exists_lb_of_isLimit (GlobalTheory.StalkLimit.diagram x h)
    (fun V => (GlobalTheory.StalkLimit.cone hpb).π.app V) (fun f => (GlobalTheory.StalkLimit.cone hpb).w f) hlim N hN
  refine ⟨j.1, j.2.1, M.pull (pullbackRestrictIsoRestrict h j.1).inv, LB.isLB_pull hM _, fun a ha => ?_⟩
  refine LBIso.symm (hall _ a (pullbackRestrictIsoRestrict h j.1).inv ?_)
  have hfst : (GlobalTheory.StalkLimit.cone hpb).π.app j ≫ pullback.fst h j.1.ι =
      pullback.fst h (S.fromSpecStalk x) := GlobalTheory.StalkLimit.cone_π_fst hpb j
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackRestrictIsoRestrict_inv_fst, ha, hfst]
  · rw [← cancel_mono j.1.ι]
    simp only [Category.assoc]
    rw [← pullback.condition, pullbackRestrictIsoRestrict_inv_fst_assoc, reassoc_of% ha,
      reassoc_of% hfst]

end GlobalTheory.StalkLB
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleNhdOfStalkBaseChangeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_lineBundle_nhd_of_stalk_baseChange : ∀ {S X : Scheme.{0}} [IsLocallyNoetherian S] (h : X ⟶ S) [QuasiCompact h] [QuasiSeparated h] (x : S) (N : LB (pullback h (S.fromSpecStalk x))), N.IsLB → ∃ W : S.Opens, x ∈ W ∧ ∃ N' : LB ↑(h ⁻¹ᵁ W), N'.IsLB ∧ ∀ a : pullback h (S.fromSpecStalk x) ⟶ ↑(h ⁻¹ᵁ W), a ≫ (h ⁻¹ᵁ W).ι = pullback.fst h (S.fromSpecStalk x) → LBIso (N'.pull a) N := by
  first | exact @GlobalTheory.StalkLB.exists_lb_nhd | exact GlobalTheory.StalkLB.exists_lb_nhd | (intros; apply GlobalTheory.StalkLB.exists_lb_nhd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleSpreadFromLocalScheme

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SpreadLB

open GlobalTheory.CechPic in
theorem exists_spread : ∀ {S Y U YU : Scheme.{0}} [IsLocallyNoetherian S] (f : Y ⟶ S) [QuasiCompact f] [QuasiSeparated f] (j : U ⟶ S) [IsOpenImmersion j] (e : YU ⟶ Y) (fU : YU ⟶ U), IsPullback e fU f j → ∀ (L : LB YU), L.IsLB → ∀ (x : S) (N : LB (pullback f (S.fromSpecStalk x))), N.IsLB → (∀ (T : Scheme.{0}) (a : T ⟶ pullback f (S.fromSpecStalk x)) (b : T ⟶ YU), a ≫ pullback.fst f (S.fromSpecStalk x) = b ≫ e → LBIso (N.pull a) (L.pull b)) → ∃ W : S.Opens, x ∈ W ∧ ∃ N' : LB ↑(f ⁻¹ᵁ W), N'.IsLB ∧ ∀ (T : Scheme.{0}) (a : T ⟶ ↑(f ⁻¹ᵁ W)) (b : T ⟶ YU), a ≫ (f ⁻¹ᵁ W).ι = b ≫ e → LBIso (N'.pull a) (L.pull b) := by

  intro S Y U YU _ f _ _ j _ e fU hpb L hL x N hN hag
  obtain ⟨W₁, hx₁, N₁, hN₁, hq⟩ := GlobalTheory.T.exists_lineBundle_nhd_of_stalk_baseChange f x N hN
  have hr1 : Set.range (pullback.fst f (S.fromSpecStalk x)) ⊆ Set.range (f ⁻¹ᵁ W₁).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    show f (pullback.fst f (S.fromSpecStalk x) y) ∈ W₁
    have hsp : f (pullback.fst f (S.fromSpecStalk x) y) ⤳ x := by
      have : f (pullback.fst f (S.fromSpecStalk x) y) ∈ Set.range (S.fromSpecStalk x) :=
        ⟨pullback.snd f (S.fromSpecStalk x) y, by rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]⟩
      rwa [Scheme.range_fromSpecStalk] at this
    exact hsp.mem_open W₁.isOpen hx₁
  let q₁ := IsOpenImmersion.lift (f ⁻¹ᵁ W₁).ι (pullback.fst f (S.fromSpecStalk x)) hr1
  have hq₁ : q₁ ≫ (f ⁻¹ᵁ W₁).ι = pullback.fst f (S.fromSpecStalk x) := IsOpenImmersion.lift_fac _ _ _
  have iso1 := hq q₁ hq₁
  haveI : IsOpenImmersion e := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hpb.flip inferInstance
  haveI : QuasiCompact e := MorphismProperty.of_isPullback (P := @QuasiCompact) hpb.flip inferInstance
  haveI : QuasiCompact (f ⁻¹ᵁ W₁).ι := MorphismProperty.of_isPullback (P := @QuasiCompact) (isPullback_morphismRestrict f W₁) inferInstance
  let h : pullback (f ⁻¹ᵁ W₁).ι e ⟶ S := pullback.fst (f ⁻¹ᵁ W₁).ι e ≫ (f ⁻¹ᵁ W₁).ι ≫ f

  obtain ⟨W₂, hx₂, iso2⟩ := GlobalTheory.T.exists_lineBundleIso_nhd_of_stalk_baseChange h x (N₁.pull (pullback.fst (f ⁻¹ᵁ W₁).ι e))
    (L.pull (pullback.snd (f ⁻¹ᵁ W₁).ι e)) (pull_isLB hN₁ _) (pull_isLB hL _) (by
      set r := pullback.fst h (S.fromSpecStalk x)
      have hs : (r ≫ pullback.fst (f ⁻¹ᵁ W₁).ι e ≫ (f ⁻¹ᵁ W₁).ι) ≫ f = pullback.snd h (S.fromSpecStalk x) ≫ S.fromSpecStalk x := by
        rw [← pullback.condition]; simp only [h, Category.assoc]; rfl
      let s := pullback.lift _ _ hs
      have hs1 : s ≫ q₁ = r ≫ pullback.fst (f ⁻¹ᵁ W₁).ι e := by
        rw [← cancel_mono (f ⁻¹ᵁ W₁).ι, Category.assoc, hq₁]; simp only [s, pullback.lift_fst, Category.assoc]
      have hs2 : s ≫ pullback.fst f (S.fromSpecStalk x) = (r ≫ pullback.snd (f ⁻¹ᵁ W₁).ι e) ≫ e := by
        simp only [s, pullback.lift_fst, Category.assoc, pullback.condition]
      have i3 := (cls_eq_iff (pull_isLB hN _) (pull_isLB hL _)).2 (hag _ s _ hs2)
      have i1 := (cls_eq_iff (pull_isLB hN₁ _) hN).2 iso1
      refine (cls_eq_iff (pull_isLB (pull_isLB hN₁ _) r) (pull_isLB (pull_isLB hL _) r)).1 ?_
      rw [cls_pull (pull_isLB hN₁ _), cls_pull hN₁, cls_pull (pull_isLB hL _), cls_pull hL, ← pull_comp, ← pull_comp, ← hs1,
        pull_comp, ← cls_pull hN₁ _ (pull_isLB hN₁ _), i1, ← cls_pull hN _ (pull_isLB hN _), i3, cls_pull hL])
  refine ⟨W₁ ⊓ W₂, ⟨hx₁, hx₂⟩, ?_⟩
  have hle : f ⁻¹ᵁ (W₁ ⊓ W₂) ≤ f ⁻¹ᵁ W₁ := fun y hy => hy.1
  refine ⟨N₁.pull (Y.homOfLE hle), pull_isLB hN₁ _, fun T a b hab => ?_⟩
  have hc : (a ≫ Y.homOfLE hle) ≫ (f ⁻¹ᵁ W₁).ι = b ≫ e := by rw [Category.assoc, Scheme.homOfLE_ι, hab]
  let c := pullback.lift _ _ hc
  have hcr : Set.range c ⊆ Set.range (h ⁻¹ᵁ W₂).ι := by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    show h (c t) ∈ W₂
    have : c ≫ h = a ≫ (f ⁻¹ᵁ (W₁ ⊓ W₂)).ι ≫ f := by
      simp only [h, c, pullback.lift_fst_assoc, Category.assoc, Scheme.homOfLE_ι_assoc]
    rw [← Scheme.Hom.comp_apply, this, Scheme.Hom.comp_apply]
    exact ((a t).2 : _).2
  let d := IsOpenImmersion.lift (h ⁻¹ᵁ W₂).ι c hcr
  have hd : d ≫ (h ⁻¹ᵁ W₂).ι = c := IsOpenImmersion.lift_fac _ _ _
  have i2 := (cls_eq_iff (pull_isLB (pull_isLB hN₁ _) _) (pull_isLB (pull_isLB hL _) _)).2 iso2
  refine (cls_eq_iff (pull_isLB (pull_isLB hN₁ _) a) (pull_isLB hL b)).1 ?_
  have e1 : a ≫ Y.homOfLE hle = d ≫ (h ⁻¹ᵁ W₂).ι ≫ pullback.fst (f ⁻¹ᵁ W₁).ι e := by
    rw [← Category.assoc, hd]; simp only [c, pullback.lift_fst]
  have e2 : b = d ≫ (h ⁻¹ᵁ W₂).ι ≫ pullback.snd (f ⁻¹ᵁ W₁).ι e := by
    rw [← Category.assoc, hd]; simp only [c, pullback.lift_snd]
  rw [cls_pull (pull_isLB hN₁ _), cls_pull hN₁, ← pull_comp, e1, cls_pull hL, e2, pull_comp, pull_comp, pull_comp d,
    pull_comp (h ⁻¹ᵁ W₂).ι, ← cls_pull hN₁ _ (pull_isLB hN₁ _), ← cls_pull (pull_isLB hN₁ _) _ (pull_isLB (pull_isLB hN₁ _) _), i2,
    cls_pull (pull_isLB hL _), cls_pull hL]

end GlobalTheory.SpreadLB
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleSpreadFromLocalSchemeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_lineBundle_spread_from_localScheme : ∀ {S Y U YU : Scheme.{0}} [IsLocallyNoetherian S] (f : Y ⟶ S) [QuasiCompact f] [QuasiSeparated f] (j : U ⟶ S) [IsOpenImmersion j] (e : YU ⟶ Y) (fU : YU ⟶ U), IsPullback e fU f j → ∀ (L : LB YU), L.IsLB → ∀ (x : S) (N : LB (pullback f (S.fromSpecStalk x))), N.IsLB → (∀ (T : Scheme.{0}) (a : T ⟶ pullback f (S.fromSpecStalk x)) (b : T ⟶ YU), a ≫ pullback.fst f (S.fromSpecStalk x) = b ≫ e → LBIso (N.pull a) (L.pull b)) → ∃ W : S.Opens, x ∈ W ∧ ∃ N' : LB ↑(f ⁻¹ᵁ W), N'.IsLB ∧ ∀ (T : Scheme.{0}) (a : T ⟶ ↑(f ⁻¹ᵁ W)) (b : T ⟶ YU), a ≫ (f ⁻¹ᵁ W).ι = b ≫ e → LBIso (N'.pull a) (L.pull b) := by
  first | exact @GlobalTheory.SpreadLB.exists_spread | exact GlobalTheory.SpreadLB.exists_spread | (intros; apply GlobalTheory.SpreadLB.exists_spread <;> assumption)
end
end
