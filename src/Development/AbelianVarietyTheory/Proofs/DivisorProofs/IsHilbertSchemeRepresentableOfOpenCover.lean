module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbRep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapEqKerIff
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafDataExtOfOpenCover
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbRep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertPointGlueOpenCoverStatement
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsRepresentableOfCover

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertFunctorLocalRepresentingDataOfRestrict

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HilbGlue

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch

theorem ker_comap_eq_ker_iff {X X' V V' : Scheme.{0}} (m : X' ⟶ X) (v : V ⟶ X) [IsClosedImmersion v]
    (v' : V' ⟶ X') [IsClosedImmersion v'] :
    v.ker.comap m = v'.ker ↔ ∃ w : V' ⟶ V, IsPullback v' w m v := by
  have e : v.ker.subschemeι = inv v.toImage ≫ v := by
    rw [IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι]
  rw [comap_eq_ker_iff]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w ≫ inv v.toImage, ?_⟩
    refine IsPullback.of_iso hw (Iso.refl _) (Iso.refl _) (asIso (inv v.toImage)) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · simp [e]
  · rintro ⟨w, hw⟩
    refine ⟨w ≫ v.toImage, ?_⟩
    refine IsPullback.of_iso hw (Iso.refl _) (Iso.refl _) (asIso v.toImage) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · simp [e]

variable {S Z : Scheme.{0}} (z : Z ⟶ S) (W : S.Opens)

lemma isPullback_restrict {Y : Scheme.{0}} (b : Y ⟶ W.toScheme) :
    IsPullback (pullback.fst (z ∣_ W) b ≫ (z ⁻¹ᵁ W).ι) (pullback.snd (z ∣_ W) b) z (b ≫ W.ι) :=
  IsPullback.paste_horiz (IsPullback.of_hasPullback (z ∣_ W) b) (isPullback_morphismRestrict z W).flip

def restrictIso {Y : Scheme.{0}} (b : Y ⟶ W.toScheme) : pullback (z ∣_ W) b ≅ pullback z (b ≫ W.ι) :=
  (isPullback_restrict z W b).isoPullback

@[reassoc (attr := simp)]
lemma restrictIso_hom_fst {Y : Scheme.{0}} (b : Y ⟶ W.toScheme) :
    (restrictIso z W b).hom ≫ pullback.fst z (b ≫ W.ι) = pullback.fst (z ∣_ W) b ≫ (z ⁻¹ᵁ W).ι :=
  (isPullback_restrict z W b).isoPullback_hom_fst

@[reassoc (attr := simp)]
lemma restrictIso_hom_snd {Y : Scheme.{0}} (b : Y ⟶ W.toScheme) :
    (restrictIso z W b).hom ≫ pullback.snd z (b ≫ W.ι) = pullback.snd (z ∣_ W) b :=
  (isPullback_restrict z W b).isoPullback_hom_snd

lemma restrictIso_inv_snd {Y : Scheme.{0}} (b : Y ⟶ W.toScheme) :
    (restrictIso z W b).inv ≫ pullback.snd (z ∣_ W) b = pullback.snd z (b ≫ W.ι) := by
  rw [Iso.inv_comp_eq, restrictIso_hom_snd]

lemma restrictIso_natural {Y H : Scheme.{0}} (b : Y ⟶ W.toScheme) (h : H ⟶ W.toScheme) (c : Y ⟶ H)
    (hc : c ≫ h = b) (w : c ≫ h ≫ W.ι = b ≫ W.ι) :
    pullback.map (z ∣_ W) b (z ∣_ W) h (𝟙 _) c (𝟙 _) (by simp) (by rw [Category.comp_id, hc]) ≫
      (restrictIso z W h).hom = (restrictIso z W b).hom ≫ bc z c (h ≫ W.ι) (b ≫ W.ι) w := by
  apply pullback.hom_ext
  · simp only [bc, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc, Category.assoc, Category.comp_id,
      restrictIso_hom_fst_assoc, restrictIso_hom_fst]
  · simp only [bc, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc, Category.assoc, Category.comp_id,
      restrictIso_hom_snd_assoc, restrictIso_hom_snd]

theorem isHilbRep_restrict_local : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (W : S.Opens),
    GlobalTheory.HilbertSch.IsHilbRep (z ∣_ W) r → ∃ (T : Scheme.{0}) (y : GlobalTheory.HilbGlue.HPt z r T) (π : T ⟶ W.toScheme),
      IsProper π ∧ y.1 = π ≫ W.ι ∧ ∀ (Y : Scheme.{0}) (x : GlobalTheory.HilbGlue.HPt z r Y) (b : Y ⟶ W.toScheme),
        x.1 = b ≫ W.ι → ∃! c : Y ⟶ T, GlobalTheory.HilbGlue.HPt.map c y = x := by
  intro S Z z r W hR
  obtain ⟨H, h, U, u, hprop, hcl, hfin, hflat, hrk, huniv⟩ := hR
  haveI := hcl
  have hv : IsFinFlatRk ((u ≫ (restrictIso z W h).hom) ≫ pullback.snd z (h ≫ W.ι)) r := by
    rw [Category.assoc, restrictIso_hom_snd]
    exact ⟨hfin, hflat, hrk⟩
  set y := mkPt (h ≫ W.ι) (u ≫ (restrictIso z W h).hom) hv with hy
  refine ⟨H, y, h, hprop, rfl, ?_⟩
  intro Y x b hx
  obtain ⟨g, J⟩ := x
  change g = b ≫ W.ι at hx
  subst hx
  set v' := J.1.subschemeι ≫ (restrictIso z W b).inv with hv'
  have e : v' ≫ pullback.snd (z ∣_ W) b = J.1.subschemeι ≫ pullback.snd z (b ≫ W.ι) := by
    rw [hv', Category.assoc, restrictIso_inv_snd]
  have key : ∀ c : Y ⟶ H, HPt.map c y = ⟨b ≫ W.ι, J⟩ ↔ ∃ hf : c ≫ h = b, ∃ w : J.1.subscheme ⟶ U,
      IsPullback v' w (pullback.map (z ∣_ W) b (z ∣_ W) h (𝟙 _) c (𝟙 _) (by simp)
        (by rw [Category.comp_id, hf])) u := by
    intro c
    constructor
    · intro hc
      have h1 : c ≫ h ≫ W.ι = b ≫ W.ι := congrArg Sigma.fst hc
      have hf : c ≫ h = b := by
        rw [← cancel_mono W.ι, Category.assoc]
        exact h1
      refine ⟨hf, ?_⟩
      rw [HPt.map_eq_mk_iff c y h1] at hc
      have hc' : (u ≫ (restrictIso z W h).hom).ker.comap (bc z c (h ≫ W.ι) (b ≫ W.ι) h1) =
          J.1.subschemeι.ker := hc.trans (Scheme.IdealSheafData.ker_subschemeι _).symm
      obtain ⟨w, hw⟩ := (ker_comap_eq_ker_iff _ _ _).1 hc'
      refine ⟨w, ?_⟩
      refine IsPullback.of_iso hw (Iso.refl _) (restrictIso z W b).symm (Iso.refl _) (restrictIso z W h).symm
        ?_ ?_ ?_ ?_
      · simp [hv']
      · simp
      · simp only [Iso.symm_hom]
        rw [Iso.comp_inv_eq, Category.assoc, restrictIso_natural z W b h c hf h1, Iso.inv_hom_id_assoc]
      · simp
    · rintro ⟨hf, w, hw⟩
      have h1 : c ≫ h ≫ W.ι = b ≫ W.ι := by rw [← Category.assoc, hf]
      rw [HPt.map_eq_mk_iff c y h1]
      refine (?_ : _ = J.1.subschemeι.ker).trans (Scheme.IdealSheafData.ker_subschemeι _)
      refine (ker_comap_eq_ker_iff _ (u ≫ (restrictIso z W h).hom) _).2 ⟨w, ?_⟩
      refine IsPullback.of_iso hw (Iso.refl _) (restrictIso z W b) (Iso.refl _) (restrictIso z W h) ?_ ?_ ?_ ?_
      · simp [hv']
      · simp
      · exact restrictIso_natural z W b h c hf h1
      · simp
  have hJ := J.2
  rw [← e] at hJ
  obtain ⟨f, hfP, huniq⟩ := huniv Y b _ v' inferInstance hJ.1 hJ.2.1 hJ.2.2
  exact ⟨f, (key f).2 hfP, fun c hc => huniq c ((key c).1 hc)⟩

end GlobalTheory.HilbGlue
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertFunctorLocalRepresentingDataOfRestrictStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue

theorem _root_.GlobalTheory.T.hilbertFunctor_local_representing_data_of_restrict : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (W : S.Opens), GlobalTheory.HilbertSch.IsHilbRep (z ∣_ W) r → ∃ (T : Scheme.{0}) (y : GlobalTheory.HilbGlue.HPt z r T) (π : T ⟶ W.toScheme), IsProper π ∧ y.1 = π ≫ W.ι ∧ ∀ (Y : Scheme.{0}) (x : GlobalTheory.HilbGlue.HPt z r Y) (b : Y ⟶ W.toScheme), x.1 = b ≫ W.ι → ∃! c : Y ⟶ T, GlobalTheory.HilbGlue.HPt.map c y = x := by
  first | exact @GlobalTheory.HilbGlue.isHilbRep_restrict_local | exact GlobalTheory.HilbGlue.isHilbRep_restrict_local | (intros; apply GlobalTheory.HilbGlue.isHilbRep_restrict_local <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertPointEqOfOpenCover

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue

set_option autoImplicit false

namespace GlobalTheory.HilbGlue

theorem idealSheaf_ext_of_openImmersions {P : Scheme.{0}} {ι : Type*} {X : ι → Scheme.{0}}
    (f : ∀ i, X i ⟶ P) [∀ i, IsOpenImmersion (f i)] (hf : ∀ x : P, ∃ i y, f i y = x)
    (I J : P.IdealSheafData) (h : ∀ i, I.comap (f i) = J.comap (f i)) : I = J := by
  apply GlobalTheory.HilbAff.idealSheafData_ext_of_openCover <;> assumption

end GlobalTheory.HilbGlue

theorem GlobalTheory.HilbGlue.HPt.ext_openCover : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (Y : Scheme.{0}) (𝒰 : Y.OpenCover) (x x' : GlobalTheory.HilbGlue.HPt z r Y), (∀ i, GlobalTheory.HilbGlue.HPt.map (𝒰.f i) x = GlobalTheory.HilbGlue.HPt.map (𝒰.f i) x') → x = x' := by
  intro S Z z r Y 𝒰 x x' e
  obtain ⟨g, I⟩ := x
  obtain ⟨g', I'⟩ := x'
  obtain rfl : g = g' := 𝒰.hom_ext _ _ fun i => congrArg Sigma.fst (e i)
  rw [HPt.mk_eq_mk_iff]
  have hP : ∀ i : 𝒰.I₀, IsPullback (pullback.snd z (𝒰.f i ≫ g)) (bc z (𝒰.f i) g (𝒰.f i ≫ g) rfl) (𝒰.f i)
      (pullback.snd z g) := fun i => (isPullback_bc z (𝒰.f i) g (𝒰.f i ≫ g) rfl).flip
  haveI : ∀ i : 𝒰.I₀, IsOpenImmersion (bc z (𝒰.f i) g (𝒰.f i ≫ g) rfl) := fun i =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hP i) inferInstance
  refine idealSheaf_ext_of_openImmersions (ι := 𝒰.I₀) (X := fun i => pullback z (𝒰.f i ≫ g)) (fun i => bc z (𝒰.f i) g (𝒰.f i ≫ g) rfl) ?_ I.1 I'.1 fun i => ?_
  · intro x
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq (pullback.snd z g x)
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd z g)
      (g := 𝒰.f i) x y hy.symm
    refine ⟨i, (isPullback_bc z (𝒰.f i) g (𝒰.f i ≫ g) rfl).isoPullback.inv w, ?_⟩
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hw]
  · have := (HPt.mk_eq_mk_iff _ _).1 (e i)
    exact this
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertPointEqOfOpenCoverStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue

theorem _root_.GlobalTheory.T.hilbert_point_eq_of_open_cover : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (Y : Scheme.{0}) (𝒰 : Y.OpenCover) (x x' : GlobalTheory.HilbGlue.HPt z r Y), (∀ i, GlobalTheory.HilbGlue.HPt.map (𝒰.f i) x = GlobalTheory.HilbGlue.HPt.map (𝒰.f i) x') → x = x' := by
  first | exact @GlobalTheory.HilbGlue.HPt.ext_openCover | exact GlobalTheory.HilbGlue.HPt.ext_openCover | (intros; apply GlobalTheory.HilbGlue.HPt.ext_openCover <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfRepresentsHilbertFunctorOfLocal

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue

namespace GlobalTheory.HilbGlue

theorem isProper_of_represents_of_local_proper : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (H : Scheme.{0}) (u : GlobalTheory.HilbGlue.HPt z r H), (∀ (T : Scheme.{0}) (x : GlobalTheory.HilbGlue.HPt z r T), ∃! c : T ⟶ H, GlobalTheory.HilbGlue.HPt.map c u = x) → (∀ s : S, ∃ W : S.Opens, s ∈ W ∧ ∃ (T : Scheme.{0}) (y : GlobalTheory.HilbGlue.HPt z r T) (π : T ⟶ W.toScheme), IsProper π ∧ y.1 = π ≫ W.ι ∧ ∀ (Y : Scheme.{0}) (x : GlobalTheory.HilbGlue.HPt z r Y) (b : Y ⟶ W.toScheme), x.1 = b ≫ W.ι → ∃! c : Y ⟶ T, GlobalTheory.HilbGlue.HPt.map c y = x) → IsProper u.1 := by
  intro S Z z r H u hu hloc
  choose W hsW T y π hπ hy hT using hloc
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper) W ?_ ?_
  · rw [eq_top_iff]
    intro s _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨s, hsW s⟩
  intro s
  set V : H.Opens := u.1 ⁻¹ᵁ W s
  have hx1 : (HPt.map V.ι u).1 = (u.1 ∣_ W s) ≫ (W s).ι := by
    change V.ι ≫ u.1 = _
    rw [morphismRestrict_ι]
  obtain ⟨φ, hφ, -⟩ := hT s V (HPt.map V.ι u) (u.1 ∣_ W s) hx1
  obtain ⟨ψ, hψ, -⟩ := hu (T s) (y s)
  have hψ1 : ψ ≫ u.1 = π s ≫ (W s).ι := by
    rw [← hy s, ← hψ]; rfl
  have hrange : Set.range ψ ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    change u.1 (ψ t) ∈ W s
    have : u.1 (ψ t) = (W s).ι (π s t) := by
      rw [← Scheme.Hom.comp_apply, hψ1, Scheme.Hom.comp_apply]
    rw [this]
    exact ((π s) t).2
  let ψ' : T s ⟶ V := IsOpenImmersion.lift V.ι ψ hrange
  have hψ' : ψ' ≫ V.ι = ψ := IsOpenImmersion.lift_fac _ _ _
  have h1 : ψ' ≫ φ = 𝟙 _ := by
    obtain ⟨c, -, hc⟩ := hT s (T s) (y s) (π s) (hy s)
    have e1 : HPt.map (ψ' ≫ φ) (y s) = y s := by
      rw [HPt.map_comp, hφ, ← HPt.map_comp, hψ', hψ]
    have e2 : HPt.map (𝟙 (T s)) (y s) = y s := HPt.map_id _
    exact (hc _ e1).trans (hc _ e2).symm
  have h2 : φ ≫ ψ' = 𝟙 _ := by
    obtain ⟨c, -, hc⟩ := hu V (HPt.map V.ι u)
    have e1 : HPt.map ((φ ≫ ψ') ≫ V.ι) u = HPt.map V.ι u := by
      rw [Category.assoc, hψ', HPt.map_comp, hψ, hφ]
    have e2 := (hc _ e1).trans (hc _ rfl).symm
    rw [← cancel_mono V.ι, e2, Category.id_comp]
  have hiso : IsIso φ := ⟨⟨ψ', h2, h1⟩⟩
  have hcomp : φ ≫ π s = u.1 ∣_ W s := by
    rw [← cancel_mono (W s).ι, Category.assoc, ← hy s, ← hx1, ← hφ]
    rfl
  rw [← hcomp]
  haveI := hπ s
  infer_instance

end GlobalTheory.HilbGlue
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfRepresentsHilbertFunctorOfLocalStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue

theorem _root_.GlobalTheory.T.isProper_of_represents_hilbertFunctor_of_local : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (H : Scheme.{0}) (u : GlobalTheory.HilbGlue.HPt z r H), (∀ (T : Scheme.{0}) (x : GlobalTheory.HilbGlue.HPt z r T), ∃! c : T ⟶ H, GlobalTheory.HilbGlue.HPt.map c u = x) → (∀ s : S, ∃ W : S.Opens, s ∈ W ∧ ∃ (T : Scheme.{0}) (y : GlobalTheory.HilbGlue.HPt z r T) (π : T ⟶ W.toScheme), IsProper π ∧ y.1 = π ≫ W.ι ∧ ∀ (Y : Scheme.{0}) (x : GlobalTheory.HilbGlue.HPt z r Y) (b : Y ⟶ W.toScheme), x.1 = b ≫ W.ι → ∃! c : Y ⟶ T, GlobalTheory.HilbGlue.HPt.map c y = x) → IsProper u.1 := by
  first | (exact @GlobalTheory.HilbGlue.isProper_of_represents_of_local_proper) | (exact GlobalTheory.HilbGlue.isProper_of_represents_of_local_proper) | (intros; apply GlobalTheory.HilbGlue.isProper_of_represents_of_local_proper  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbertSchemeRepresentableOfOpenCover

section

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue Opposite

theorem GlobalTheory.HilbGlue.isSheaf_hilbFunctor {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) :
    Presieve.IsSheaf Scheme.zariskiTopology (hilbFunctor z r) := by
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro Y P hP
  obtain ⟨(𝒰 : Scheme.OpenCover Y), rfl⟩ := Scheme.exists_cover_of_mem_pretopology hP
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  exact existsUnique_of_exists_of_unique (GlobalTheory.T.hilbert_point_glue_open_cover z r Y 𝒰 x fun i j R b c h => hx i j R b c h)
    fun y y' h h' => GlobalTheory.T.hilbert_point_eq_of_open_cover z r Y 𝒰 y y' fun i => (h i).trans (h' i).symm

theorem GlobalTheory.HilbGlue.isHilbRep_of_cover : ∀ (S Z : Scheme.{0}) (z : Z ⟶ S), IsFinite z → Flat z →
    LocallyOfFinitePresentation z → ∀ r : ℕ, (∀ s : S, ∃ W : S.Opens, s ∈ W ∧ IsHilbRep (z ∣_ W) r) →
    IsHilbRep z r := by
  intro S Z z _ _ _ r hS
  have hloc : ∀ s : S, ∃ W : S.Opens, s ∈ W ∧ ∃ (T : Scheme.{0}) (y : HPt z r T) (π : T ⟶ W.toScheme),
      IsProper π ∧ y.1 = π ≫ W.ι ∧ ∀ (Y : Scheme.{0}) (x : HPt z r Y) (b : Y ⟶ W.toScheme),
        x.1 = b ≫ W.ι → ∃! c : Y ⟶ T, HPt.map c y = x := fun s => by
    obtain ⟨W, hs, hW⟩ := hS s
    exact ⟨W, hs, GlobalTheory.T.hilbertFunctor_local_representing_data_of_restrict z r W hW⟩
  have hloc' := hloc
  choose W hsW T y π _ hπ huniq using hloc
  have hrep : (hilbFunctor z r).IsRepresentable :=
    GlobalTheory.GenTorsor.isRepresentable_of_cover (hilbFunctor z r) (GlobalTheory.HilbGlue.isSheaf_hilbFunctor z r) (hilbProj z r) W
      (eq_top_iff.2 fun s _ => TopologicalSpace.Opens.mem_iSup.2 ⟨s, hsW s⟩) T y π hπ huniq
  obtain ⟨H, u, hu⟩ : ∃ (H : Scheme.{0}) (u : HPt z r H), ∀ (T : Scheme.{0}) (x : HPt z r T),
      ∃! c : T ⟶ H, HPt.map c u = x := by
    obtain ⟨H, ⟨e⟩⟩ := hrep.has_representation
    have h : ∀ {T : Scheme.{0}} (c : T ⟶ H), HPt.map c (e.homEquiv (𝟙 H)) = e.homEquiv c :=
      fun c => (e.homEquiv_eq c).symm
    exact ⟨H, e.homEquiv (𝟙 H), fun T x => ⟨e.homEquiv.symm x, (h _).trans (e.homEquiv.apply_symm_apply x),
      fun c hc => e.homEquiv.eq_symm_apply.2 ((h c).symm.trans hc)⟩⟩
  have hprop : IsProper u.1 := GlobalTheory.T.isProper_of_represents_hilbertFunctor_of_local z r H u hu hloc'
  obtain ⟨h, I⟩ := u
  refine ⟨H, h, I.1.subscheme, I.1.subschemeι, hprop, inferInstance, I.2.1, I.2.2.1, I.2.2.2, ?_⟩
  intro T g V v _ h1 h2 h3
  have hv' : IsFinFlatRk (v ≫ pullback.snd z g) r := ⟨h1, h2, h3⟩
  obtain ⟨c, hc, hcu⟩ := hu T (mkPt g v hv')
  have key : ∀ (f : T ⟶ H) (hf : f ≫ h = g), HPt.map f ⟨h, I⟩ = mkPt g v hv' ↔
      ∃ w : V ⟶ I.1.subscheme, IsPullback v w (bc z f h g hf) I.1.subschemeι := by
    intro f hf
    rw [mkPt, HPt.map_eq_mk_iff f ⟨h, I⟩ hf]
    exact GlobalTheory.HilbGlue.comap_eq_ker_iff (bc z f h g hf) I.1 v
  have hcg : c ≫ h = g := congrArg Sigma.fst hc
  exact ⟨c, ⟨hcg, (key c hcg).1 hc⟩, fun f ⟨hf, hw⟩ => hcu f ((key f hf).2 hw)⟩
end
end
