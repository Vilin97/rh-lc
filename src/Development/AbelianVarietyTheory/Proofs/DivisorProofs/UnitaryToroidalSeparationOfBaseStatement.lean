module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleTwistNormalisedBlowupNoetherianDomain
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedBlowupCyclotomicAwayProjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCartierOnNormalizedBlowup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
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
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreNormalProjectiveAmpleCharZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdlAlongComapEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefIntersectionNumberNonnegSubscheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparationNormalizedBlowupUnitaryCompactificatioStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryThetaSetupIdealOverComponentStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UValThruTopOfDisjoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealDescentToComponentCompactification
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleComponentsClopenPartition
import Mathlib.Tactic.Basify
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIntegralCompactificationExistsViaThetaStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormBl

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.NormBlowupField

theorem exists_normBl : ∀ (K : Type) [Field K] [CharZero K] (Z : Scheme.{0}) (z : Z ⟶ Sp K),
    IsProjOver z → GlobalTheory.IsNormalScheme Z → ∀ (J : Z.IdealSheafData) (W : Z.Opens),
    Dense (W : Set Z) → (∀ x ∈ J.support, x ∉ W) → ∃ (S : Scheme.{0}) (π : S ⟶ Z)
    (BD : EffCartierData S), GlobalTheory.Poinc.IsNormBl π J ∧ IsProjOver (π ≫ z) ∧ IsProper π ∧
    BD.idealSheaf = J.comap π ∧ IsIso (π ∣_ W) ∧ Dense (π ⁻¹' W : Set S) := by
  intro K _ _ Z z hz hZ J W hWd hWJ
  obtain ⟨X', b, hb, hbs, hiso⟩ := GlobalTheory.ProjBlowup.exists_blowup z hz J
  haveI : LocallyOfFiniteType (b ≫ z) := by
    obtain ⟨m, i, hi, e⟩ := hbs
    have := isProper_str K m
    rw [← e]; infer_instance
  haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (b ≫ z)
  let V : X'.Opens := b ⁻¹ᵁ W
  haveI hbW : IsIso (b ∣_ W) := hiso W fun x hx hJ => hWJ x hJ hx
  haveI hoi : IsOpenImmersion (V.ι ≫ b) := by
    rw [← morphismRestrict_ι]; infer_instance
  haveI hN : GlobalTheory.IsNormalScheme V.toScheme := .of_isOpenImmersion (V.ι ≫ b)
  haveI : IsReduced V.toScheme := by
    exact inferInstance
  haveI hfin : IsFinite V.ι.fromNormalization :=
    isFinite_fromNormalization_of_genericPoints (o := CommRingCat.of K) V.ι (b ≫ z)
      (fun x _ => charZero_of_injective_ringHom (f := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        (V.ι ≫ b ≫ z).appTop ≫ V.toScheme.presheaf.germ ⊤ x trivial ≫ V.toScheme.residue x).hom)
        (RingHom.injective _))
      fun x _ => (LocallyOfFiniteType.stalkMap V.ι x).residueFieldMap
  let ν := V.ι.fromNormalization
  have hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme V.ι.normalization := IsNormalScheme.pred _
  have hν : IsIso (ν ∣_ V) := by
    have H := isPullback_toNormalization_of_mono (𝟙 _) V.ι V.ι (Category.id_comp _).symm
    have e := IsPullback.isoIsPullback_hom_fst _ _ (isPullback_morphismRestrict V.ι.fromNormalization V) H.flip
    rw [← e]
    infer_instance
  have hd : Dense ((ν ⁻¹ᵁ V : V.ι.normalization.Opens) : Set V.ι.normalization) := by
    refine V.ι.toNormalization.denseRange.mono ?_
    rintro _ ⟨x, rfl⟩
    change V.ι.fromNormalization (V.ι.toNormalization x) ∈ V
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization]
    exact x.2
  have hVd : Dense (V : Set X') := GlobalTheory.NormBlowupInt.dense_preimage_of_blowup J b hb hiso W hWd
  obtain ⟨D, hD⟩ := EffCartierData.exists_idealSheaf_eq hb.1
  have hK : D.KeepsRegular ν := by
    refine D.keepsRegular_of_dense ν (fun y => (hS y).1) (hd.mono fun t ht => ?_)
    show ν t ∉ D.idealSheaf.support
    rw [hD, GlobalTheory.ProjBlowup.mem_support_comap]
    exact fun h => hWJ _ h ht
  have hproj : IsProjOver ((ν ≫ b) ≫ z) := by
    rw [Category.assoc]; exact isProjOver_comp_of_isFinite ν hbs
  have hprop : IsProper (ν ≫ b) := by
    haveI : IsProper z := by
      obtain ⟨m, i, hi, e⟩ := hz
      have := isProper_str K m
      rw [← e]; infer_instance
    haveI : IsProper ((ν ≫ b) ≫ z) := by
      obtain ⟨m, i, hi, e⟩ := hproj
      have := isProper_str K m
      rw [← e]; infer_instance
    exact IsProper.of_comp (ν ≫ b) z
  refine ⟨V.ι.normalization, ν ≫ b, D.pull ν hK,
    ⟨inferInstance, X', b, ν, V, hb, rfl, hfin, hVd, hd, hν⟩, hproj, hprop, ?_, ?_, ?_⟩
  · rw [EffCartierData.idealSheaf_pull, hD, Scheme.IdealSheafData.comap_comp]
  · rw [morphismRestrict_comp]; exact IsIso.comp_isIso' hν hbW
  · convert hd using 1
    ext t
    simp [V]

end GlobalTheory.NormBlowupField
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealDescentToComponentCompactificationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem _root_.GlobalTheory.T.ideal_descent_to_component_compactification : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (A : Set C.Z), IsClopen A → IsIrreducible A → (A ∩ Set.range C.i).Nonempty → ∀ (X₁ : USetup C) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι → Set.range X₁.π = A → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range C.i) → UValThru Xo c C.i X₁.π Set.univ φ J₁ ι → ∃ (d : ℕ) (J : C.Z.IdealSheafData), 1 ≤ d ∧ (∀ x ∈ J.support, x ∈ A ∧ x ∉ Set.range C.i) ∧ UValThru Xo c C.i (𝟙 C.Z) A φ J d := by
  first | exact @GlobalTheory.UPoincDown.idealDescent | exact GlobalTheory.UPoincDown.idealDescent | (intros; apply GlobalTheory.UPoincDown.idealDescent <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCompactificationExistsBoundaryIdeal

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc

theorem uIdealSt_holds : UIdealSt := by
  intro E _ _ _ H Dw hpq φ hφ l Xo c C
  haveI : IsNoetherianRing C.o := C.ded.toIsDedekindRing.toIsNoetherian
  haveI : AlgebraicGeometry.IsNoetherian C.Z := GlobalTheory.isNoetherian_of_isProjOver C.proj
  have hdom : ∀ x : C.Z, IsDomain (C.Z.presheaf.stalk x) := fun x => C.normal.isDomain_stalk x
  have hfin : (irreducibleComponents C.Z).Finite := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  letI : Fintype (irreducibleComponents C.Z) := hfin.fintype
  have hclo : ∀ k : irreducibleComponents C.Z, IsClopen (k : Set C.Z) := fun k =>
    ⟨isClosed_of_mem_irreducibleComponents _ k.2, GlobalTheory.CompPart.isOpen_of_mem hdom k.2⟩
  have key : ∀ k : irreducibleComponents C.Z, ∃ (d : ℕ) (J : C.Z.IdealSheafData), 1 ≤ d ∧
      (∀ x ∈ J.support, x ∈ (k : Set C.Z) ∧ x ∉ Set.range C.i) ∧ UValThru Xo c C.i (𝟙 C.Z) k φ J d := by
    intro k
    by_cases hk : ((k : Set C.Z) ∩ Set.range C.i).Nonempty
    · obtain ⟨X₁, ι, J₁, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_unitaryThetaSetup_ideal_over_component E H Dw hpq φ hφ l Xo c C k (hclo k) k.2.1 hk
      exact GlobalTheory.T.ideal_descent_to_component_compactification E H Dw hpq φ hφ l Xo c C k (hclo k) k.2.1 hk X₁ ι J₁ h1 h2 h3 h4
    · refine ⟨1, ⊤, le_rfl, fun x hx => ?_, uValThru_top_of_disjoint (hclo k).2 (Set.not_nonempty_iff_eq_empty.1 hk) φ 1⟩
      rw [Scheme.IdealSheafData.support_top] at hx
      exact absurd hx (by simp [← SetLike.mem_coe])
  choose d J hd hJ hv using key
  exact exists_uValOn_of_pieces (ι := irreducibleComponents C.Z) C.i φ (fun k => (k : Set C.Z)) J d (GlobalTheory.CompPart.existsUnique_mem hdom) hd hJ hv

end GlobalTheory.UPoinc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCompactificationExistsBoundaryIdealStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem _root_.GlobalTheory.T.unitaryCompactification_exists_boundary_ideal : UIdealSt := by
  first | exact @GlobalTheory.UPoinc.uIdealSt_holds | exact GlobalTheory.UPoinc.uIdealSt_holds | (intros; apply GlobalTheory.UPoinc.uIdealSt_holds <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIntegralCompactificationsExist

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc

theorem uMinSt_holds : UMinSt := GlobalTheory.T.unitary_integral_compactification_exists_via_theta

end GlobalTheory.UPoinc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIntegralCompactificationsExistStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem _root_.GlobalTheory.T.unitary_integral_compactifications_exist : UMinSt := by
  first | exact @GlobalTheory.UPoinc.uMinSt_holds | exact GlobalTheory.UPoinc.uMinSt_holds | (intros; apply GlobalTheory.UPoinc.uMinSt_holds <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryToroidalSeparationOfBase

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoincTop

theorem uPoinStX_sep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q →
    ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ →
    ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), ∃ (Z : Scheme.{0}) (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z)
      (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) (S : Scheme.{0}) (π : S ⟶ Z) (j : Xo.XF c ⟶ S)
      (BD : EffCartierData S), UPoinOnX Xo c φ zs i OZ N d J π j BD ∧ GlobalTheory.UChart.SepB Xo c φ j := by
  intro E _ _ _ H Dw hpq φ hφ hns l Xo c
  obtain ⟨C⟩ := GlobalTheory.T.unitary_integral_compactifications_exist E H Dw hpq l Xo c
  obtain ⟨d, J₀, hd, hJ₀, hval₀⟩ := GlobalTheory.T.unitaryCompactification_exists_boundary_ideal E H Dw hpq φ hφ l Xo c C
  haveI := C.ded
  haveI := C.iF_open
  have hgen := GlobalTheory.T.generic_fibre_normal_projective_ample_charZero C.o c.F C.b C.inj C.Z C.z C.OZ C.proj C.normal C.OZ_lb C.OZ_ample
  obtain ⟨hprojZ, hnormZ, hOZlb, hOZamp⟩ := hgen
  let Z := pullback C.z (spMap C.b)
  let fZ : Z ⟶ C.Z := pullback.fst C.z (spMap C.b)
  let J : Z.IdealSheafData := J₀.comap fZ
  let W : Z.Opens := C.iF.opensRange
  have hWset : (W : Set Z) = Set.range C.iF := by simp [W]
  have hJ : ∀ x ∈ J.support, x ∉ Set.range C.iF := by
    intro x hx hxr
    rw [Scheme.IdealSheafData.support_comap] at hx
    obtain ⟨y, rfl⟩ := hxr
    exact hJ₀ _ hx ⟨y, rfl⟩
  have hval : UValOn Xo c C.iF φ J d := by
    intro W' _ _ _ hW ϖ hϖ χ y hy t tK htK hK P be hbe hmono
    obtain ⟨n, hn, hid⟩ := hval₀ W' hW ϖ hϖ (χ ≫ fZ) y
      (by rw [UCompact.i, ← Category.assoc, hy, Category.assoc]) t tK htK hK P be hbe hmono
    exact ⟨n, hn, by rw [GlobalTheory.PullAlong.idlAlong_comap_eq]; exact hid⟩
  obtain ⟨S, π, BD, hbl, hpS, hprop, hBD, hiso, hdS⟩ :=
    GlobalTheory.NormBlowupField.exists_normBl c.F Z (pullback.snd C.z (spMap C.b)) hprojZ hnormZ J W (by rw [hWset]; exact C.iF_dense)
      (fun x hx hxW => hJ x hx (by have h : x ∈ (W : Set Z) := hxW; rwa [hWset] at h))
  haveI := hiso
  let A : Xo.XF c ⟶ (π ⁻¹ᵁ W).toScheme := C.iF.isoOpensRange.hom ≫ inv (π ∣_ W)
  let j : Xo.XF c ⟶ S := A ≫ (π ⁻¹ᵁ W).ι
  have hjπ : j ≫ π = C.iF := by
    simp only [j, A, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
    simp [W]
  have hrj : Set.range j = π ⁻¹' Set.range C.iF := by
    have hA : Function.Surjective A := A.surjective
    change Set.range ((π ⁻¹ᵁ W).ι ∘ A) = _
    rw [Set.range_comp, hA.range_eq, Set.image_univ, Scheme.Opens.range_ι, ← hWset]
    rfl
  have hjo : IsOpenImmersion j := inferInstance
  refine ⟨Z, pullback.snd C.z (spMap C.b), C.iF, C.OZ.pull fZ, C.N, d, J, S, π, j, BD, ⟨⟨hprojZ, hnormZ, C.iF_open,
    C.iF_dense, C.iF_over, hOZlb, hOZamp⟩, ⟨C.N_pos, ?_⟩, ?_, ⟨hd, hJ, hval⟩, ⟨hbl, hpS, hjo, ?_, hjπ, hrj.symm, hBD, ?_⟩, ?_⟩, ?_⟩
  · intro Y f hf hY
    have h := C.omega Y f hf hY
    exact LBIso.trans (pull_isLB hOZlb f) (pull_isLB C.OZ_lb _) (LB.isLB_linComb hY _ _)
      (LBIso.symm (GlobalTheory.FibreNef.lbIso_pull_comp C.OZ_lb fZ f)) h
  · intro R _ _ _ hR t hP y hy σ hσ
    obtain ⟨ξ₀, h₁, h₂⟩ := C.ext R hR t hP y hy (σ ≫ spMap C.b) (by rw [← Category.assoc, hσ, Category.assoc])
    refine ⟨pullback.lift ξ₀ σ (by rw [h₂]), ?_, pullback.lift_snd _ _ _⟩
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]; exact h₁
    · simp only [Category.assoc, pullback.lift_snd, C.iF_over]; exact hσ
  · rw [hrj, ← hWset]; exact hdS
  · intro W' _ _ _ hW ϖ hϖ χ y hy t tK htK hK P be hbe hmono
    obtain ⟨n, hn, hid⟩ := hval W' hW ϖ hϖ (χ ≫ π) y (by rw [← Category.assoc, ← hy, Category.assoc, hjπ])
      t tK htK hK P be hbe hmono
    exact ⟨n, hn, by rw [hBD, GlobalTheory.PullAlong.idlAlong_comap_eq]; exact hid⟩
  · obtain ⟨S₀, π₀, ν, U, hb, hνπ, hfin, -⟩ := hbl.2
    obtain ⟨T₀, hT⟩ := GlobalTheory.BlowAmpleNoeth.ample_twist_of_blowup c.F Z S₀ S (pullback.snd C.z (spMap C.b)) J π₀ ν BD hprojZ hb hfin
      (by rw [hνπ]; exact hBD) (C.OZ.pull fZ) hOZamp
    refine ⟨T₀, fun k hk => ?_⟩
    have h := hT k hk
    rwa [hνπ] at h
  · exact GlobalTheory.T.separation_normalizedBlowup_unitaryCompactification E H Dw hpq φ hφ hns l Xo c C d J₀ hd hJ₀ hval₀ S π j hbl hprop hjπ hjo hrj.symm

theorem uStB : GlobalTheory.UChart.UStB := uPoinStX_sep

end GlobalTheory.UPoincTop
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryToroidalSeparationOfBaseStatement

section

@[expose] public section

open GlobalTheory.UChart

theorem _root_.GlobalTheory.T.unitaryToroidalSeparation_of_base : UStB := by
  first | exact @GlobalTheory.UPoincTop.uStB | exact GlobalTheory.UPoincTop.uStB | (intros; apply GlobalTheory.UPoincTop.uStB <;> assumption)
end
end
