module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenImmersionBigCellBaseAffineCoords
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnected
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyQuasiFiniteBigCellToBaseProdAffineSpaceStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.TotallySplit

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenImmersionBigCellBaseAffineCoordsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical


theorem _root_.GlobalTheory.T.exists_open_immersion_big_cell_base_affine_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N), Nonempty W → ∃ V : (Spec (CommRingCat.of Γ(Y₀ TF.X Z, W))).Opens, Nonempty V ∧ IsOpenImmersion (V.ι ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N)))) := by
  first | exact @GlobalTheory.LogPole.CellBir.exists_isOpenImmersion | exact GlobalTheory.LogPole.CellBir.exists_isOpenImmersion | (intros; apply GlobalTheory.LogPole.CellBir.exists_isOpenImmersion <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionSpecOfQuasiFiniteOfNormal

section

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory

theorem eq_of_minimalPrimes_le_of_isDomain_localization {A : Type} [CommRing A]
    (hA : ∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P))
    {P p q : Ideal A} [P.IsPrime] (hp : p ∈ minimalPrimes A) (hq : q ∈ minimalPrimes A)
    (hpP : p ≤ P) (hqP : q ≤ P) : p = q := by
  haveI := hA P
  let K := RingHom.ker (algebraMap A (Localization.AtPrime P))
  have hK : K.IsPrime := RingHom.ker_isPrime _
  have hle : ∀ Q : Ideal A, Q.IsPrime → Q ≤ P → K ≤ Q := by
    intro Q hQ hQP
    have h := IsLocalization.under_map_of_isPrime_disjoint P.primeCompl (Localization.AtPrime P) hQ
      (Set.disjoint_left.2 fun x hx hxQ ↦ hx (hQP hxQ))
    rw [← h]
    intro x hx
    rw [RingHom.mem_ker] at hx
    simp [Ideal.mem_comap, hx]
  have h1 : K = p := le_antisymm (hle p hp.1.1 hpP) (hp.2 ⟨hK, bot_le⟩ (hle p hp.1.1 hpP))
  have h2 : K = q := le_antisymm (hle q hq.1.1 hqP) (hq.2 ⟨hK, bot_le⟩ (hle q hq.1.1 hqP))
  exact h1.symm.trans h2

theorem isOpen_zeroLocus_of_mem_minimalPrimes {A : Type} [CommRing A] [IsNoetherianRing A]
    (hA : ∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P))
    {p : Ideal A} (hp : p ∈ minimalPrimes A) : IsOpen (PrimeSpectrum.zeroLocus (p : Set A)) := by
  have hfin := (minimalPrimes.finite_of_isNoetherianRing A).subset (Set.diff_subset (t := {p}))
  have heq : (PrimeSpectrum.zeroLocus (p : Set A))ᶜ =
      ⋃ q ∈ minimalPrimes A \ {p}, PrimeSpectrum.zeroLocus (q : Set A) := by
    ext x
    simp only [Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe,
      Set.mem_iUnion, Set.mem_diff, Set.mem_singleton_iff, exists_prop]
    constructor
    · intro hx
      obtain ⟨q, hq, hqx⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := x.asIdeal) bot_le
      refine ⟨q, ⟨hq, ?_⟩, hqx⟩
      rintro rfl
      exact hx hqx
    · rintro ⟨q, ⟨hq, hne⟩, hqx⟩ hpx
      exact hne (eq_of_minimalPrimes_le_of_isDomain_localization hA hq hp hqx hpx)
  rw [← isClosed_compl_iff, heq]
  exact hfin.isClosed_biUnion fun q _ ↦ PrimeSpectrum.isClosed_zeroLocus _

end GlobalTheory

namespace GlobalTheory

theorem isOpenImmersion_spec_of_quasiFinite_of_normal {A B : Type} [CommRing A] [CommRing B]
    [IsDomain B] [IsNoetherianRing A] (φ : A →+* B)
    (hA : ∀ (𝔭 : Ideal A) [𝔭.IsPrime],
      IsDomain (Localization.AtPrime 𝔭) ∧ IsIntegrallyClosed (Localization.AtPrime 𝔭))
    (hφ : φ.FiniteType) (hqf : LocallyQuasiFinite (Spec.map (CommRingCat.ofHom φ)))
    (hV : ∃ V : (Spec (CommRingCat.of B)).Opens, Nonempty V ∧
      IsOpenImmersion (V.ι ≫ Spec.map (CommRingCat.ofHom φ))) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) := by
  obtain ⟨V, hVne, hVo⟩ := hV
  set f := Spec.map (CommRingCat.ofHom φ) with hf
  have hAd : ∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P) :=
    fun P _ ↦ (hA P).1
  have hft : LocallyOfFiniteType f :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr hφ
  let η := genericPoint (Spec (CommRingCat.of B))
  have hηV : η ∈ V :=
    ((genericPoint_spec _).mem_open_set_iff V.isOpen).mpr (by simpa using hVne)
  let y₀ : PrimeSpectrum A := f η
  have hsp : ∀ x, y₀ ⤳ f x := fun x ↦ (genericPoint_specializes x).map f.continuous

  have hW : IsOpen (Set.range (V.ι ≫ f)) := (V.ι ≫ f).isOpenEmbedding.isOpen_range
  have hy₀W : y₀ ∈ Set.range (V.ι ≫ f) := ⟨⟨η, hηV⟩, rfl⟩
  have hmin : y₀.asIdeal ∈ minimalPrimes A := by
    refine ⟨⟨y₀.isPrime, bot_le⟩, fun q hq hle ↦ ?_⟩
    let z : PrimeSpectrum A := ⟨q, hq.1⟩
    have hz : z ⤳ y₀ := (PrimeSpectrum.le_iff_specializes z y₀).1 hle
    obtain ⟨v, hv⟩ := hz.mem_open hW hy₀W
    have h2 : y₀ ≤ z := by
      rw [← hv, Scheme.Hom.comp_apply]
      exact (PrimeSpectrum.le_iff_specializes _ _).2 (hsp _)
    exact h2

  have hZo : IsOpen (closure ({y₀} : Set (PrimeSpectrum A))) := by
    rw [PrimeSpectrum.closure_singleton]
    exact isOpen_zeroLocus_of_mem_minimalPrimes hAd hmin
  let Z : (Spec (CommRingCat.of A)).Opens := ⟨closure ({y₀} : Set (PrimeSpectrum A)), hZo⟩
  have hrange : Set.range f ⊆ Set.range Z.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact specializes_iff_mem_closure.1 (hsp x)
  let g : Spec (CommRingCat.of B) ⟶ Z.toScheme := IsOpenImmersion.lift Z.ι f hrange
  have hgf : g ≫ Z.ι = f := IsOpenImmersion.lift_fac _ _ _

  haveI : _root_.IsReduced A := isReduced_ofLocalizationMaximal A fun P _ ↦ by
    haveI := hAd P; infer_instance
  haveI : Nonempty Z.toScheme := ⟨⟨y₀, subset_closure rfl⟩⟩
  haveI : IrreducibleSpace Z.toScheme :=
    Subtype.irreducibleSpace (isIrreducible_singleton (x := y₀)).closure
  haveI : IsIntegral Z.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have hZ : ∀ z : Z.toScheme, IsIntegrallyClosed (Z.toScheme.presheaf.stalk z) := by
    intro z
    have e₁ := asIso (Z.ι.stalkMap z)
    let x : PrimeSpectrum A := Z.ι z
    have hloc : IsLocalization.AtPrime ((Spec.structureSheaf A).presheaf.stalk x) x.asIdeal :=
      StructureSheaf.IsLocalization.to_stalk A x
    have e₂ := IsLocalization.algEquiv x.asIdeal.primeCompl
      ((Spec.structureSheaf A).presheaf.stalk x) (Localization.AtPrime x.asIdeal)
    haveI := (hA x.asIdeal).2
    have hic : IsIntegrallyClosed ((Spec.structureSheaf A).presheaf.stalk x) :=
      IsIntegrallyClosed.of_equiv e₂.symm.toRingEquiv
    haveI : IsIntegrallyClosed ((Spec (CommRingCat.of A)).presheaf.stalk (Z.ι z)) := hic
    exact IsIntegrallyClosed.of_equiv (e₁.commRingCatIsoToRingEquiv)

  haveI : IsSeparated g := IsSeparated.of_comp g Z.ι
  haveI : QuasiCompact g := QuasiCompact.of_comp g Z.ι
  haveI : LocallyOfFiniteType (g ≫ Z.ι) := by rw [hgf]; exact hft
  haveI : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g Z.ι
  haveI : LocallyQuasiFinite (g ≫ Z.ι) := by rw [hgf]; exact hqf
  haveI : LocallyQuasiFinite g := LocallyQuasiFinite.of_comp g Z.ι
  haveI : IsOpenImmersion ((V.ι ≫ g) ≫ Z.ι) := by rw [Category.assoc, hgf]; exact hVo
  haveI : IsOpenImmersion (V.ι ≫ g) := IsOpenImmersion.of_comp _ Z.ι
  have := isOpenImmersion_of_quasiFinite_of_isOpenImmersion_restrict g hZ V hVne
  rw [← hgf]
  infer_instance

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionSpecOfQuasiFiniteOfNormalStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry

theorem _root_.GlobalTheory.T.isOpenImmersion_specMap_of_quasiFinite_of_normal : ∀ {A B : Type} [CommRing A] [CommRing B] [IsDomain B] [IsNoetherianRing A] (φ : A →+* B), (∀ (𝔭 : Ideal A) [𝔭.IsPrime], IsDomain (Localization.AtPrime 𝔭) ∧ IsIntegrallyClosed (Localization.AtPrime 𝔭)) → φ.FiniteType → LocallyQuasiFinite (Spec.map (CommRingCat.ofHom φ)) → (∃ V : (Spec (CommRingCat.of B)).Opens, Nonempty V ∧ IsOpenImmersion (V.ι ≫ Spec.map (CommRingCat.ofHom φ))) → IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) := by
  first | exact @GlobalTheory.isOpenImmersion_spec_of_quasiFinite_of_normal | exact GlobalTheory.isOpenImmersion_spec_of_quasiFinite_of_normal | (intros; apply GlobalTheory.isOpenImmersion_spec_of_quasiFinite_of_normal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleBigCellCoordinatesFlagSpace

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CellEtale

theorem etale_of_isOpenImmersion_spec {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B)
    (h : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))) : φ.Etale := by
  have : Etale (Spec.map (CommRingCat.ofHom φ)) := inferInstance
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).1 this

theorem etale_of_subsingleton {A B : Type} [CommRing A] [CommRing B] [Subsingleton B] (φ : A →+* B) :
    φ.Etale := by
  letI := φ.toAlgebra
  have : IsLocalization.Away (0 : A) B := by
    refine ⟨fun ⟨y, _⟩ => isUnit_of_subsingleton _, fun z => ⟨⟨0, 1⟩, Subsingleton.elim _ _⟩,
      fun {x y} _ => ⟨⟨0, 1, pow_one 0⟩, by simp⟩⟩
  have : Algebra.Etale A B := Algebra.Etale.of_isLocalizationAway (0 : A)
  exact RingHom.etale_algebraMap.2 this

theorem normal_mvPolynomial : ∀ (X : Scheme.{0}) (K : Type) [Field K] (s : X ⟶ Spec (CommRingCat.of K)) [Smooth s] (U : X.affineOpens) (ι : Type) [Finite ι], IsNoetherianRing (MvPolynomial ι Γ(X, U.1)) ∧ ∀ (𝔭 : Ideal (MvPolynomial ι Γ(X, U.1))) [𝔭.IsPrime], IsDomain (Localization.AtPrime 𝔭) ∧ IsIntegrallyClosed (Localization.AtPrime 𝔭) := by
  intro X K _ s _ U ι _
  have h1 := HasRingHomProperty.appLE (P := @Smooth) s inferInstance ⟨⊤, isAffineOpen_top _⟩ U (by simp)
  let g : K →+* Γ(X, U.1) := (s.appLE ⊤ U.1 (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have hg : g.Smooth := by
    refine RingHom.Smooth.comp ?_ h1
    exact RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso _)
  let G : K →+* MvPolynomial ι Γ(X, U.1) := MvPolynomial.C.comp g
  have hC : (MvPolynomial.C : Γ(X, U.1) →+* MvPolynomial ι Γ(X, U.1)).Smooth :=
    RingHom.smooth_algebraMap.2 { formallySmooth := inferInstance, finitePresentation := Algebra.FinitePresentation.mvPolynomial Γ(X, U.1) Γ(X, U.1) ι }
  have hG : G.Smooth := RingHom.Smooth.comp hg hC
  algebraize [G]
  refine ⟨?_, fun 𝔭 _ => GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_smooth K 𝔭 _⟩
  have : Algebra.FiniteType K (MvPolynomial ι Γ(X, U.1)) := inferInstance
  exact Algebra.FiniteType.isNoetherianRing K _

theorem isDomain_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (W : (Y₀ TF.X Z).Opens), IsAffineOpen W → Nonempty W → IsDomain Γ(Y₀ TF.X Z, W) := by
  intro E _ _ _ H Dw l Xo c TF Z hF W hW hne
  obtain ⟨hs, hp, hc⟩ := GlobalTheory.VarFlag.isVariety₀_flag E H Dw l Xo c TF Z hF
  have : Smooth (str₀ TF.X Z) := SmoothOfRelativeDimension.smooth (GlobalTheory.FlagTan.dimFlag Dw) _
  have : GeometricallyIntegral (str₀ TF.X Z) := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _
  have hY : IsIntegral (Y₀ TF.X Z) := GeometricallyIntegral.geometrically_isIntegral (f := str₀ TF.X Z) (K := c.F)
    (𝟙 _) (𝟙 _) (str₀ TF.X Z) IsPullback.of_id_fst
  infer_instance

theorem finiteType_cell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N), (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N)).FiniteType := by
  intro E _ _ _ H Dw l Xo c TF Z hF U n e v hv W k L N h
  have hπ : LocallyOfFiniteType (toBase TF Z) := by
    have : IsProper TF.X.π := TF.X.proper
    infer_instance
  have h1 := HasRingHomProperty.appLE (P := @LocallyOfFiniteType) (toBase TF Z) hπ U ⟨W, h.1⟩ h.2.1
  refine RingHom.FiniteType.of_comp_finiteType
    (f := (MvPolynomial.C : Γ(TF.Y.X, U.1) →+* MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1))) ?_
  rw [MvPolynomial.eval₂Hom_comp_C]
  exact h1

theorem etale_cellCoord : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N), (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N)).Etale := by
  intro E _ _ _ H Dw l Xo c TF Z hF U n e v hv W k L N h
  by_cases hW : Nonempty W
  · haveI := isDomain_sections E H Dw l Xo c TF Z hF W h.1 hW
    haveI := TF.smooth
    have : Smooth TF.Y.s := SmoothOfRelativeDimension.smooth (n := Dw.dim) TF.Y.s
    obtain ⟨hN, hA⟩ := normal_mvPolynomial TF.Y.X c.F TF.Y.s U (VIx Dw)
    exact etale_of_isOpenImmersion_spec _ (GlobalTheory.T.isOpenImmersion_specMap_of_quasiFinite_of_normal _ hA
      (finiteType_cell E H Dw l Xo c TF Z hF U n e v hv W k L N h)
      (GlobalTheory.T.locallyQuasiFinite_bigCell_to_base_prod_affineSpace E H Dw l Xo c TF Z hF U n e v hv W k L N h)
      (GlobalTheory.T.exists_open_immersion_big_cell_base_affine_coords E H Dw l Xo c TF Z hF U n e v hv W k L N h hW))
  · haveI : Subsingleton Γ(Y₀ TF.X Z, W) := by
      have hE : IsEmpty W := not_nonempty_iff.1 hW
      have : IsEmpty (Spec Γ(Y₀ TF.X Z, W)) := (Scheme.Hom.homeomorph h.1.isoSpec.hom).isEmpty_congr.1 hE
      by_contra hs
      rw [not_subsingleton_iff_nontrivial] at hs
      obtain ⟨m, hm⟩ := Ideal.exists_maximal Γ(Y₀ TF.X Z, W)
      exact this.elim ⟨m, hm.isPrime⟩
    exact etale_of_subsingleton _

end GlobalTheory.CellEtale
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleBigCellCoordinatesFlagSpaceStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem _root_.GlobalTheory.T.etale_bigCellCoordinates_flagSpace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N), (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N)).Etale := by
  first | exact @GlobalTheory.CellEtale.etale_cellCoord | exact GlobalTheory.CellEtale.etale_cellCoord | (intros; apply GlobalTheory.CellEtale.etale_cellCoord <;> assumption)
end
end
