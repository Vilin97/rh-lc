module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPureBCId
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMulEquivPointsOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoBaseChangesOfCongruentMapsPureHodgeStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FormallyUnramifiedMulInvertibleInteger
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPureBCId
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAlgebraMapEqOfValVLeOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexEmbeddingFractionFieldCdvr
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointEqOfResidueEqInvertibleOrder

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj

namespace GlobalTheory.TorsionReduction

theorem eq_of_residue_eq : ∀ (S : Type) [CommRing S] (P : Out.PolAV (Sp S)) (T : Type) [CommRing T] [IsLocalRing T] (b : S →+* T) (n : ℕ), IsUnit (n : T) → ∀ x y : Over.mk (spMap b) ⟶ P.A, x ^ n = 1 → y ^ n = 1 → spMap (IsLocalRing.residue T) ≫ x.left = spMap (IsLocalRing.residue T) ≫ y.left → x = y := by
  intro S _ P T _ _ b n hn x y hx hy hr
  letI := P.isAb.comm
  haveI : Smooth P.A.hom := P.isAb.smooth
  let j : Sp T ⟶ Sp S := spMap b
  let G : Over (Sp T) := (Over.pullback j).obj P.A
  have hn' : IsUnit (n : Γ(Sp T, ⊤)) := by
    simpa using hn.map (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom
  let m : G.left ⟶ G.left := (Out.mulA G n).left
  have hw : m ≫ G.hom = G.hom := Over.w _
  have h₁ : FormallyUnramified m := formallyUnramified_mulA (Sp T) G n hn'
  have h₂ : LocallyOfFiniteType (m ≫ G.hom) := by
    rw [hw]; dsimp [G]; infer_instance
  have h₃ : LocallyOfFiniteType m := locallyOfFiniteType_of_comp _ G.hom
  have e : (Over.pullback j).map (Out.mulA P.A n) = Out.mulA G n :=
    (map_pow (Over.pullback j).homMonoidHom (𝟙 P.A) n).trans
      (congrArg (· ^ n) (CategoryTheory.Functor.map_id (Over.pullback j) P.A))
  have mf : m ≫ pullback.fst P.A.hom j = pullback.fst P.A.hom j ≫ (Out.mulA P.A n).left := by
    change (Out.mulA G n).left ≫ _ = _
    rw [← e]; exact pullback.lift_fst _ _ _
  have kx : ∀ z : Over.mk (spMap b) ⟶ P.A, z ^ n = 1 → z.left ≫ (Out.mulA P.A n).left = j ≫ (η[P.A]).left := by
    intro z hz
    rw [← Over.comp_left, Out.mulA, MonObj.comp_pow, Category.comp_id, hz, Hom.one_def]
    simp [j]
  let x' : Sp T ⟶ G.left := pullback.lift x.left (𝟙 _) (by simpa [j] using Over.w x)
  let y' : Sp T ⟶ G.left := pullback.lift y.left (𝟙 _) (by simpa [j] using Over.w y)
  have x₁ : x' ≫ pullback.fst P.A.hom j = x.left := pullback.lift_fst _ _ _
  have y₁ : y' ≫ pullback.fst P.A.hom j = y.left := pullback.lift_fst _ _ _
  have x₂ : x' ≫ pullback.snd P.A.hom j = 𝟙 _ := pullback.lift_snd _ _ _
  have y₂ : y' ≫ pullback.snd P.A.hom j = 𝟙 _ := pullback.lift_snd _ _ _
  have hab : x' ≫ m = y' ≫ m := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, mf, pullback.lift_fst_assoc, pullback.lift_fst_assoc, kx x hx, kx y hy]
    · rw [Category.assoc, Category.assoc]
      change x' ≫ m ≫ G.hom = y' ≫ m ≫ G.hom
      rw [hw]
      exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
  have hc : spMap (IsLocalRing.residue T) ≫ x' = spMap (IsLocalRing.residue T) ≫ y' := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) x₁).trans
        (hr.trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) y₁)).symm))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (x₂.trans y₂.symm)).trans (Category.assoc _ _ _).symm)
  have hopen := isOpenImmersion_equalizer_ι_of_unramified m hab
  have hsub := range_subset_range_equalizer_ι _ hc
  have hcl : IsLocalRing.closedPoint T ∈ Set.range (equalizer.ι x' y') :=
    hsub ⟨IsLocalRing.closedPoint _, IsLocalRing.comap_closedPoint (IsLocalRing.residue T)⟩
  have hall : Set.range (equalizer.ι x' y') = Set.univ :=
    Set.eq_univ_of_forall fun p =>
      (IsLocalRing.specializes_closedPoint p).mem_open (equalizer.ι x' y').isOpenEmbedding.isOpen_range hcl
  have hxy : x' = y' := eq_of_range_equalizer_ι_eq_univ m hab hall
  apply Over.OverMorphism.ext
  exact x₁.symm.trans ((congrArg (· ≫ pullback.fst P.A.hom j) hxy).trans y₁)

end GlobalTheory.TorsionReduction
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointEqOfResidueEqInvertibleOrderStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.torsion_point_eq_of_residue_eq_invertible_order : ∀ (S : Type) [CommRing S] (P : Out.PolAV (Sp S)) (T : Type) [CommRing T] [IsLocalRing T] (b : S →+* T) (n : ℕ), IsUnit (n : T) → ∀ x y : Over.mk (spMap b) ⟶ P.A, x ^ n = 1 → y ^ n = 1 → spMap (IsLocalRing.residue T) ≫ x.left = spMap (IsLocalRing.residue T) ≫ y.left → x = y := by
  first | exact @GlobalTheory.TorsionReduction.eq_of_residue_eq | exact GlobalTheory.TorsionReduction.eq_of_residue_eq | (intros; apply GlobalTheory.TorsionReduction.eq_of_residue_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaFixesComplexFibrePureEndomorphismTorsion

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj

namespace GlobalTheory.InertiaTransfer

theorem spMap_comp_of {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {f : A →+* B} {g : B →+* C}
    {h : A →+* C} (e : g.comp f = h) : spMap g ≫ spMap f = spMap h := by
  subst e
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem exists_completion (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (𝔮 : Ideal (𝓞 K)) (h𝔮 : 𝔮.IsMaximal) :
    ∃ (T : Formalism.L2.Pj.CDVR) (a : 𝓞 K →+* T.V) (j : T.V →+* ℂ), j.comp a = σ.comp (algebraMap (𝓞 K) K) ∧
      ∀ x, a x ∈ IsLocalRing.maximalIdeal T.V ↔ x ∈ 𝔮 := by
  let la : IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
    ⟨𝔮, h𝔮.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField h𝔮 (RingOfIntegers.not_isField K)⟩
  obtain ⟨T, io, ho, hfin, -⟩ := GlobalTheory.PlaceCompletion.exists_initial_completion K la
  obtain ⟨em, hem⟩ := GlobalTheory.ComplexEmbedding.exists_embedding_fractionField K σ T hfin io
  have hv : ∀ x : K, Formalism.L2.Pj.valV T.V (io x) = la.valuation K x := fun x => by
    rw [GlobalTheory.PlaceCompletion.valV_eq_pow_of_overLa ho, pow_one]
  have hex : ∀ x : 𝓞 K, ∃ v : T.V, algebraMap T.V T.Fr v = io (algebraMap (𝓞 K) K x) := fun x =>
    GlobalTheory.PlaceCompletion.exists_algebraMap_eq_of_valV_le_one (by
      rw [hv]; exact la.valuation_le_one x)
  choose f hf using hex
  have hinj := IsFractionRing.injective T.V T.Fr
  refine ⟨T, { toFun := f
               map_one' := hinj (by rw [hf, map_one, map_one, map_one])
               map_mul' := fun x y => hinj (by rw [map_mul, hf, hf, hf, map_mul, map_mul])
               map_zero' := hinj (by rw [hf, map_zero, map_zero, map_zero])
               map_add' := fun x y => hinj (by rw [map_add (f := _), hf, hf, hf, map_add (f := _), map_add (f := _)]) },
    em.comp (algebraMap T.V T.Fr), RingHom.ext fun x => ?_, fun x => ?_⟩
  · change em (algebraMap T.V T.Fr (f x)) = σ (algebraMap (𝓞 K) K x)
    rw [hf, ← hem]; rfl
  · change f x ∈ _ ↔ _
    rw [← GlobalTheory.PlaceCompletion.valV_algebraMap_lt_one_iff (K' := T.Fr), hf, hv]
    exact la.valuation_lt_one_iff_mem x

theorem pow_eq_one_iff {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (y : Over.mk (𝟙 S') ⟶ G') (z : Over.mk f ⟶ G)
    (e : z.left = y.left ≫ φ) (n : ℕ) : y ^ n = 1 ↔ z ^ n = 1 := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.LamF.exists_mulEquiv_points_of_isGrpPullback S S' f G G' φ h (Over.mk (𝟙 S'))
  have key : ∀ {g : S' ⟶ S} (_ : g = f) (w : Over.mk g ⟶ G), w.left = z.left → (w ^ n = 1 ↔ z ^ n = 1) := by
    intro g hg w hw
    subst hg
    rw [Over.OverMorphism.ext hw]
  rw [← key (Category.id_comp f) (Φ y) ((hΦ y).trans e.symm), ← map_pow, MulEquiv.map_eq_one_iff]

noncomputable def restrict {S S' : Scheme.{0}} (f : S' ⟶ S) {G : Over S} (y : Over.mk (𝟙 S) ⟶ G) : Over.mk f ⟶ G :=
  (Over.homMk f (Category.comp_id f) : Over.mk f ⟶ Over.mk (𝟙 S)) ≫ y

theorem restrict_pow {S S' : Scheme.{0}} (f : S' ⟶ S) {G : Over S} [GrpObj G] {y : Over.mk (𝟙 S) ⟶ G} {n : ℕ}
    (hy : y ^ n = 1) : restrict f y ^ n = 1 := by
  rw [restrict, ← MonObj.comp_pow, hy, MonObj.comp_one]

theorem exists_isGrpPullback_of_inertia : GlobalTheory.Published.FormalAlgebraisation → GlobalTheory.Published.GrothendieckMessing → ∀ (N : IntermediateField ℚ ℂ) [NumberField N] (P : Out.PolAV (Sp (𝓞 N))) (W : P.A ⟶ P.A) [IsMonHom W] (r s : 𝓞 N), IsPureBC P.A W r s → ∀ q : ℕ, q.Prime → ∀ 𝔮 : Ideal (𝓞 N), 𝔮.IsMaximal → (q : 𝓞 N) ∈ 𝔮 → r - s ∉ 𝔮 → ∀ τ : ℂ ≃+* ℂ, (∀ x : 𝓞 N, ∃ y : 𝓞 N, ((y : N) : ℂ) = τ ((x : N) : ℂ) ∧ y - x ∈ 𝔮) → ∀ (A : Over (Sp ℂ)) [GrpObj A] (ψ : A.left ⟶ P.A.left), IsGrpPullback A P.A (spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N))) ψ → ∃ io : A.left ⟶ A.left, IsGrpPullback A A (spMap (τ : ℂ →+* ℂ)) io ∧ ∀ n : ℕ, ¬ q ∣ n → ∀ y : Over.mk (𝟙 (Sp (𝓞 N))) ⟶ P.A, y ^ n = 1 → ∀ x : Sp ℂ ⟶ A.left, x ≫ A.hom = 𝟙 _ → x ≫ ψ = spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) ≫ y.left → x ≫ io = spMap (τ : ℂ →+* ℂ) ≫ x := by
  intro hFA hGM N _ P W _ r s hW q hq 𝔮 h𝔮 hq𝔮 hrs τ hτ A _ ψ hψ
  set i : 𝓞 N →+* ℂ := (algebraMap N ℂ).comp (algebraMap (𝓞 N) N) with hi
  have hinj : Function.Injective i := (algebraMap N ℂ).injective.comp (IsFractionRing.injective (𝓞 N) N)
  choose σ₀ hσ₀ hσ₁ using hτ
  have hσ : ∀ x, i (σ₀ x) = τ (i x) := hσ₀
  let σ : 𝓞 N →+* 𝓞 N :=
    { toFun := σ₀
      map_one' := hinj (by rw [hσ, map_one, map_one])
      map_mul' := fun x y => hinj (by rw [map_mul, hσ, hσ, hσ, map_mul, map_mul])
      map_zero' := hinj (by rw [hσ, map_zero, map_zero])
      map_add' := fun x y => hinj (by rw [map_add (f := _), hσ, hσ, hσ, map_add (f := _), map_add (f := _)]) }
  obtain ⟨T, a, j, hj, ha⟩ := exists_completion N (algebraMap N ℂ) 𝔮 h𝔮
  let b : 𝓞 N →+* T.V := a.comp σ
  have hab : ∀ x, a x - b x ∈ IsLocalRing.maximalIdeal T.V := fun x => by
    have := (ha _).2 (𝔮.neg_mem (hσ₁ x))
    rwa [neg_sub, map_sub] at this
  have hqT : (q : T.V) ∈ IsLocalRing.maximalIdeal T.V := by
    have := (ha _).2 hq𝔮
    rwa [map_natCast] at this
  have hu : IsUnit (a (r - s)) := by
    by_contra h
    exact hrs ((ha _).1 h)
  obtain ⟨B, _, φ, hφ⟩ : ∃ (B : Over (Sp T.V)) (_ : GrpObj B) (φ : B.left ⟶ P.A.left),
      IsGrpPullback B P.A (spMap a) φ := ⟨_, inferInstance, _, isGrpPullback_pullback P.A (spMap a)⟩
  obtain ⟨φ', hφ', hred⟩ := GlobalTheory.T.exists_iso_baseChanges_of_congruent_maps_pureHodge hFA hGM (𝓞 N) P.A P.g P.isAb P.smoothDim W r s hW T.V T.cpl q hq hqT a b
    hab hu B φ hφ
  have ea : spMap j ≫ spMap a = spMap i := spMap_comp_of hj
  have eb : spMap j ≫ spMap b = spMap (τ : ℂ →+* ℂ) ≫ spMap i :=
    (spMap_comp_of (RingHom.ext fun x => (RingHom.congr_fun hj (σ x)).trans (hσ x))).trans
      (spMap_comp_of (f := i) (g := (τ : ℂ →+* ℂ)) rfl).symm
  have er : spMap (IsLocalRing.residue T.V) ≫ spMap a = spMap (IsLocalRing.residue T.V) ≫ spMap b :=
    (spMap_comp_of (RingHom.ext fun x => Ideal.Quotient.eq.2 (hab x))).trans
      (spMap_comp_of (f := b) (g := IsLocalRing.residue T.V) rfl).symm
  have w₁ : ψ ≫ P.A.hom = (A.hom ≫ spMap j) ≫ spMap a := by rw [Category.assoc, ea, hψ.1.w]
  obtain ⟨χ, hχ₁, hχ₂⟩ : ∃ χ : A.left ⟶ B.left, χ ≫ φ = ψ ∧ χ ≫ B.hom = A.hom ≫ spMap j :=
    ⟨hφ.1.lift _ _ w₁, hφ.1.lift_fst _ _ _, hφ.1.lift_snd _ _ _⟩
  have hχ : IsGrpPullback A B (spMap j) χ := hφ.cancel (hψ.congr ea.symm hχ₁.symm) hχ₂
  have hc := (hχ.comp hφ').congr eb rfl
  have w₂ : (χ ≫ φ') ≫ P.A.hom = (A.hom ≫ spMap (τ : ℂ →+* ℂ)) ≫ spMap i := by rw [hc.1.w, Category.assoc]
  obtain ⟨io, hio₁, hio₂⟩ : ∃ io : A.left ⟶ A.left, io ≫ ψ = χ ≫ φ' ∧ io ≫ A.hom = A.hom ≫ spMap (τ : ℂ →+* ℂ) :=
    ⟨hψ.1.lift _ _ w₂, hψ.1.lift_fst _ _ _, hψ.1.lift_snd _ _ _⟩
  refine ⟨io, hψ.cancel (hc.congr rfl hio₁.symm) hio₂, fun n hn y hy x hx₁ hx₂ => ?_⟩
  have hnu : IsUnit (n : T.V) := by
    by_contra h
    have h' : (n : T.V) ∈ IsLocalRing.maximalIdeal T.V := h
    have hc : IsCoprime (q : T.V) (n : T.V) := by
      simpa using (Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hq).2 hn)).map (Int.castRingHom T.V)
    obtain ⟨u, v, huv⟩ := hc
    exact (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top ((Ideal.eq_top_iff_one _).2
      (huv ▸ add_mem (Ideal.mul_mem_left _ u hqT) (Ideal.mul_mem_left _ v h')))
  have hyw : y.left ≫ P.A.hom = 𝟙 (Sp (𝓞 N)) := Over.w y
  have w₃ : (spMap a ≫ y.left) ≫ P.A.hom = 𝟙 (Sp T.V) ≫ spMap a := by
    rw [Category.assoc, hyw, Category.comp_id, Category.id_comp]
  obtain ⟨t, ht₁, ht₂⟩ : ∃ t : Sp T.V ⟶ B.left, t ≫ φ = spMap a ≫ y.left ∧ t ≫ B.hom = 𝟙 _ :=
    ⟨hφ.1.lift _ _ w₃, hφ.1.lift_fst _ _ _, hφ.1.lift_snd _ _ _⟩
  let yT : Over.mk (𝟙 (Sp T.V)) ⟶ B := Over.homMk t ht₂
  have hyT : yT ^ n = 1 := (pow_eq_one_iff hφ yT (restrict (spMap a) y) ht₁.symm n).2 (restrict_pow _ hy)
  let z : Over.mk (spMap b) ⟶ P.A := Over.homMk (t ≫ φ') (by
    change (t ≫ φ') ≫ P.A.hom = spMap b
    rw [Category.assoc, hφ'.1.w, reassoc_of% ht₂])
  have hz : z ^ n = 1 := (pow_eq_one_iff hφ' yT z rfl n).1 hyT
  have hzy : z = restrict (spMap b) y := GlobalTheory.T.torsion_point_eq_of_residue_eq_invertible_order (𝓞 N) P T.V b n hnu z _ hz (restrict_pow _ hy) (by
    change spMap (IsLocalRing.residue T.V) ≫ t ≫ φ' = spMap (IsLocalRing.residue T.V) ≫ spMap b ≫ y.left
    rw [← Category.assoc, ← hred _ (by rw [Category.assoc, ht₂, Category.comp_id]), Category.assoc, ht₁,
      reassoc_of% er])
  have hzy' : t ≫ φ' = spMap b ≫ y.left := congrArg (fun u => u.left) hzy
  have hxχ : x ≫ χ = spMap j ≫ t := by
    refine hφ.1.hom_ext ?_ ?_
    · rw [Category.assoc, hχ₁, hx₂, Category.assoc, ht₁, reassoc_of% ea]
    · rw [Category.assoc, hχ₂, reassoc_of% hx₁, Category.assoc, ht₂, Category.comp_id]
  refine hψ.1.hom_ext ?_ ?_
  · rw [Category.assoc, hio₁, reassoc_of% hxχ, hzy', reassoc_of% eb, Category.assoc, hx₂]
  · rw [Category.assoc, hio₂, reassoc_of% hx₁, Category.assoc, hx₁, Category.comp_id]

end GlobalTheory.InertiaTransfer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaFixesComplexFibrePureEndomorphismTorsionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.inertia_fixes_complex_fibre_pure_endomorphism_torsion : GlobalTheory.Published.FormalAlgebraisation → GlobalTheory.Published.GrothendieckMessing → ∀ (N : IntermediateField ℚ ℂ) [NumberField N] (P : Out.PolAV (Sp (𝓞 N))) (W : P.A ⟶ P.A) [IsMonHom W] (r s : 𝓞 N), IsPureBC P.A W r s → ∀ q : ℕ, q.Prime → ∀ 𝔮 : Ideal (𝓞 N), 𝔮.IsMaximal → (q : 𝓞 N) ∈ 𝔮 → r - s ∉ 𝔮 → ∀ τ : ℂ ≃+* ℂ, (∀ x : 𝓞 N, ∃ y : 𝓞 N, ((y : N) : ℂ) = τ ((x : N) : ℂ) ∧ y - x ∈ 𝔮) → ∀ (A : Over (Sp ℂ)) [GrpObj A] (ψ : A.left ⟶ P.A.left), IsGrpPullback A P.A (spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N))) ψ → ∃ io : A.left ⟶ A.left, IsGrpPullback A A (spMap (τ : ℂ →+* ℂ)) io ∧ ∀ n : ℕ, ¬ q ∣ n → ∀ y : Over.mk (𝟙 (Sp (𝓞 N))) ⟶ P.A, y ^ n = 1 → ∀ x : Sp ℂ ⟶ A.left, x ≫ A.hom = 𝟙 _ → x ≫ ψ = spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) ≫ y.left → x ≫ io = spMap (τ : ℂ →+* ℂ) ≫ x := by
  first | exact @GlobalTheory.InertiaTransfer.exists_isGrpPullback_of_inertia | exact GlobalTheory.InertiaTransfer.exists_isGrpPullback_of_inertia | (intros; apply GlobalTheory.InertiaTransfer.exists_isGrpPullback_of_inertia <;> assumption)
end
end
