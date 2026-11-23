module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.BaseOnto
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ABetaH
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ABetaLat
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ADictP
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.GalOfKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorInverseHeckeTranslatesForgetLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeTranslateHarrisTaylorPullbackBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeIdPowFiniteEtaleSurjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsEtIdealOfPlace
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtLevZero
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ALevTr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ANumSplit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ASysExt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsGHeckeMapForget
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSiegelObjectPolarisationKernelKilled
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntIntCast
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqOneOfGeometricPointsTorsion
import Mathlib.Tactic.Basify
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ATrKer
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ATrPull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentHomQuotientGaloisGroupScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackDescentAlongGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackProdInjectiveBirigidifiedGaloisIsogenyStatement
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.CoreAOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.StepAOf

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.AGalOfKer

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.galOfKer_holds :
    GalOfKer := by
  intro S A B _ _ _ _ hA hB ψ ψ' κ hψ hψ' h1 h2 hκ H hfin hHψ hinj hsurj
  haveI := hA
  haveI := hB
  obtain ⟨-, haF, haE, -⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective S A κ hA hκ
  obtain ⟨-, -, hbE, hbS⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective S B κ hB hκ
  haveI : IsProper A.hom := IsAbelianScheme.proper
  haveI : IsProper B.hom := IsAbelianScheme.proper
  haveI : Smooth B.hom := IsAbelianScheme.smooth
  haveI : IsSeparated (ψ'.left ≫ A.hom) := by rw [Over.w ψ']; infer_instance
  haveI : IsSeparated ψ'.left := IsSeparated.of_comp ψ'.left A.hom
  haveI : LocallyOfFiniteType (ψ'.left ≫ A.hom) := by rw [Over.w ψ']; infer_instance
  haveI : LocallyOfFiniteType ψ'.left := locallyOfFiniteType_of_comp ψ'.left A.hom
  haveI : IsFinite (ψ.left ≫ ψ'.left) := by rw [← Over.comp_left, h1]; exact haF
  haveI : Etale (ψ.left ≫ ψ'.left) := by rw [← Over.comp_left, h1]; exact haE
  haveI : Etale (ψ'.left ≫ ψ.left) := by rw [← Over.comp_left, h2]; exact hbE
  haveI : Surjective (ψ'.left ≫ ψ.left) := by rw [← Over.comp_left, h2]; exact hbS
  haveI : FormallyUnramified ψ'.left := FormallyUnramified.of_comp ψ'.left ψ.left
  refine ⟨hfin, ?_, ?_, ?_, IsFinite.of_comp ψ.left ψ'.left, Etale.of_comp ψ.left ψ'.left,
    Surjective.of_comp ψ'.left ψ.left, ?_⟩
  · simp [Hecke.PullHecke.transl_one]
  · intro a c
    simp [Hecke.PullHecke.transl_mul]
  · intro a
    have ht : Hecke.transl (a : 𝟙_ (Over S) ⟶ A) ≫ ψ = ψ := by
      have e := Hecke.Comp.comp_transl (𝟙 A) (a : 𝟙_ (Over S) ⟶ A)
      rw [Category.id_comp] at e
      rw [e, MonObj.mul_comp, Category.id_comp, Category.assoc, hHψ a a.2, comp_one, _root_.mul_one]
    rw [← Over.comp_left, ht]
  · intro K _ _ y y' hyy
    have hz : y' ≫ A.hom = y ≫ A.hom := by
      rw [← Over.w ψ]
      simp only [← Category.assoc, hyy]
    let Y0 : Over.mk (y ≫ A.hom) ⟶ A := Over.homMk y rfl
    let Y1 : Over.mk (y ≫ A.hom) ⟶ A := Over.homMk y' hz
    have hY : Y1 ≫ ψ = Y0 ≫ ψ := by
      ext
      simp [Y0, Y1, hyy]
    have hg : (Y1 * Y0⁻¹) ≫ ψ = 1 := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, hY, _root_.mul_inv_cancel]
    obtain ⟨g₀, hg₀H, hgg₀⟩ := hsurj K (y ≫ A.hom) (Y1 * Y0⁻¹) hg
    have key : ∀ h : 𝟙_ (Over S) ⟶ A, (y ≫ Over.Hom.left (Hecke.transl h) = y' ↔
        toUnit (Over.mk (y ≫ A.hom)) ≫ h = Y1 * Y0⁻¹) := by
      intro h
      have e := Hecke.Comp.comp_transl Y0 h
      constructor
      · intro hh
        have e' : Y0 ≫ Hecke.transl h = Y1 := by
          ext
          simpa [Y0, Y1] using hh
        rw [e'] at e
        rw [e, mul_comm Y0, _root_.mul_assoc, _root_.mul_inv_cancel, _root_.mul_one]
      · intro hh
        rw [hh, mul_comm Y1, ← _root_.mul_assoc, _root_.mul_inv_cancel, _root_.one_mul] at e
        have := congrArg Over.Hom.left e
        simpa [Y0, Y1] using this
    refine ⟨⟨g₀, hg₀H⟩, (key g₀).mpr hgg₀.symm, ?_⟩
    rintro ⟨h, hH⟩ hh
    have h3 := (key h).mp hh
    apply Subtype.ext
    have h4 : toUnit (Over.mk (y ≫ A.hom)) ≫ (h * g₀⁻¹) = 1 := by
      rw [MonObj.comp_mul, GrpObj.comp_inv, h3, hgg₀, _root_.mul_inv_cancel]
    exact mul_inv_eq_one.mp (hinj K (y ≫ A.hom) _ (H.mul_mem hH (H.inv_mem hg₀H)) h4)
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ALevRe

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.levRe_holds :
    LevRe := by
  intro q _ D R _ b N 𝔟₁ 𝔟₂ β hle hR S s o lv h
  obtain ⟨h1, h2, h3, h4⟩ := id h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    dsimp only
    rw [h.congr (hR.add x y), h1]
  · intro c x
    dsimp only
    rw [h.congr (hR.lin c x), h2]
  · intro x hx
    exact h3 _ ((hR.ker x).mpr hx)
  · intro k _ _ x
    refine ⟨fun y hy => (hR.ker y).mp ((h4 k x).1 _ hy), ?_⟩
    intro g hg
    have hg₁ : ∀ c ∈ 𝔟₁ ^ 1, g ≫ o.act.act ((algebraMap (𝓞 D.F) D.O) c) = 1 := by
      intro c hc
      rw [pow_one] at hc
      exact hg c (by rw [pow_one]; exact hle hc)
    obtain ⟨y0, hy0⟩ := (h4 k x).2 g hg₁
    obtain ⟨y, hy⟩ := hR.onto y0 (by
      intro c hc
      apply (h4 k x).1
      rw [h2, ← Category.assoc, hy0]
      exact hg c (by rw [pow_one]; exact hc))
    exact ⟨y, by dsimp only; rw [← h.congr hy, hy0]⟩
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ATrEtaK

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.trEtaK_holds :
    TrEtaK := by
  intro p _ D G L R _ _ gb h X s M₁ M₂ o' o ψ hT n κ c₁ c₂ hM1 hM2 x y hxy
  obtain ⟨v, hv, hxv⟩ := hxy
  haveI : IsMonHom ψ := hT.1
  obtain ⟨hM13, hM1c⟩ := M₁.2
  obtain ⟨hM23, hM2c⟩ := M₂.2
  have hne1 : (M₁ : ℕ) ≠ 0 := by omega
  have hne2 : (M₂ : ℕ) ≠ 0 := by omega
  have hne1' := hne1
  have hne2' := hne2
  rw [hM1] at hne1 hM1c
  rw [hM2] at hne2 hM2c
  have hn0 : 0 < n := Nat.pos_of_ne_zero (fun h0 => hne2 (by simp [h0]))
  have hκ0 : 0 < κ := Nat.pos_of_ne_zero (fun h0 => hne1 (by simp [h0]))
  have hc10 : 0 < c₁ := Nat.pos_of_ne_zero (fun h0 => hne1 (by simp [h0]))
  have hc20 : 0 < c₂ := Nat.pos_of_ne_zero (fun h0 => hne2 (by simp [h0]))
  have hnc : n.Coprime p := Nat.Coprime.coprime_dvd_left ⟨c₂, rfl⟩ hM2c
  have hnκc : (n * κ).Coprime p := Nat.Coprime.coprime_dvd_left ⟨c₁, rfl⟩ hM1c
  have hpc : ∀ (f : 𝟙_ (Over X) ⟶ o'.A) (k : ℕ), (f ^ k) ≫ ψ = (f ≫ ψ) ^ k := by
    intro f k
    induction k with
    | zero => rw [_root_.pow_zero, _root_.pow_zero, MonObj.one_comp]
    | succ k ih => rw [_root_.pow_succ, _root_.pow_succ, MonObj.mul_comp, ih]
  set a := o'.eta (c₁ • x) ≫ ψ with ha
  set b := o.eta (c₂ • y) with hb
  have haN : a ^ (M₁ : ℕ) = 1 := by
    rw [ha, ← hpc]
    exact (congrArg (· ≫ ψ) ((GObj.eta_nsmul o' _ _).symm.trans (GObj.eta_ker o' _))).trans
      (MonObj.one_comp ψ)
  have hbN : b ^ (M₂ : ℕ) = 1 := (GObj.eta_nsmul o _ _).symm.trans (GObj.eta_ker o _)
  have hunit : IsUnit (((M₁ : ℕ) * (M₂ : ℕ) : ℕ) : Γ(X, ⊤)) := by
    have hR : IsUnit (((M₁ : ℕ) * (M₂ : ℕ) : ℕ) : R) := by
      rw [← map_natCast (algebraMap ℚ R)]
      refine IsUnit.map (algebraMap ℚ R) (IsUnit.mk0 _ ?_)
      exact_mod_cast Nat.mul_ne_zero hne1' hne2'
    have := hR.map ((s.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    simpa using this
  rw [← _root_.mul_inv_eq_one]
  have hpow : (a * b⁻¹) ^ ((M₁ : ℕ) * (M₂ : ℕ)) = 1 := by
    rw [mul_pow, _root_.inv_pow, _root_.pow_mul, haN, _root_.mul_comm (M₁ : ℕ), _root_.pow_mul, hbN,
      _root_.one_pow, _root_.one_pow, inv_one, _root_.mul_one]
  have := GlobalTheory.TorsGeomPow.pow_eq_one_of_geometric_points X o.A o.ab _ hunit _ (a * b⁻¹) hpow 1 ?_
  · simpa using this
  intro k _ _ ξ
  rw [_root_.pow_one, MonObj.comp_mul, GrpObj.comp_inv, _root_.mul_inv_eq_one]
  rw [show Over.homMk ξ _ = toUnit (Over.mk (ξ ≫ (𝟙_ (Over X)).hom)) from Subsingleton.elim _ _]
  obtain ⟨β, hβ⟩ := GlobalTheory.UPel.HT.GenCmp.exists_spMap ((ξ ≫ (𝟙_ (Over X)).hom) ≫ s)
  obtain ⟨I', I'', h1, h2, hev⟩ := hT.2.2.2.2 k (ξ ≫ (𝟙_ (Over X)).hom) β hβ
  have e1 : I'.ev (M₁ : ℕ) (c₁ • x) = I'.ev (n * κ) x :=
    (KerBy.ev_nsmul _ (I'.add _) c₁ x).trans
      ((congrArg (fun m => I'.ev m x ^ c₁) hM1).trans (I'.tower (n * κ) c₁ (Nat.mul_pos hn0 hκ0) hc10 x))
  have e2 : I''.ev (M₂ : ℕ) (c₂ • y) = I''.ev n y :=
    (KerBy.ev_nsmul _ (I''.add _) c₂ y).trans
      ((congrArg (fun m => I''.ev m y ^ c₂) hM2).trans (I''.tower n c₂ hn0 hc20 y))
  have e3 : I''.ev (n * κ) (κ • y) = I''.ev n y :=
    (KerBy.ev_nsmul _ (I''.add _) κ y).trans (I''.tower n κ hn0 hκ0 y)
  have e4 : I'.ev (n * κ) x ≫ ψ = I''.ev (n * κ) (κ • y) :=
    (hev (n * κ) (Nat.mul_pos hn0 hκ0) hnκc x (κ • y)).mpr
      ⟨v, hv, by rw [GlobalTheory.HeckeApprox.inAf_nsmul]; exact hxv⟩
  rw [ha, hb, ← Category.assoc]
  exact (congrArg (· ≫ ψ) ((h1 _).trans e1)).trans (e4.trans (e3.trans (e2.symm.trans (h2 _).symm)))
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ATrSame

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels
open GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Hecke.Comp

theorem UpperTheory.Gal.FiniteEtaleModels.trSame_holds :
    TrSame := by
  intro q _ D R _ b f c k N S s o o₁ o₂ ψ₁ ψ₂ h₁ h₂
  obtain ⟨m₁, a₁, e₁, g₁, l₁, -⟩ := h₁
  obtain ⟨m₂, a₂, e₂, g₂, l₂, -⟩ := h₂
  have ep₁ := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover g₁
  have ep₂ := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover g₂
  have kill : ∀ {X : Over S} [GrpObj X] (ψ : o.A ⟶ X), IsMonHom ψ →
      GlobalTheory.ZM.IsGaloisCover (↥(heckeSubA o f N)) (fun h ↦ Over.Hom.left (transl h.1)) (Over.Hom.left ψ) →
      ∀ h ∈ heckeSubA o f N, h ≫ ψ = 1 := by
    intro X _ ψ hψ g h hh
    exact comp_eq_one_of_transl ψ h (g.inv ⟨h, hh⟩)
  obtain ⟨φ, hφ, hφc⟩ := GlobalTheory.HomDescent.exists_desc S o.A o₁.A o₂.A _ ψ₁ m₁ g₁ ψ₂ m₂ (kill ψ₂ m₂ g₂)
  obtain ⟨φ', hφ', hφ'c⟩ := GlobalTheory.HomDescent.exists_desc S o.A o₂.A o₁.A _ ψ₂ m₂ g₂ ψ₁ m₁ (kill ψ₁ m₁ g₁)
  have canc : ∀ {X Y : Over S} (π : X ⟶ Y) [Epi π.left] {Z : Over S} (u v : Y ⟶ Z), π ≫ u = π ≫ v → u = v := by
    intro X Y π _ Z u v h
    ext1
    rw [← cancel_epi π.left, ← Over.comp_left, h, Over.comp_left]
  let e : o₁.A ≅ o₂.A :=
    { hom := φ, inv := φ',
      hom_inv_id := canc ψ₁ _ _ (by rw [reassoc_of% hφc, hφ'c, Category.comp_id])
      inv_hom_id := canc ψ₂ _ _ (by rw [reassoc_of% hφ'c, hφc, Category.comp_id]) }
  haveI : IsMonHom e.hom := hφ
  haveI : IsMonHom ψ₁ := m₁
  haveI : IsMonHom ψ₂ := m₂
  have hc : ψ₁.left ≫ φ.left = ψ₂.left := by rw [← Over.comp_left, hφc]
  refine ⟨⟨φ.left, sq2 φ, isGrpPullback_of_iso e, ⟨grpSchemeSquareProductMap_fst φ, grpSchemeSquareProductMap_snd φ⟩, ?_, ?_, ?_⟩, hc⟩
  · intro a
    have t₁ := congrArg Over.Hom.left (a₁ a)
    have t₂ := congrArg Over.Hom.left (a₂ a)
    simp only [Over.comp_left] at t₁ t₂
    rw [← cancel_epi ψ₁.left, ← Category.assoc, ← t₁, Category.assoc, hc, reassoc_of% hc, ← t₂]
  · have hP := o₂.isLB
    have Z : ∀ (u : o₁.A.left ⟶ (G2 o₁.A).left) (v : o₂.A.left ⟶ (G2 o₂.A).left),
        u ≫ sq2 φ = φ.left ≫ v → (∃ t : (o₂.P.pull v).Gen, t.IsGen) →
        ∃ t : ((o₂.P.pull (sq2 φ)).pull u).Gen, t.IsGen := by
      intro u v huv hv
      rw [← GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB (pull_isLB hP _) _),
        GlobalTheory.CechPic.cls_pull (pull_isLB hP _), GlobalTheory.CechPic.cls_pull hP, ← GlobalTheory.CechPic.pull_comp, huv,
        GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.cls_pull hP v (pull_isLB hP v),
        (GlobalTheory.CechPic.cls_eq_zero_iff _).2 hv, map_zero]
    obtain ⟨l₁⟩ := l₁
    obtain ⟨l₂⟩ := l₂
    have lA := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_linComb o.isLB (fun _ : Fin (k ^ 2 / c) ↦ 𝟙 _) (fun _ ↦ (1 : ℤ))
    have Y : LBIso (o₂.P.pull (sq2 ψ₂)) ((o₂.P.pull (sq2 φ)).pull (sq2 ψ₁)) := by
      rw [← GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _),
        GlobalTheory.CechPic.cls_pull hP, GlobalTheory.CechPic.cls_pull (pull_isLB hP _), GlobalTheory.CechPic.cls_pull hP,
        ← GlobalTheory.CechPic.pull_comp, ← grpSchemeSquareProductMap_comp, hφc]
    refine GlobalTheory.T.pullback_prod_injective_birigidified_galois_isogeny S o.A o₁.A _ ψ₁ o.ab o₁.ab m₁ g₁ o₁.P (o₂.P.pull (sq2 φ)) o₁.isLB
      (pull_isLB o₂.isLB _) o₁.rig₁ o₁.rig₂ ?_ ?_ ?_
    · exact Z _ _ (lift_one_id_grpSchemeSquareProductMap φ) o₂.rig₁
    · exact Z _ _ (lift_id_one_grpSchemeSquareProductMap φ) o₂.rig₂
    · exact LBIso.trans (pull_isLB o₁.isLB _) lA (pull_isLB (pull_isLB hP _) _) (LBIso.symm l₁)
        (LBIso.trans lA (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) l₂ Y)
  · intro y
    rw [e₁ y, e₂ y, Over.comp_left, Over.comp_left, Category.assoc, hc, Category.id_comp]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.StepAHolds

section

@[expose] public section

open UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.FiniteEtaleModels

theorem stepA_holds (h₁ : MultUnit) (h₂ : LatGen) (h₃ : ClsEx) (h₄ : TrEta) (h₅ : TrBack) (h₆ : QComp) : StepA :=
  stepA_of (dictP_holds h₁) sysExt_holds trEtaK_holds trKer_holds galOfKer_holds betaH_holds (betaLat_holds h₂) numSplit_holds
    (coreA_of trPull trSame_holds levTr_holds levRe_holds h₃) h₄ h₅ h₆

end UpperTheory.Gal.FiniteEtaleModels
end
end
