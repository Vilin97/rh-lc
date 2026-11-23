module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsQuotTriv
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LSigFin
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsEtIdealOfPlace
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelEqKN
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEtaleSurjectiveProj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LPtsHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LiesAbsOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PSigmaFEt

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LGrpHolds

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.lGrp_holds :
    LGrp := by
  intro Γ _ K K₀ K₁ KN KM hMN hNK hN0 hM1 h10 hnorm hdec b₀ hb₀ u hu
  obtain ⟨a, haK, ha0, hau⟩ := hdec u⁻¹ (inv_mem hu)
  have hconj : ∀ m ∈ KM, a⁻¹ * m * a ∈ KM := by
    intro m hm
    simpa using hnorm a⁻¹ (inv_mem ha0) m hm
  have hmem : ∀ (c : ↥K ⧸ KN.subgroupOf K) (n : ↥KN ⧸ KM.subgroupOf KN),
      b₀⁻¹ * ((Quotient.out c : ↥K) : Γ) * ((Quotient.out n : ↥KN) : Γ) * u⁻¹ ∈ K₁ →
      b₀⁻¹ * ((Quotient.out c : ↥K) : Γ) * ((Quotient.out n : ↥KN) : Γ) * a ∈ K ⊓ K₁ := by
    intro c n hcn
    refine ⟨?_, ?_⟩
    · exact K.mul_mem (K.mul_mem (K.mul_mem (K.inv_mem hb₀) (Quotient.out c).2) (hNK (Quotient.out n).2)) haK
    · have hua : u * a ∈ K₁ := by simpa using K₁.inv_mem hau
      rw [show b₀⁻¹ * ((Quotient.out c : ↥K) : Γ) * ((Quotient.out n : ↥KN) : Γ) * a
          = (b₀⁻¹ * ((Quotient.out c : ↥K) : Γ) * ((Quotient.out n : ↥KN) : Γ) * u⁻¹) * (u * a) by group]
      exact K₁.mul_mem hcn hua
  refine Eq.trans (b := Nat.card ((K ⊓ K₁ : Subgroup Γ) ⧸ KM.subgroupOf (K ⊓ K₁))) ?_ rfl
  refine Nat.card_eq_of_bijective (fun cn => (QuotientGroup.mk ⟨_, hmem cn.1.1 cn.1.2 cn.2⟩ : (K ⊓ K₁ : Subgroup Γ) ⧸ KM.subgroupOf (K ⊓ K₁))) ⟨?_, ?_⟩
  · rintro ⟨⟨c₁, n₁⟩, h₁⟩ ⟨⟨c₂, n₂⟩, h₂⟩ h
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    have h' : ((Quotient.out n₁ : ↥KN) : Γ)⁻¹ * ((Quotient.out c₁ : ↥K) : Γ)⁻¹
        * ((Quotient.out c₂ : ↥K) : Γ) * ((Quotient.out n₂ : ↥KN) : Γ) ∈ KM := by
      have := hnorm a ha0 _ h
      convert this using 1
      group
    have hc : c₁ = c₂ := by
      rw [← QuotientGroup.out_eq' c₁, ← QuotientGroup.out_eq' c₂, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have := KN.mul_mem (KN.mul_mem (Quotient.out n₁).2 (hMN h')) (KN.inv_mem (Quotient.out n₂).2)
      convert this using 1
      group
    subst hc
    have hn : n₁ = n₂ := by
      rw [← QuotientGroup.out_eq' n₁, ← QuotientGroup.out_eq' n₂, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      convert h' using 1
      group
    subst hn
    rfl
  · intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨x, hK, hK1⟩ := x
      let g : ↥K := ⟨b₀ * x * a⁻¹, K.mul_mem (K.mul_mem hb₀ hK) (K.inv_mem haK)⟩
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (KN.subgroupOf K) g
      have hkN : ((k : ↥K) : Γ) ∈ KN := k.2
      let n₀ : ↥KN := ⟨((k : ↥K) : Γ)⁻¹, KN.inv_mem hkN⟩
      obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (KM.subgroupOf KN) n₀
      have hmM : ((m : ↥KN) : Γ) ∈ KM := m.2
      have key : ((Quotient.out (QuotientGroup.mk g : ↥K ⧸ KN.subgroupOf K) : ↥K) : Γ)
          * ((Quotient.out (QuotientGroup.mk n₀ : ↥KN ⧸ KM.subgroupOf KN) : ↥KN) : Γ)
          = b₀ * x * a⁻¹ * ((m : ↥KN) : Γ) := by
        rw [hk, hm]
        simp only [Subgroup.coe_mul, g, n₀]
        group
      refine ⟨⟨(QuotientGroup.mk g, QuotientGroup.mk n₀), ?_⟩, ?_⟩
      · dsimp only
        rw [mul_assoc b₀⁻¹, key,
          show b₀⁻¹ * (b₀ * x * a⁻¹ * ((m : ↥KN) : Γ)) * u⁻¹
            = x * (a⁻¹ * ((m : ↥KN) : Γ) * a) * (a⁻¹ * u⁻¹) by group]
        exact K₁.mul_mem (K₁.mul_mem hK1 (hM1 (hconj _ hmM))) hau
      · dsimp only
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [mul_assoc b₀⁻¹, key,
          show (b₀⁻¹ * (b₀ * x * a⁻¹ * ((m : ↥KN) : Γ)) * a)⁻¹ * x
            = (a⁻¹ * ((m : ↥KN) : Γ) * a)⁻¹ by group]
        exact KM.inv_mem (hconj _ hmM)
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LIdxHolds

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.lIdx_holds :
    LIdx := by
  intro p _ D G L N hN
  obtain ⟨K1, h1⟩ := GlobalTheory.LKGeo.KNLevel.exists_level_eq_KN p D G L 1 one_pos
  obtain ⟨KN, hKN⟩ := GlobalTheory.LKGeo.KNLevel.exists_level_eq_KN p D G L N hN
  have hc : CompactSpace (L.KN 1) := by
    rw [← h1]
    exact isCompact_iff_compactSpace.1 K1.compact
  have ho : IsOpen (((L.KN N).subgroupOf (L.KN 1) : Subgroup (L.KN 1)) : Set (L.KN 1)) := by
    rw [← hKN]
    exact KN.K.isOpen.preimage continuous_subtype_val
  have hf : Finite ((L.KN 1) ⧸ (L.KN N).subgroupOf (L.KN 1)) :=
    Subgroup.quotient_finite_of_isOpen _ ho
  exact Nat.card_pos.ne'
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LPCount

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.lCount_holds :
    LSigPt → LSigFin → LCount := by
  intro hpt hfin I B _ _ W Z Y Y' cls f kc π s m hf he hs hes hm h
  obtain ⟨hsF, hsE⟩ := hfin B Y' Y s hs hes
  obtain ⟨hdF, hdE⟩ := hfin I W Z f hf he
  set sB : (∐ fun _ : B => Y') ⟶ Y := Sigma.desc fun _ : B => s with hsB
  set ℓ := pullback.lift _ _ h with hℓ
  have hℓ1 : ℓ ≫ pullback.fst π sB = Sigma.desc fun _ : I => f := pullback.lift_fst _ _ h
  have hℓ2 : ℓ ≫ pullback.snd π sB =
      Sigma.desc fun c : I => kc c ≫ Sigma.ι (fun _ : B => Y') (cls c) := pullback.lift_snd _ _ h
  haveI := hsF
  haveI := hsE
  haveI : IsFinite (pullback.fst π sB) := inferInstance
  haveI : Etale (pullback.fst π sB) := inferInstance
  haveI : IsFinite (ℓ ≫ pullback.fst π sB) := by rw [hℓ1]; exact hdF
  haveI : Etale (ℓ ≫ pullback.fst π sB) := by rw [hℓ1]; exact hdE
  refine ⟨IsFinite.of_comp ℓ (pullback.fst π sB), Etale.of_comp ℓ (pullback.fst π sB), ?_⟩
  intro K _ _ x
  obtain ⟨⟨b, y'⟩, hb⟩ := (hpt B Y' K).2 (x ≫ pullback.snd π sB)
  replace hb : y' ≫ Sigma.ι (fun _ : B => Y') b = x ≫ pullback.snd π sB := hb
  have hy : y' ≫ s = (x ≫ pullback.fst π sB) ≫ π := by
    calc y' ≫ s = (y' ≫ Sigma.ι (fun _ : B => Y') b) ≫ sB := by simp [hsB]
      _ = (x ≫ pullback.fst π sB) ≫ π := by
        rw [hb, Category.assoc, Category.assoc, pullback.condition]
  have key : ∀ (c : I) (v : sp K ⟶ W), (v ≫ Sigma.ι (fun _ : I => W) c) ≫ ℓ = x ↔
      v ≫ f = x ≫ pullback.fst π sB ∧ cls c = b ∧ v ≫ kc c = y' := by
    intro c v
    have e1 : ((v ≫ Sigma.ι (fun _ : I => W) c) ≫ ℓ) ≫ pullback.fst π sB = v ≫ f := by
      rw [Category.assoc, hℓ1]; simp
    have e2 : ((v ≫ Sigma.ι (fun _ : I => W) c) ≫ ℓ) ≫ pullback.snd π sB =
        (v ≫ kc c) ≫ Sigma.ι (fun _ : B => Y') (cls c) := by
      rw [Category.assoc, hℓ2]; simp
    constructor
    · intro hx
      rw [hx] at e1 e2
      have h2 : (fun p : B × (sp K ⟶ Y') => p.2 ≫ Sigma.ι (fun _ : B => Y') p.1) (cls c, v ≫ kc c) =
          (fun p : B × (sp K ⟶ Y') => p.2 ≫ Sigma.ι (fun _ : B => Y') p.1) (b, y') := by
        show (v ≫ kc c) ≫ Sigma.ι (fun _ : B => Y') (cls c) = y' ≫ Sigma.ι (fun _ : B => Y') b
        rw [← e2, hb]
      obtain ⟨h3, h4⟩ := Prod.mk.inj ((hpt B Y' K).1 h2)
      exact ⟨e1.symm, h3, h4⟩
    · rintro ⟨h1, h3, h4⟩
      apply pullback.hom_ext
      · rw [e1, h1]
      · rw [e2, h3, h4, hb]
  rw [← hm K (x ≫ pullback.fst π sB) b y' hy]
  let F : {cx : I × (sp K ⟶ W) // cx.2 ≫ f = x ≫ pullback.fst π sB ∧ cls cx.1 = b ∧ cx.2 ≫ kc cx.1 = y'} →
      {y : sp K ⟶ ∐ (fun _ : I => W) // y ≫ ℓ = x} :=
    fun p => ⟨p.1.2 ≫ Sigma.ι (fun _ : I => W) p.1.1, (key _ _).2 p.2⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨⟨c, v⟩, hv⟩ ⟨⟨c', v'⟩, hv'⟩ e
      have e' : (fun p : I × (sp K ⟶ W) => p.2 ≫ Sigma.ι (fun _ : I => W) p.1) (c, v) =
          (fun p : I × (sp K ⟶ W) => p.2 ≫ Sigma.ι (fun _ : I => W) p.1) (c', v') :=
        congrArg Subtype.val e
      exact Subtype.ext ((hpt I W K).1 e')
    · rintro ⟨y, hy'⟩
      obtain ⟨⟨c, v⟩, hv⟩ := (hpt I W K).2 y
      replace hv : v ≫ Sigma.ι (fun _ : I => W) c = y := hv
      subst hv
      exact ⟨⟨(c, v), (key c v).1 hy'⟩, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective F hF)).symm
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LPSigFin

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.lSigFin_holds :
    LSigFin := by
  intro I _ W Z f hf he
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  have hfold := GlobalTheory.Et.TrivTors.isFinite_sigmaDesc_fin W k
  let i : (∐ fun _ : I => W) ≅ ∐ fun _ : Fin k => W :=
    Sigma.whiskerEquiv (f := fun _ : I => W) (g := fun _ : Fin k => W) e fun _ => Iso.refl W
  have hd : (Sigma.desc fun _ : I => f) = i.hom ≫ (Sigma.desc fun _ : Fin k => 𝟙 W) ≫ f := by
    apply Sigma.hom_ext
    intro a
    simp [i]
  refine ⟨by rw [hd]; infer_instance, ?_⟩
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale)
  exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun _ => inferInstance
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LPSigPt

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.lSigPt_holds :
    LSigPt := by
  intro I W Ω _
  haveI : Unique (sp Ω) := inferInstanceAs (Unique (PrimeSpectrum Ω))
  constructor
  · rintro ⟨i, x⟩ ⟨j, x'⟩ h
    have h' : x ≫ Sigma.ι (fun _ : I => W) i = x' ≫ Sigma.ι (fun _ : I => W) j := h
    have e : (Sigma.ι (fun _ : I => W) i) (x default) = (Sigma.ι (fun _ : I => W) j) (x' default) := by
      have := congrArg (fun f : sp Ω ⟶ _ => f default) h'
      simpa using this
    have e2 := (sigmaι_eq_iff _ _ _ _ _).mp e
    obtain ⟨rfl⟩ : i = j := congrArg Sigma.fst e2
    have : x = x' := (cancel_mono (Sigma.ι (fun _ : I => W) i)).mp h'
    rw [this]
  · intro y
    obtain ⟨i, w, hw⟩ := (sigmaOpenCover fun _ : I => W).exists_eq (y default)
    have hr : Set.range y ⊆ Set.range (Sigma.ι (fun _ : I => W) i) := by
      rintro _ ⟨p, rfl⟩
      rw [Subsingleton.elim p default]
      exact ⟨w, hw⟩
    exact ⟨(i, IsOpenImmersion.lift (Sigma.ι (fun _ : I => W) i) y hr), IsOpenImmersion.lift_fac _ _ _⟩
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LiesAbsHolds

section

@[expose] public section

namespace UpperTheory.Gal.FiniteEtaleModels

theorem liesAbs_holds : LiesAbs :=
  liesAbs_of (lPts_holds lGrp_holds) (lCount_holds lSigPt_holds lSigFin_holds) lIdx_holds sigmaFEt_holds

end UpperTheory.Gal.FiniteEtaleModels
end
end
