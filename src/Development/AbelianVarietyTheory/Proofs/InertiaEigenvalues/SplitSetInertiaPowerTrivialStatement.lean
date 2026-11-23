module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResFinEqOneOfAway
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArtinPullbackIsGoodTwistOfAnticyclotomicTame
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIdeleExistsLocalApprox
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqProdLocalComponentsApproximating
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsResOfTameAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedPowSubOneLtOne
import Mathlib.Algebra.Order.Star.Int
import Mathlib.FieldTheory.Galois.Profinite

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoprimeAbsNormOfNatCastNotMem

section

@[expose] public section

namespace GlobalTheory.CoprimeAbsNorm

open NumberField IsDedekindDomain

theorem coprime_absNorm_of_natCast_notMem {E : Type} [Field E] [NumberField E]
    {P : HeightOneSpectrum (RingOfIntegers E)} {m : ℕ}
    (hm : (m : RingOfIntegers E) ∉ P.asIdeal) :
    Nat.Coprime m (Ideal.absNorm P.asIdeal) := by
  apply Nat.coprime_of_dvd
  intro p hp hpm hpN
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : P.asIdeal.IsPrime := P.isPrime
  haveI : Finite (RingOfIntegers E ⧸ P.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot P.asIdeal P.ne_bot
  have hcard : p ∣ Nat.card (RingOfIntegers E ⧸ P.asIdeal) := by
    rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hpN
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p hcard
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hx
    exact hp.one_lt.ne hx
  have hpx : (p : RingOfIntegers E ⧸ P.asIdeal) * x = 0 := by
    rw [← nsmul_eq_mul, ← hx]
    exact addOrderOf_nsmul_eq_zero x
  have hp0 : (p : RingOfIntegers E ⧸ P.asIdeal) = 0 :=
    (mul_eq_zero.mp hpx).resolve_right hx0
  have hpP : (p : RingOfIntegers E) ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact hp0
  obtain ⟨k, rfl⟩ := hpm
  apply hm
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hpP

end GlobalTheory.CoprimeAbsNorm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharUnramifiedOutsideSplitSetOfTame

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnramTame


theorem unramOutside_of_corr_of_tame : ∀ (D : D7) (N : NData D.R D.host D.what₂) (art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E N.Om), GlobalTheory.HeckeGal.IsGlobalArtin art → ∀ (r : G D.host.E N.Om →* ℂˣ) (M : ℕ), M ≠ 0 → (∀ σ, r σ ^ M = 1) → ∀ (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → GlobalTheory.ToricDistribution.Corr art r χ → ∀ Q : Finset (Pl D.host.E), SplitSet Q → (∀ P ∈ Q, ∀ P' : Pl D.host.E, (P' = P ∨ Formalism.BasicNotions.IsConjPl D.host P P') → χ.TameAt P') → (∀ v : Pl D.host.E, v ∉ Q → (∀ P ∈ Q, ¬ Formalism.BasicNotions.IsConjPl D.host P v) → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ σ ∈ Ine (F := D.host.E) B, r σ = 1) → GlobalTheory.ExportSeries.UnramOutside c Q := by
  intro D N art hart r Mo hMo hMr c χ hc hcorr Q hQ htame hine
  intro x hx1 hx2 hx3 hxQ
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have hidem := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3
  obtain ⟨M, hM, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2 hidem c χ hc
  choose e he hinf he1 he0 using hidem
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E M hM
    (Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x)
  set f := idem Q + cA D (idem Q) with hf
  have hcf : cA D f = f := by rw [hf, map_add (f := _), GlobalTheory.DualPairCheck.cA_cA, add_comm]
  have hfe : ∀ P ∈ Q, idemAt P * f = idemAt P := by
    intro P hP
    have k1 : idemAt P * idem Q = idemAt P :=
      GlobalTheory.PlaceModelSum.mul_sum_orth (fun a ha => (hQ.isIdemAt ha).1) (fun a ha b hb hab => hQ.mul_eq_zero ha hb hab) hP
    have k2 : idemAt P * cA D (idem Q) = 0 := by

      rw [idem, map_sum, Finset.mul_sum]
      exact Finset.sum_eq_zero fun j hj => hQ.mul_conj hP hj
    rw [hf, mul_add, k1, k2, add_zero]
  have hdelta : ∀ P e', GlobalTheory.IdemSupport.IsDelta Φ P e' → e P = e' := fun P e' h' =>
    GlobalTheory.IdemSupport.delta_unique hΦ ((GlobalTheory.IdemSupport.tie_iff hΦ (he P).1 (hinf P) P).1 (he P).2.2) h'
  have hcomp : ∀ P, (∃ a, e P = a ∧ a * f = a) → ι (finPart D (x : AE D)) P = 1 := by
    rintro P ⟨a, hea, haf⟩
    have k : e P * (x : AE D) = e P := by rw [hea, ← haf, mul_assoc, hxQ]
    have k' : ι (finPart D (e P * (x : AE D))) P = ι (finPart D (e P)) P := by rw [k]
    have e5 : ι (finPart D (e P * (x : AE D))) = ι (finPart D (e P)) * ι (finPart D (x : AE D)) := by
      rw [map_mul (finPart D) (e P) (x : AE D), map_mul ι]
    rw [e5] at k'
    change ι (finPart D (e P)) P * ι (finPart D (x : AE D)) P = ι (finPart D (e P)) P at k'
    rwa [he1 P, one_mul] at k'
  have hstar : ∀ z : D.host.E, star z = D.host.conj z := bridge_star_holds D.R D.host
  have hconj : ∀ P' v : Pl D.host.E, Formalism.BasicNotions.IsConjPl D.host P' v → v = GlobalTheory.IdemSupport.cP P' := by
    intro P' v h
    refine (GlobalTheory.IdemSupport.eq_of_le fun y hy => ?_).symm
    refine (h (GlobalTheory.IdemSupport.cO D y) y ?_).1 hy
    rw [GlobalTheory.IdemSupport.cO_coe, ← hstar, star_star]
  have hv : ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι (finPart D (x : AE D)) P) = 1 := by
    intro P
    have a := (h2 _).1 hx2 P
    have b := (h2 _).1 hx3 P
    have e' : Valued.v (ι (finPart D (x : AE D)) P) * Valued.v (ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P) = 1 := by
      rw [← map_mul]
      have : ι (finPart D (x : AE D)) P * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P = 1 := by
        change (ι (finPart D (x : AE D)) * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D))) P = 1
        rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
        rfl
      rw [this, map_one]
    refine le_antisymm a ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := e'.symm
      _ ≤ Valued.v (ι (finPart D (x : AE D)) P) * 1 := mul_le_mul_right b _
      _ = _ := mul_one _
  have key := hprod x hx1 S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS'
  apply Subtype.ext
  refine key.trans (Finset.prod_eq_one fun P hP => ?_)
  obtain ⟨a, -, b⟩ := hS P hP
  have a' : Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k P : D.host.E) := a
  have b' : Valued.v (ι (finPart D (x : AE D)) P - algebraMap D.host.E _ (k P : D.host.E)) ≤
      WithZero.exp (-1 : ℤ) * P.valuation D.host.E (k P : D.host.E) := b
  rw [hv P] at a'
  rw [← a', mul_one] at b'
  have hun : Formalism.L2.Host.IsUnitAt P (Formalism.L2.Host.atFin P (k P)) := by
    show Valued.v (((k P : D.host.E)) : P.adicCompletion D.host.E) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← a']
  have : χ.locK P (k P) = 1 := by
    show χ.loc P (Formalism.L2.Host.atFin P (k P)) = 1
    by_cases hPQ : P ∈ Q ∨ ∃ P' ∈ Q, Formalism.BasicNotions.IsConjPl D.host P' P
    · have h1P : ι (finPart D (x : AE D)) P = 1 := by
        refine hcomp P ?_
        rcases hPQ with hPQ | ⟨P', hP', hc'⟩
        · exact ⟨idemAt P, hdelta P _ (GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ (hQ.isIdemAt hPQ)), hfe P hPQ⟩
        · refine ⟨cA D (idemAt P'), ?_, ?_⟩
          · rw [hconj P' P hc']
            exact hdelta _ _ (GlobalTheory.IdemSupport.delta_conj hΦ (GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ (hQ.isIdemAt hP')))
          · rw [← hcf, ← map_mul, hfe P' hP']
      have ht : χ.TameAt P := by
        rcases hPQ with hPQ | ⟨P', hP', hc'⟩
        · exact htame P hPQ P (Or.inl rfl)
        · exact htame P' hP' P (Or.inr hc')
      refine ht _ hun ?_
      rw [h1P] at b'
      have e4 : ((Formalism.L2.Host.atFin P (k P) : (P.adicCompletion D.host.E)ˣ) : P.adicCompletion D.host.E) - 1 =
          -(1 - algebraMap D.host.E _ (k P : D.host.E)) := by
        show algebraMap D.host.E _ (k P : D.host.E) - 1 = _
        ring
      rw [e4, Valuation.map_neg]
      simpa using b'
    · push_neg at hPQ
      obtain ⟨B, hB⟩ := ReciprocityTheory.Gal.exists_isPlaceOver N.Om P
      exact GlobalTheory.ToricDistribution.Corr.unr hart hcorr hB (hine P hPQ.1 hPQ.2 B hB) _ hun
  show ((χ.locK P (k P) : ℂˣ) : ℂ) = 1
  rw [this, Units.val_one]

end GlobalTheory.UnramTame
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharUnramifiedOutsideSplitSetOfTameStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.heckeChar_unramified_outside_split_set_of_tame : ∀ (D : D7) (N : NData D.R D.host D.what₂) (art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E N.Om), GlobalTheory.HeckeGal.IsGlobalArtin art → ∀ (r : G D.host.E N.Om →* ℂˣ) (M : ℕ), M ≠ 0 → (∀ σ, r σ ^ M = 1) → ∀ (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → GlobalTheory.ToricDistribution.Corr art r χ → ∀ Q : Finset (Pl D.host.E), SplitSet Q → (∀ P ∈ Q, ∀ P' : Pl D.host.E, (P' = P ∨ Formalism.BasicNotions.IsConjPl D.host P P') → χ.TameAt P') → (∀ v : Pl D.host.E, v ∉ Q → (∀ P ∈ Q, ¬ Formalism.BasicNotions.IsConjPl D.host P v) → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ σ ∈ Ine (F := D.host.E) B, r σ = 1) → GlobalTheory.ExportSeries.UnramOutside c Q := by
  first | exact @GlobalTheory.UnramTame.unramOutside_of_corr_of_tame | exact GlobalTheory.UnramTame.unramOutside_of_corr_of_tame | (intros; apply GlobalTheory.UnramTame.unramOutside_of_corr_of_tame <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitSetInertiaPowerTrivial

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)


attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwistPullTame

theorem coprime_absNorm {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {m : ℕ}
    (hm : ((m : ℕ) : 𝓞 E) ∉ P.asIdeal) : Nat.Coprime m (Ideal.absNorm P.asIdeal) := by
  first
  | exact @_root_.GlobalTheory.CoprimeAbsNorm.coprime_absNorm_of_natCast_notMem
  | exact _root_.GlobalTheory.CoprimeAbsNorm.coprime_absNorm_of_natCast_notMem
  | (apply _root_.GlobalTheory.CoprimeAbsNorm.coprime_absNorm_of_natCast_notMem <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoprimeAbsNorm.coprime_absNorm_of_natCast_notMem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoprimeAbsNorm.coprime_absNorm_of_natCast_notMem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoprimeAbsNorm.coprime_absNorm_of_natCast_notMem ..)


open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin) in
theorem tameAt_of_ine {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {art : Neutral.B1.Ideles E →* Gab E Ω}
    (ha : IsGlobalArtin art) {r : G E Ω →* ℂˣ} {χ : Formalism.L2.Host.HChar E} (h : GlobalTheory.ToricDistribution.Corr art r χ)
    {P : HeightOneSpectrum (𝓞 E)} {B : ValuationSubring Ω} (hB : IsPlaceOver B P) {m : ℕ}
    (hm : ((m : ℕ) : 𝓞 E) ∉ P.asIdeal) (hi : ∀ σ ∈ Ine (F := E) B, r σ ^ m = 1) : χ.TameAt P := by
  intro x hx hx1
  obtain ⟨a, ha'⟩ := GlobalTheory.Mem.UnrAe.exists_levelLe χ P
  have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem P.asIdeal
  have hlt : Valued.v ((Ideal.absNorm P.asIdeal : ℕ) : P.adicCompletion E) < 1 := by
    rw [← map_natCast (algebraMap (𝓞 E) (P.adicCompletion E)), GlobalTheory.Mem.WildChar.valued_algebraMap_lt_one]
    exact hmem
  have h3 := ha' _ (GlobalTheory.Mem.UnrAe.isUnitAt_pow hx (Ideal.absNorm P.asIdeal ^ a)) (by
    rw [Units.val_pow_eq_pow_val]
    refine GlobalTheory.Mem.WildChar.val_pow_pow_sub_one_le _ (le_of_eq hx) (hx1.trans_lt ?_) hlt a
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num)
  rw [map_pow] at h3
  have h4 : χ.loc P x ^ m = 1 := by
    obtain ⟨σ, hσ, e⟩ := (ha.ine P B hB _).mp ⟨x, hx, rfl⟩
    have e2 : χ.loc P x = r σ := h _ σ e.symm
    rw [e2, hi σ hσ]
  have hc : Nat.Coprime m (Ideal.absNorm P.asIdeal ^ a) := (coprime_absNorm hm).pow_right a
  rw [← pow_one (χ.loc P x), ← hc.gcd_eq_one]
  exact pow_gcd_eq_one.2 ⟨h4, h3⟩

theorem ine_pow_of_conj {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N) {A : Type} [CommGroup A]
    {φ : G D.host.E N.Om →* A} (hanti : AntiHom X.cc φ) {P P' : Pl D.host.E} (hc : Formalism.BasicNotions.IsConjPl D.host P P') {m : ℕ}
    (h : ∀ B : ValuationSubring N.Om, IsPlaceOver B P → ∀ σ ∈ Ine (F := D.host.E) B, φ σ ^ m = 1)
    (B' : ValuationSubring N.Om) (hB' : IsPlaceOver B' P') (σ : G D.host.E N.Om) (hσ : σ ∈ Ine (F := D.host.E) B') :
    φ σ ^ m = 1 := by
  have h1 := GlobalTheory.TwistDet.cConj_mem_ine X hσ
  have h2 := GlobalTheory.TwistDet.isPlaceOver_moveVal_cc X (GlobalTheory.TwistDet.isConjPl_symm hc) hB'
  have h3 := h _ h2 _ h1
  rw [GlobalTheory.TwistDet.antiHom_cConj X hanti, inv_pow, inv_eq_one] at h3
  exact h3

theorem natCast_mem_conj {D : D7} {P P' : Pl D.host.E} (hc : Formalism.BasicNotions.IsConjPl D.host P P') (m : ℕ) :
    ((m : ℕ) : 𝓞 D.host.E) ∈ P'.asIdeal ↔ ((m : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
  rw [GlobalTheory.TwistDet.isConjPl_iff.1 hc, map_natCast]

end GlobalTheory.TwistPullTame

namespace GlobalTheory.TwistPullTame

open GlobalTheory.TwistPull

theorem good_pull_tame : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (a : Recip D N.Om), a.Good → ∀ (A : Type) [CommGroup A] (φ : G D.host.E N.Om →* A), IsOpen (φ.ker : Set (G D.host.E N.Om)) → AntiHom X.cc φ → ∀ Q : Finset (Pl D.host.E), SplitSet Q → (∀ P ∈ Q, ∃ m : ℕ, ((m : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ ∀ B : ValuationSubring N.Om, IsPlaceOver B P → ∀ σ ∈ Ine (F := D.host.E) B, φ σ ^ m = 1) → (∀ v : Pl D.host.E, v ∉ Q → (∀ P ∈ Q, ¬ Formalism.BasicNotions.IsConjPl D.host P v) → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ σ ∈ Ine (F := D.host.E) B, φ σ = 1) → (⟨Q, a.pull φ, resOf (a.pull φ)⟩ : Twist D A).Good := by
  intro D N X a ha A _ φ hφ hanti Q hQ hQm hunr
  haveI := finite_range (D := D) hφ
  set M := Nat.card φ.range with hMdef
  have hM : M ≠ 0 := Nat.card_pos.ne'
  have hr : ∀ f : φ.range →* ℂˣ, IsOpen ((f.comp φ.rangeRestrict).ker : Set (G D.host.E N.Om)) ∧
      ∀ σ, (f.comp φ.rangeRestrict) σ ^ M = 1 := fun f => by
    refine ⟨Subgroup.isOpen_mono (H₁ := φ.ker) (fun g hg => ?_) hφ, fun σ => ?_⟩
    · have : φ.rangeRestrict g = 1 := Subtype.ext (MonoidHom.mem_ker.1 hg)
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, this, map_one]
    · rw [MonoidHom.comp_apply, ← map_pow, pow_card_eq_one', map_one]
  have hanti' : ∀ f : φ.range →* ℂˣ, AntiHom X.cc (f.comp φ.rangeRestrict) := fun f g g' hg => by
    have e : φ.rangeRestrict g' = (φ.rangeRestrict g)⁻¹ := Subtype.ext (hanti g g' hg)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, e, map_inv]

  have hin : ∀ P ∈ Q, ∀ P' : Pl D.host.E, (P' = P ∨ Formalism.BasicNotions.IsConjPl D.host P P') → ∃ m : ℕ,
      ((m : ℕ) : 𝓞 D.host.E) ∉ P'.asIdeal ∧
        ∀ B : ValuationSubring N.Om, IsPlaceOver B P' → ∀ σ ∈ Ine (F := D.host.E) B, φ σ ^ m = 1 := by
    intro P hP P' hP'
    obtain ⟨m, hm, hB⟩ := hQm P hP
    rcases hP' with rfl | hc
    · exact ⟨m, hm, hB⟩
    · exact ⟨m, fun h => hm ((natCast_mem_conj hc m).1 h), ine_pow_of_conj X hanti hc hB⟩
  have htame : ∀ (f : φ.range →* ℂˣ) (χ : Formalism.L2.Host.HChar D.host.E),
      GlobalTheory.ToricDistribution.Corr a.art (f.comp φ.rangeRestrict) χ →
      ∀ P ∈ Q, ∀ P' : Pl D.host.E, (P' = P ∨ Formalism.BasicNotions.IsConjPl D.host P P') → χ.TameAt P' := by
    intro f χ hχ P hP P' hP'
    obtain ⟨m, hm, hB⟩ := hin P hP P' hP'
    obtain ⟨B, hB'⟩ := ReciprocityTheory.Gal.exists_isPlaceOver N.Om P'
    refine tameAt_of_ine ha.artin hχ hB' hm fun σ hσ => ?_
    have e : φ.rangeRestrict σ ^ m = 1 := Subtype.ext (by
      rw [SubmonoidClass.coe_pow, MonoidHom.coe_rangeRestrict, hB B hB' σ hσ]; rfl)
    rw [MonoidHom.comp_apply, ← map_pow, e, map_one]
  refine ⟨isOpen_ker_pull ha hφ, fun x => pull_rat ha φ x, fun y => ?_, hQ, ?_, fun PP hPP => isResAt_resOf ?_⟩
  ·
    refine (pull_eq_of_chars a hφ (y := 1) fun f => ?_).trans (map_one _)
    obtain ⟨h1, h2⟩ := hr f
    obtain ⟨c, χ, hc, hχ, hcr⟩ := exists_chrEq_pull ha h1 hM h2
    rw [map_one]
    refine Units.ext ((hcr _).symm.trans ?_)
    rw [real_C D N X a.art ha.artin _ _ hM h2 (hanti' f) c χ hc hχ y]
    simp
  ·
    intro x h1 h2 h3 h4
    refine (pull_eq_of_chars a hφ (y := 1) fun f => ?_).trans (map_one _)
    obtain ⟨o1, o2⟩ := hr f
    obtain ⟨c, χ, hc, hχ, hcr⟩ := exists_chrEq_pull ha o1 hM o2
    rw [map_one]
    refine Units.ext ((hcr _).symm.trans ?_)
    rw [GlobalTheory.T.heckeChar_unramified_outside_split_set_of_tame D N a.art ha.artin _ M hM o2 c χ hc hχ Q hQ (htame f χ hχ) (fun v hv hc' B hB σ hσ => by
      rw [MonoidHom.comp_apply, show φ.rangeRestrict σ = 1 from Subtype.ext (hunr v hv hc' B hB σ hσ), map_one]) x h1 h2 h3 h4]
    simp
  ·
    have hPP := hQ.isIdemAt hPP
    have same : ∀ (x x' : (AE D)ˣ) (u : (kP PP)ˣ), (1 - idemAt PP) * (x : AE D) = 1 - idemAt PP →
        (1 - idemAt PP) * (x' : AE D) = 1 - idemAt PP →
        ∀ (hi : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
          (hi' : toEAf D (x' : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E),
        resS D.host.F PP ⟨_, hi⟩ = u → resS D.host.F PP ⟨_, hi'⟩ = u → a.pull φ x = a.pull φ x' := by
      intro x x' u hx hx' hi hi' hu hu'
      refine pull_eq_of_chars a hφ fun f => ?_
      obtain ⟨o1, o2⟩ := hr f
      obtain ⟨c, χ, hc, hχ, hcr⟩ := exists_chrEq_pull ha o1 hM o2
      have ht : χ.TameAt PP := htame f χ hχ PP ‹_› PP (Or.inl rfl)
      obtain ⟨ρ, hρ⟩ := GlobalTheory.exists_isRes_of_tameAt D χ PP ht
      have e : ∀ z : (AE D)ˣ, (1 - idemAt PP) * (z : AE D) = 1 - idemAt PP →
          ∀ (hz : toEAf D (z : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E),
          resS D.host.F PP ⟨_, hz⟩ = u → a.pull (f.comp φ.rangeRestrict) z = ρ u := fun z hz hzi hzu =>
        Units.ext ((hcr z).symm.trans (GlobalTheory.ConjTwist.eq_res_of_chrEq hc hPP ht hρ z hz hzi u hzu))
      rw [e x hx hi hu, e x' hx' hi' hu']
    have hlift := fun u => GlobalTheory.ConjTwist.exists_isLocUnit hPP u
    choose xs hxs using hlift
    have hmul : ∀ u v, a.pull φ (xs (u * v)) = a.pull φ (xs u * xs v) := fun u v => by
      obtain ⟨hi, hu⟩ := (hxs (u * v)).res
      obtain ⟨hi1, hu1⟩ := (hxs u).res
      obtain ⟨hi2, hu2⟩ := (hxs v).res
      have hi3 : toEAf D ((xs u * xs v : (AE D)ˣ) : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
        rw [Units.val_mul, map_mul]
        exact mul_mem hi1 hi2
      refine same _ _ (u * v) (hxs (u * v)).off ?_ hi hi3 hu ?_
      · rw [Units.val_mul, ← mul_assoc, (hxs u).off, (hxs v).off]
      · have : (⟨_, hi3⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨_, hi1⟩ * ⟨_, hi2⟩ :=
          Subtype.ext (by
            change toEAf D ((xs u * xs v : (AE D)ˣ) : AE D) = toEAf D (xs u : AE D) * toEAf D (xs v : AE D)
            rw [Units.val_mul, map_mul])
        rw [this, map_mul, hu1, hu2, Units.val_mul]
    refine ⟨MonoidHom.mk' (fun u => a.pull φ (xs u)) (fun u v => ?_), ?_⟩
    · show a.pull φ (xs (u * v)) = a.pull φ (xs u) * a.pull φ (xs v)
      rw [hmul, map_mul]
    · intro x hx hi u hu
      show a.pull φ x = a.pull φ (xs u)
      obtain ⟨hi', hu'⟩ := (hxs u).res
      exact same x (xs u) u hx (hxs u).off hi hi' hu hu'

end GlobalTheory.TwistPullTame
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitSetInertiaPowerTrivialStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)


attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.split_set_inertia_power_trivial : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (a : Recip D N.Om), a.Good → ∀ (A : Type) [CommGroup A] (φ : G D.host.E N.Om →* A), IsOpen (φ.ker : Set (G D.host.E N.Om)) → AntiHom X.cc φ → ∀ Q : Finset (Pl D.host.E), SplitSet Q → (∀ P ∈ Q, ∃ m : ℕ, ((m : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ ∀ B : ValuationSubring N.Om, IsPlaceOver B P → ∀ σ ∈ Ine (F := D.host.E) B, φ σ ^ m = 1) → (∀ v : Pl D.host.E, v ∉ Q → (∀ P ∈ Q, ¬ Formalism.BasicNotions.IsConjPl D.host P v) → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ σ ∈ Ine (F := D.host.E) B, φ σ = 1) → (⟨Q, a.pull φ, resOf (a.pull φ)⟩ : Twist D A).Good := by
  first | exact @GlobalTheory.TwistPullTame.good_pull_tame | exact GlobalTheory.TwistPullTame.good_pull_tame | (intros; apply GlobalTheory.TwistPullTame.good_pull_tame <;> assumption)
end
end
