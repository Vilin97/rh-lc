module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolySmulOfProd
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharsOfReading
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfPowEqOneOfValLt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
public import Formalism.CyclotomicNorms.StatementT
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.FieldTheory.Finite.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstTwistCharacterEqLadicHeckeCharacter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIneOfUnit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfPowEqSelf

section

@[expose] public section

open Polynomial

namespace GlobalTheory.RangeOfPowerFixed

theorem mem_range_of_pow_eq_self {g : ℕ} [Fact (Nat.Prime g)] {K : Type*} [Field K] [Algebra (ZMod g) K]
    (z : K) (hz : z ^ g = z) : ∃ c : ZMod g, algebraMap (ZMod g) K c = z := by
  classical
  by_contra hne
  simp only [not_exists] at hne
  have hg : 1 < g := (Fact.out : Nat.Prime g).one_lt
  set P : K[X] := X ^ g - X with hPeq
  have hP0 : P ≠ 0 := Polynomial.X_pow_sub_X_ne_zero hg
  have hdeg : P.natDegree = g := Polynomial.natDegree_X_pow_sub_X (R := K) hg

  have hroot : ∀ x : K, x ^ g = x → x ∈ P.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, mem_roots hP0, hPeq]
    simp [hx]

  set S : Finset K := insert z (Finset.univ.image (algebraMap (ZMod g) K)) with hSeq
  have hzS : z ∉ Finset.univ.image (algebraMap (ZMod g) K) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact hne
  have hcard : S.card = g + 1 := by
    rw [hSeq, Finset.card_insert_of_notMem hzS,
      Finset.card_image_of_injective _ (algebraMap (ZMod g) K).injective, Finset.card_univ, ZMod.card]
  have hsub : S ⊆ P.roots.toFinset := by
    intro x hx
    rw [hSeq, Finset.mem_insert, Finset.mem_image] at hx
    rcases hx with rfl | ⟨c, -, rfl⟩
    · exact hroot _ hz
    · exact hroot _ (by rw [← map_pow, ZMod.pow_card])
  have := (Finset.card_le_card hsub).trans
    ((Multiset.toFinset_card_le _).trans (card_roots' P))
  omega

theorem main : ∀ {g : ℕ} [inst : Fact (Nat.Prime g)] (z : Formalism.CyclotomicNorms.Fbar g), z ^ g = z →
    ∃ (c : ZMod g), (Algebra.algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) : ZMod g → Formalism.CyclotomicNorms.Fbar g) c = z := by
  intro g _ z hz
  exact mem_range_of_pow_eq_self z hz

end GlobalTheory.RangeOfPowerFixed
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsZmodEq

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TameGenRep

open Formalism.L2.NT

theorem exists_zmod_eq {g : ℕ} [Fact g.Prime] (z : Formalism.CyclotomicNorms.Fbar g) (hz : z ^ g = z) :
    ∃ c : ZMod g, algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c = z := by
  first
  | exact @_root_.GlobalTheory.RangeOfPowerFixed.main
  | exact _root_.GlobalTheory.RangeOfPowerFixed.main
  | (apply _root_.GlobalTheory.RangeOfPowerFixed.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.RangeOfPowerFixed.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RangeOfPowerFixed.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RangeOfPowerFixed.main ..)

theorem exists_rep : ∀ (D : D7), GrpSide D → ∀ (k : Fin 2) (v : D.nd.PlG k), normV (D.naut.plGw k v) = D.host.g k ∧ ∃ (u ϖ : 𝓞 D.host.E) (π : D.nd.Om), u ∉ (D.naut.plGw k v).asIdeal ∧ ϖ ∈ (D.naut.plGw k v).asIdeal ∧ ϖ ∉ (D.naut.plGw k v).asIdeal ^ 2 ∧ π ^ (normV (D.naut.plGw k v) - 1) = algebraMap D.host.E D.nd.Om (ϖ : D.host.E) ∧ (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) < 1 ∧ orderOf (D.ntypes.tg k v π / π) = normV (D.naut.plGw k v) - 1 := by
  intro D hG k v
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  haveI : CharZero D.nd.Om := charZero_of_injective_ringHom (f := algebraMap D.host.E D.nd.Om) (algebraMap D.host.E D.nd.Om).injective
  have hgp : (D.host.g k).Prime := D.host.g_prime k
  have hAP : IsPlaceOver (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) :=
    D.nd.plOm.2 (D.naut.plGw k v)
  have hgP : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
  have hspl := GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) hgp (D.nd.g_split k) (D.naut.plGw k v) hgP
  have hN : normV (D.naut.plGw k v) = D.host.g k := by
    rw [← hspl.1, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hg1 : 0 < D.host.g k - 1 := by have := hgp.two_le; omega
  have hgΩ : ((D.host.g k : ℕ) : D.nd.Om) ≠ 0 := Nat.cast_ne_zero.mpr hgp.ne_zero
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq ((D.host.g k : ℕ) : D.nd.Om) hg1
  have hT : redThrough (D.nd.plOm.1 (D.naut.plGw k v)) (hG.kv k v) (D.ntypes.tg k v π / π) = hG.ζ k 1 :=
    hG.tg_tame k v 1 one_pos π (by rw [pow_one]; exact hπ)
  have hq : D.ntypes.tg k v π / π ∈ D.nd.plOm.1 (D.naut.plGw k v) :=
    tameQuot_mem (D.nd.plOm.1 (D.naut.plGw k v)) (D.ntypes.tg k v) hg1 hgΩ hπ
  have hpow : (D.ntypes.tg k v π / π) ^ (D.host.g k - 1) = 1 := tameQuot_pow (D.ntypes.tg k v) hgΩ hπ
  have hζ := (hG.ζ_gen k 1 one_pos).1
  rw [pow_one] at hζ
  have hζ1 : hG.ζ k 1 ^ (D.host.g k - 1) = 1 := by rw [← hζ]; exact pow_orderOf_eq_one _
  have hζpow : hG.ζ k 1 ^ D.host.g k = hG.ζ k 1 := by
    calc _ = hG.ζ k 1 ^ (D.host.g k - 1) * hG.ζ k 1 := by rw [← pow_succ, Nat.sub_add_cancel hgp.one_le]
      _ = _ := by rw [hζ1, one_mul]
  have hζ0 : hG.ζ k 1 ≠ 0 := by
    intro h
    rw [h, zero_pow hg1.ne'] at hζ1
    exact zero_ne_one hζ1
  obtain ⟨c, hc⟩ := exists_zmod_eq _ hζpow
  have hca : ((c.val : ℕ) : Formalism.CyclotomicNorms.Fbar (D.host.g k)) = hG.ζ k 1 := by
    rw [← hc, ← map_natCast (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))), ZMod.natCast_zmod_val]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = c.val := ⟨_, rfl⟩
  rw [← hn] at hca
  have hcast : algebraMap D.host.E D.nd.Om ((n : 𝓞 D.host.E) : D.host.E) = (n : D.nd.Om) := by
    simp
  have haA : (n : D.nd.Om) ∈ D.nd.plOm.1 (D.naut.plGw k v) := natCast_mem _ _
  have hra : redThrough (D.nd.plOm.1 (D.naut.plGw k v)) (hG.kv k v) (n : D.nd.Om) =
      hG.kv k v (IsLocalRing.residue _ ⟨_, haA⟩) := by
    unfold redThrough; rw [dite_eq_left haA]
  have hra' : hG.kv k v (IsLocalRing.residue _ ⟨_, haA⟩) = hG.ζ k 1 := by
    have : (⟨(n : D.nd.Om), haA⟩ : D.nd.plOm.1 (D.naut.plGw k v)) = (n : D.nd.plOm.1 (D.naut.plGw k v)) :=
      Subtype.ext (by simp)
    rw [this, map_natCast, map_natCast, hca]
  have hrq : redThrough (D.nd.plOm.1 (D.naut.plGw k v)) (hG.kv k v) (D.ntypes.tg k v π / π) =
      hG.kv k v (IsLocalRing.residue _ ⟨_, hq⟩) := by
    unfold redThrough; rw [dite_eq_left hq]
  have hval : (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v π / π - (n : D.nd.Om)) < 1 := by
    have h1 := (hG.kv k v).injective (((hrq.symm.trans hT).trans hra'.symm))
    have h2 := Ideal.Quotient.eq.1 h1
    have h3 := ((D.nd.plOm.1 (D.naut.plGw k v)).valuation_lt_one_iff _).1 h2
    exact h3
  have hu : (n : 𝓞 D.host.E) ∉ (D.naut.plGw k v).asIdeal := by
    intro h
    have h1 := (hAP _).2 h
    have h2 : (n : D.nd.Om) ∈ D.nd.plOm.1 (D.naut.plGw k v) := haA
    have h3 : (⟨_, haA⟩ : D.nd.plOm.1 (D.naut.plGw k v)) ∈ IsLocalRing.maximalIdeal _ :=
      ((D.nd.plOm.1 (D.naut.plGw k v)).valuation_lt_one_iff _).2 (by rw [hcast] at h1; exact h1)
    rw [← IsLocalRing.residue_eq_zero_iff] at h3
    rw [h3, map_zero] at hra'
    exact hζ0 hra'.symm
  have hord : orderOf (D.ntypes.tg k v π / π) = D.host.g k - 1 := by
    apply Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hpow)
    rw [← hζ]
    apply orderOf_dvd_of_pow_eq_one
    have h1 : (⟨_, hq⟩ : D.nd.plOm.1 (D.naut.plGw k v)) ^ orderOf (D.ntypes.tg k v π / π) = 1 :=
      Subtype.ext (by simp [pow_orderOf_eq_one])
    rw [← hT, hrq, ← map_pow, ← map_pow, h1, map_one, map_one]
  refine ⟨hN, (n : 𝓞 D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E), π, hu, hgP, hspl.2.1, ?_, ?_, ?_⟩
  · rw [hN]; simpa using hπ
  · rw [hcast]; exact hval
  · rw [hN]; exact hord

end GlobalTheory.TameGenRep

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstTwistCharactersEqLadicCharactersAllReadings

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwInputs.isChars_of_sideB : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ChiTOk D cf → GrpSide D → CharSide D cf → ValLL0 D cf → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∀ (art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om), GlobalTheory.HeckeGal.IsGlobalArtin art → ∀ i b (ρ : GlobalTheory.Triple.Reading D.ntw i b), GlobalTheory.Triple.IsChars cf art ρ := by
  intro _hCh hGAR D cf Rw low Pq S hL eig θ Bs hT hG _hCS hV _hroots art ha i b ρ
  have hchi := GlobalTheory.TwChiGal.firstTwistCharacter_eq_ladic_heckeCharacter D cf Bs.chiD Bs.chi Bs.eta_eq Bs.ringSpec_normalisedCharacter_eq Bs.del_eq hV art ha i b ρ
  refine ⟨hchi, fun j k hk v => ?_⟩
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨hN, u, ϖ, π, hu, hϖ1, hϖ2, hπ, hval, hord⟩ := GlobalTheory.TameGenRep.exists_rep D hG k v
  have hAw : IsPlaceOver (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) := D.nd.plOm.2 _
  have hu0 : (u : D.host.E) ≠ 0 := fun h => hu (by
    rw [show u = 0 from RingOfIntegers.coe_eq_zero_iff.1 h]; exact zero_mem _)
  have hTR : NX.TameRep (D.naut.plGw k v) 1 (D.ntypes.tg k v) u :=
    ⟨_, hAw, D.ntypes.tg_mem k v, ϖ, π, hϖ1, hϖ2, hπ, by simpa using hval⟩
  obtain ⟨c, hc, hcv⟩ := hT k v j u hu0 hTR
  have hxu : IsUnitAt (D.naut.plGw k v) (atFin (D.naut.plGw k v) (Units.mk0 (u : D.host.E) hu0)) := by
    show Valued.v (((u : D.host.E) : (D.naut.plGw k v).adicCompletion D.host.E)) = 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem _).2 hu
  obtain ⟨σ, hσI, hσart, hσval⟩ := GlobalTheory.TameRecip.exists_ine_of_unit hGAR D.host.E D.nd.Om art ha
    (D.naut.plGw k v) _ hAw ϖ hϖ1 hϖ2 π hπ (atFin (D.naut.plGw k v) (Units.mk0 (u : D.host.E) hu0)) u hxu
    (by simp [atFin])
  obtain ⟨n, hn⟩ := hchi j
  have hl := GlobalTheory.Triple.Model.notMem_l (X := D.ntw) hk v
  have e1 := hn.loc (Or.inl hl) hσart.symm
  obtain ⟨h1, -, h3, -, h5⟩ := GlobalTheory.GalChar.inertialOrderFifteenChar_auxiliaryPrime_spec (GlobalTheory.Triple.hframe cf) (l := D.ntw.l i)
  have hdel : (cf.delAt (D.ntw.l i)).UnrAt (D.naut.plGw k v) :=
    h5.unr _ (GlobalTheory.GalChar.notMem_of_ne (D.host.g_prime k) h1 (h3 k).symm (D.naut.plGw_over k v))
  rw [GlobalTheory.Triple.blockChar, GlobalTheory.GalChar.block_loc (cf.isEta.unr _) hxu, GlobalTheory.Triple.muBase] at e1
  change _ = ((cf.mu0 j).loc _ _ : ℂ) * ((cf.delAt (D.ntw.l i)).loc _ _ : ℂ) at e1
  simp only [hdel _ hxu, Units.val_one, mul_one] at e1
  have hg2 := (D.host.g_prime k).two_le
  have hgw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
  have hm : ((normV (D.naut.plGw k v) - 1 : ℕ) : 𝓞 D.host.E) ∉ (D.naut.plGw k v).asIdeal := by
    rw [hN]
    intro h
    apply (D.naut.plGw k v).isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have := (D.naut.plGw k v).asIdeal.sub_mem hgw h
    rwa [Nat.cast_sub (by omega), Nat.cast_one, sub_sub_cancel] at this
  have hI : ∀ τ ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)),
      GlobalTheory.GalChar.inQ ρ.κ (D.ntw.chi1 i (j.1 + 1) b) τ ^ (normV (D.naut.plGw k v) - 1) = 1 := by
    intro τ hτ
    rw [hN, GlobalTheory.GalChar.inQ, MonoidHom.comp_apply, ← map_pow, D.ntw.twistCharacterFamily_tame i (j.1 + 1) b k _ hgw hl _ hAw τ hτ, map_one]
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow (by rw [hN]; omega)] at hπ
    apply hϖ2
    have h0 : (ϖ : D.host.E) = 0 := (map_eq_zero_iff _ (algebraMap D.host.E D.nd.Om).injective).1 hπ.symm
    rw [show ϖ = 0 from RingOfIntegers.coe_eq_zero_iff.1 h0]
    exact zero_mem _
  have hsub : (D.nd.plOm.1 (D.naut.plGw k v)).valuation (σ π / π - D.ntypes.tg k v π / π) < 1 := by
    have e : σ π / π - D.ntypes.tg k v π / π = (σ π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) -
      (D.ntypes.tg k v π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) := by ring
    rw [e]
    exact Valuation.map_sub_lt _ hσval hval
  have e2 := GlobalTheory.TameCharDet.eq_of_tameChar D.host.E D.nd.Om (D.naut.plGw k v) _ hAw _ (D.ntypes.tg_gen k v) _
    (GlobalTheory.GalChar.inQ ρ.κ (D.ntw.chi1 i (j.1 + 1) b)) (hn.cont (D.ntw.twistBaseCoefficientRing_isAdic i) ρ.κ_alg) _ (by omega) hm hI π _
    hπ0 hπ hord σ hσI hsub
  refine ⟨c, hc, ?_⟩
  rw [GlobalTheory.Triple.Reading.toC_apply, ← GlobalTheory.GalChar.inQ_val, ← e2, GlobalTheory.GalChar.inQ_val, e1]
  exact hcv

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstTwistCharactersEqLadicCharactersAllReadingsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.firstTwistCharacters_eq_ladic_characters_allReadings : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ChiTOk D cf → GrpSide D → CharSide D cf → ValLL0 D cf → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∀ (art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om), GlobalTheory.HeckeGal.IsGlobalArtin art → ∀ i b (ρ : GlobalTheory.Triple.Reading D.ntw i b), GlobalTheory.Triple.IsChars cf art ρ := by
  first | exact @GlobalTheory.TwInputs.isChars_of_sideB | exact GlobalTheory.TwInputs.isChars_of_sideB | (intros; apply GlobalTheory.TwInputs.isChars_of_sideB <;> assumption)
end
end
