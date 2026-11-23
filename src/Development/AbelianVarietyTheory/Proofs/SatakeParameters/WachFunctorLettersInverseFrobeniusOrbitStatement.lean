module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceOverPrimeOfPadicAlgClEmbeddingStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankLocalFieldEqCardDecompositionGroupStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicAlgClFiniteDenseEqAdjoinStatement
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Decomp
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.KrullDimension.PID
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueEmbeddingReadsGaloisElementStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueEmbeddingRestrictsToWachLetterUnramiStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobGIsArithFrobAndSignStatement
public import Formalism.LocalRingCardinality.DataDIV
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HostFieldPadicEmbeddingMemMaxUnramifiedStatement
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Mathlib.RingTheory.Valuation.Integral
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Mathlib.RingTheory.Ideal.Int
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompletionEmbeddingsSingleFrobeniusOrbit

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory.LocalFrobeniusOrbit

theorem norm_algHom_eq {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : K →ₐ[ℚ_[l]] PadicAlgCl l) (x : K) : ‖σ x‖ = ‖(x : PadicAlgCl l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm,
    minpoly.algHom_eq σ σ.injective, ← minpoly.algHom_eq K.val K.val.injective]
  rfl

theorem exists_aut_comp {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] {l : ℕ} [Fact l.Prime]
    (c ρ : E →+* PadicAlgCl l) : ∃ g : E ≃ₐ[ℚ] E, ∀ x, ρ x = c (g x) := by
  let Φ : (E ≃ₐ[ℚ] E) → (E →ₐ[ℚ] PadicAlgCl l) := fun g => c.toRatAlgHom.comp g.toAlgHom
  have hinj : Function.Injective Φ := by
    intro g h hgh
    ext x
    have := congrArg (fun f : E →ₐ[ℚ] PadicAlgCl l => f x) hgh
    exact c.injective this
  have hcard : Nat.card (E →ₐ[ℚ] PadicAlgCl l) ≤ Nat.card (E ≃ₐ[ℚ] E) := by
    rw [Nat.card_eq_fintype_card, AlgHom.card, IsGalois.card_aut_eq_finrank]
  have hbij := hinj.bijective_of_nat_card_le hcard
  obtain ⟨g, hg⟩ := hbij.2 ρ.toRatAlgHom
  exact ⟨g, fun x => (congrArg (fun f : E →ₐ[ℚ] PadicAlgCl l => f x) hg).symm⟩

theorem embeddings_orbit : ∀ {R : Ranks} (H : Host R) (l : ℕ) [Fact l.Prime], l ∉ H.small → l ≠ H.q → l ≠ H.d → ∀ (c : H.E →+* PadicAlgCl l) (K : Loc.FinExt l) (hc : ∀ x, c x ∈ K.1), (K.1 : Set (PadicAlgCl l)) ⊆ closure (Set.range c) → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(l : ℤ)})] (s : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ s P → Module.finrank ℚ_[l] ↥K.1 = orderOf (H.galE s) ∧ ∀ τ : ↥K.1 →ₐ[ℚ_[l]] Loc.Om l, ∃! i : ZMod (orderOf (H.galE s)), ∀ x : H.E, τ ⟨c x, hc x⟩ = c ((s ^ i.val) x) := by
  intro R H l _ h2 hq hd c K hc hcl P _ _ s hs
  haveI hG : IsGalois ℚ H.E := H.hostE_isGalois
  have hN0 : ¬ l ∣ H.condN := by
    rw [H.dvd_condN_iff_small Fact.out]; tauto
  have hF := H.der.frob l hN0
  have hco : Nat.Coprime l H.condN := (Fact.out : l.Prime).coprime_iff_not_dvd.2 hN0
  obtain ⟨v, hvl, hv⟩ := GlobalTheory.T.exists_place_over_prime_of_padicAlgCl_embedding l H.E c
  have hp : l.Prime := Fact.out
  have hpz : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI := v.isPrime
  haveI hvo : v.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) :=
    (Ideal.liesOver_span_iff v.isPrime.ne_top hpz).mpr (by simpa [placesOver] using hvl)
  have hsv : IsArithFrobAt ℤ s v.asIdeal := (H.frob_iff l hco v.asIdeal s).2 ((H.frob_iff l hco P s).1 hs)
  have hstab : MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) v.asIdeal = Subgroup.zpowers s := by
    refine le_antisymm (fun σ hσ => ?_) (Subgroup.zpowers_le.2 hsv.mem_stabilizer)
    obtain ⟨k, ρ, hρ, rfl⟩ := Formalism.FrobeniusOrbits.Decomp.stab_eq_inertia_mul l v.asIdeal s σ hsv hσ
    rw [((hF v.asIdeal).2.2.2 ρ).1 hρ, one_mul]
    exact Subgroup.npow_mem_zpowers s k
  have hord : orderOf s = orderOf (H.galE s) :=
    (H.gal.orderOf_eq s).symm
  set N := orderOf (H.galE s) with hN
  have hNpos : 0 < N := hord ▸ orderOf_pos s
  haveI : NeZero N := ⟨hNpos.ne'⟩
  refine ⟨?_, ?_⟩
  · have hK : K.1 = IntermediateField.adjoin ℚ_[l] (Set.range c) := GlobalTheory.T.padicAlgCl_finite_dense_eq_adjoin' l H.E c K.1 hc K.2 hcl
    have hdeg := GlobalTheory.T.finrank_local_field_eq_card_decomposition_group l H.E c v hv
    rw [← hord, ← Nat.card_zpowers, ← hstab, ← hdeg, hK]
  · intro τ
    let ρ : H.E →+* PadicAlgCl l := (τ : ↥K.1 →+* PadicAlgCl l).comp (c.codRestrict K.1 hc)
    obtain ⟨g, hg⟩ := exists_aut_comp c ρ
    have hρx : ∀ x, ρ x = τ ⟨c x, hc x⟩ := fun x => rfl
    have hgs : g ∈ Subgroup.zpowers s := by
      rw [← hstab]
      refine Formalism.FrobeniusOrbits.Decomp.mem_stab_of g v.asIdeal (fun z => ?_)
      rw [hv, hv]
      have h1 : c ((g • z : 𝓞 H.E) : H.E) = τ ⟨c z, hc z⟩ := by
        rw [← hρx, hg]; rfl
      rw [h1, norm_algHom_eq]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hgs
    have hpow : ∀ j : ZMod N, s ^ j.val = s ^ ((j.val : ℤ)) := fun j => (zpow_natCast s j.val).symm
    refine ⟨(k : ZMod N), fun x => ?_, fun j hj => ?_⟩
    · rw [← hρx, hg, hpow, ZMod.val_intCast, ← hord, zpow_mod_orderOf, hk]
    · have hgj : g = s ^ j.val := by
        refine AlgEquiv.ext fun x => c.injective ?_
        rw [← hg, hρx, hj]
      apply ZMod.val_injective
      have h3 : s ^ j.val = s ^ (k : ZMod N).val := by
        rw [← hgj, hpow, ZMod.val_intCast, ← hord, zpow_mod_orderOf, hk]
      have h4 := pow_inj_mod.1 h3
      rw [hord, Nat.mod_eq_of_lt (ZMod.val_lt j), Nat.mod_eq_of_lt (ZMod.val_lt _)] at h4
      exact h4

end GlobalTheory.LocalFrobeniusOrbit
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompletionEmbeddingsSingleFrobeniusOrbitStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

theorem _root_.GlobalTheory.T.completion_embeddings_single_frobenius_orbit : ∀ {R : Ranks} (H : Host R) (l : ℕ) [Fact l.Prime], l ∉ H.small → l ≠ H.q → l ≠ H.d → ∀ (c : H.E →+* PadicAlgCl l) (K : Loc.FinExt l) (hc : ∀ x, c x ∈ K.1), (K.1 : Set (PadicAlgCl l)) ⊆ closure (Set.range c) → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(l : ℤ)})] (s : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ s P → Module.finrank ℚ_[l] ↥K.1 = orderOf (H.galE s) ∧ ∀ τ : ↥K.1 →ₐ[ℚ_[l]] Loc.Om l, ∃! i : ZMod (orderOf (H.galE s)), ∀ x : H.E, τ ⟨c x, hc x⟩ = c ((s ^ i.val) x) := by
  first | exact @GlobalTheory.LocalFrobeniusOrbit.embeddings_orbit | exact GlobalTheory.LocalFrobeniusOrbit.embeddings_orbit | (intros; apply GlobalTheory.LocalFrobeniusOrbit.embeddings_orbit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodDatumFrobeniusRestrictHostField

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.FrobPeriod

theorem norm_int_le_one {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (c : E →+* PadicAlgCl l) (x : 𝓞 E) : ‖c (x : E)‖ ≤ 1 := by
  have hx : IsIntegral ℤ (c (x : E)) := map_isIntegral_int c x.isIntegral_coe
  have h : c (x : E) ∈ (NormedField.valuation (K := PadicAlgCl l)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := PadicAlgCl l))).mem_of_integral
      hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem exists_comp_of_normal {E L : Type} [Field E] [Field L] [CharZero E] [CharZero L]
    [Normal ℚ E] (φ ψ : E →+* L) : ∃ g : E ≃ₐ[ℚ] E, ∀ x, ψ x = φ (g x) := by
  letI : Algebra E L := φ.toAlgebra
  haveI : IsScalarTower ℚ E L := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  refine ⟨AlgHom.restrictNormal' ψ.toRatAlgHom E, fun x => ?_⟩
  exact (AlgHom.restrictNormal_commutes ψ.toRatAlgHom E x).symm

theorem liesOver_of_mem {E : Type} [Field E] [NumberField E] (l : ℕ) [hl : Fact l.Prime]
    (v : HeightOneSpectrum (𝓞 E)) (h : ((l : ℕ) : 𝓞 E) ∈ v.asIdeal) :
    v.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) := by
  constructor
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl.out).irreducible
  refine hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_
  rw [Ideal.span_le, Set.singleton_subset_iff]
  change (algebraMap ℤ (𝓞 E) (l : ℤ)) ∈ v.asIdeal
  simpa using h

theorem card_quot_under {E : Type} [Field E] [NumberField E] (l : ℕ) [hl : Fact l.Prime]
    (Q : Ideal (𝓞 E)) [h : Q.LiesOver (Ideal.span {(l : ℤ)})] :
    Nat.card (ℤ ⧸ Q.under ℤ) = l := by
  rw [← h.over, Nat.card_congr (Int.quotientSpanNatEquivZMod l).toEquiv, Nat.card_zmod]

end GlobalTheory.FrobPeriod


open GlobalTheory.FrobPeriod in
theorem GlobalTheory.FrobPeriod.periodFrob_restrict : ∀ (D : D7) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (c : D.host.E →+* ↥K.1), l ∉ D.host.small → l ≠ D.host.q → l ≠ D.host.d → ∀ (x : D.host.E) (y : ↥(K0 K)), algebraMap ↥(K0 K) ↥K.1 y = c x → algebraMap ↥(K0 K) ↥K.1 ((P.PD K).σ y) = c (D.host.sigmaOf (DV.frobG D l) x) := by
  intro D l _ P K c h2 hq hd x y hy
  have hlN : ¬ l ∣ D.host.condN := fun h => by
    rcases (D.host.dvd_condN_iff_small Fact.out).1 h with h | h | h
    exacts [h2 h, hq h, hd h]
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  let c' : D.host.E →+* PadicAlgCl l := K.1.val.toRingHom.comp c
  have hK : ∀ z, c' z ∈ K0 K := fun z =>
    IntermediateField.mem_inf.2 ⟨(c z).2, GlobalTheory.T.hostField_padicEmbedding_mem_maxUnramified D.host l h2 hq hd c' z⟩
  let c0 : D.host.E →+* ↥(K0 K) := c'.codRestrict (K0 K) hK
  have hc0 : ∀ z, ((c0 z : ↥(K0 K)) : PadicAlgCl l) = c' z := fun z => rfl
  have hyx : y = c0 x := Subtype.ext (congrArg (fun t : ↥K.1 => (t : PadicAlgCl l)) hy)
  let σ0 := (P.PD K).σ
  obtain ⟨g, hg⟩ := exists_comp_of_normal c0 ((σ0 : ↥(K0 K) →+* ↥(K0 K)).comp c0)
  obtain ⟨v, hvl, hv⟩ := GlobalTheory.T.exists_place_over_prime_of_padicAlgCl_embedding l D.host.E c'
  haveI := liesOver_of_mem l v hvl
  have hgl : ∀ z : 𝓞 D.host.E, g • z - z ^ l ∈ v.asIdeal := fun z => by
    refine (hv _).2 ?_
    have h := P.PD_σ K (c0 z) (by rw [hc0]; exact norm_int_le_one c' z)
    have e : ((g • z - z ^ l : 𝓞 D.host.E) : D.host.E) = g (z : D.host.E) - (z : D.host.E) ^ l := by
      push_cast
      rfl
    rw [e, map_sub, map_pow, ← hc0, ← hc0, ← hg]
    exact h
  set F := D.host.sigmaOf (DV.frobG D l) with hFdef
  have hF : ∀ z : 𝓞 D.host.E, F • z - z ^ l ∈ v.asIdeal := fun z => by
    have h := (GlobalTheory.T.frobG_isArithFrobAt_and_sign_eq_jacobiSym D l h2 hq hd).1 v.asIdeal z
    rw [card_quot_under l v.asIdeal] at h
    exact h
  have hin := (D.host.der.frob l hlN v.asIdeal).2.2.2
  have hgF : g * F⁻¹ = 1 := by
    refine (hin _).1 fun z => ?_
    have h := v.asIdeal.sub_mem (hgl (F⁻¹ • z)) (hF (F⁻¹ • z))
    have e : (g * F⁻¹) • z - z = g • F⁻¹ • z - (F⁻¹ • z) ^ l - (F • F⁻¹ • z - (F⁻¹ • z) ^ l) := by
      rw [mul_smul, smul_inv_smul]
      ring
    rw [e]
    exact h
  have hgF' : g = F := by simpa using mul_inv_eq_one.1 hgF
  subst hyx
  apply Subtype.ext
  change (((σ0 (c0 x) : ↥(K0 K)) : PadicAlgCl l)) = c' (F x)
  have := hg x
  simp only [RingHom.comp_apply] at this
  rw [show (σ0 (c0 x)) = c0 (g x) from this, hc0, hgF']
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodDatumFrobeniusRestrictHostFieldStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.periodDatum_frobenius_restrict_hostField : ∀ (D : D7) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (c : D.host.E →+* ↥K.1), l ∉ D.host.small → l ≠ D.host.q → l ≠ D.host.d → ∀ (x : D.host.E) (y : ↥(K0 K)), algebraMap ↥(K0 K) ↥K.1 y = c x → algebraMap ↥(K0 K) ↥K.1 ((P.PD K).σ y) = c (D.host.sigmaOf (DV.frobG D l) x) := by
  first | exact @GlobalTheory.FrobPeriod.periodFrob_restrict | exact GlobalTheory.FrobPeriod.periodFrob_restrict | (intros; apply GlobalTheory.FrobPeriod.periodFrob_restrict <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.WachFunctorLettersInverseFrobeniusOrbit

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem reads_orbit_invFrob : ∀ (D : D7) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL) (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1), l ∉ D.host.small → l ≠ D.host.q → l ≠ D.host.d → (K.1 : Set (Om l)) ⊆ closure (Set.range fun x => ((c x : ↥K.1) : Om l)) → K.1 ≤ MaximalUnramifiedExtension l → ∃ g : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → D.R.GG, IsOrbit g (DV.frobG D l)⁻¹ ∧ ∀ τ a, Over W τ a → Reads D.host c κ τ (g a) := by
  intro D l _ P K LL W c κ h2 hq hd hcl hK
  set φ := DV.frobG D l with hφ
  set n := Module.finrank ℚ_[l] ↥(K0 K) with hn
  have hτ := fun a => GlobalTheory.T.existsUnique_embeddingRestrictsToWachLetter_unramified P K LL W hK a
  have hg := fun τ => GlobalTheory.T.existsUnique_embeddingReadsGaloisElement D.host K LL c κ τ
  let τa : ZMod n → (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := fun a => (hτ a).exists.choose
  have hover : ∀ a, Over W (τa a) a := fun a => (hτ a).exists.choose_spec
  let g : ZMod n → D.R.GG := fun a => (hg (τa a)).exists.choose
  have hread : ∀ a, Reads D.host c κ (τa a) (g a) := fun a => (hg (τa a)).exists.choose_spec
  have smul : ∀ u v : D.R.GG, D.host.sigmaOf (u * v) = D.host.sigmaOf u * D.host.sigmaOf v :=
    fun u v => map_mul (D.host.gal).symm u v
  have hK0 : K0 K = K.1 := inf_eq_left.mpr hK

  have step : ∀ a, g (a + 1) = g a * φ⁻¹ := by
    intro a
    refine (hg (τa (a + 1))).unique (hread (a + 1)) ?_
    intro z
    set x := D.host.sigmaOf φ⁻¹ z with hx
    have hz : D.host.sigmaOf φ x = z := by
      rw [hx, ← AlgEquiv.mul_apply, ← smul, mul_inv_cancel]
      show (D.host.gal).symm 1 z = z
      rw [map_one]; rfl
    let y : ↥(K0 K) := ⟨((c x : ↥K.1) : Om l), ⟨(c x).2, hK (c x).2⟩⟩
    have hy : algebraMap ↥(K0 K) ↥K.1 y = c x := Subtype.ext rfl
    have hσ := GlobalTheory.T.periodDatum_frobenius_restrict_hostField D P K c h2 hq hd x y hy
    have ov : ∀ b (t : ↥(K0 K)), τa b (algebraMap ↥(K0 K) ↥K.1 t) = W.emb b t := by
      intro b t
      have := congrArg (fun f => f t) (hover b)
      simpa using this
    have hemb : W.emb (a + 1) ((P.PD K).σ y) = W.emb a y := by
      have := congrArg (fun f => f y) (W.emb_σ a)
      simpa using this
    calc τa (a + 1) (c z) = τa (a + 1) (c (D.host.sigmaOf φ x)) := by rw [hz]
      _ = τa (a + 1) (algebraMap ↥(K0 K) ↥K.1 ((P.PD K).σ y)) := by rw [hσ]
      _ = W.emb (a + 1) ((P.PD K).σ y) := ov _ _
      _ = W.emb a y := hemb
      _ = τa a (algebraMap ↥(K0 K) ↥K.1 y) := (ov _ _).symm
      _ = τa a (c x) := by rw [hy]
      _ = κ (D.host.sigmaOf (g a) x) := hread a x
      _ = κ (D.host.sigmaOf (g a * φ⁻¹) z) := by rw [smul, AlgEquiv.mul_apply]

  have hfr : n = Module.finrank ℚ_[l] ↥K.1 := by
    rw [hn]; exact (IntermediateField.equivOfEq hK0).toLinearEquiv.finrank_eq
  have hlen : n = orderOf φ⁻¹ := by
    rw [orderOf_inv]
    obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
      (Ideal.span {(l : ℤ)}) (⊥ : Ideal (𝓞 D.host.E)) (by
        intro x hx
        simp only [Ideal.mem_comap, Ideal.mem_bot] at hx
        have : x = 0 := (algebraMap ℤ (𝓞 D.host.E)).injective_int (by simpa using hx)
        rw [this]; exact Ideal.zero_mem _)
    have := hQ
    have : Q.LiesOver (Ideal.span {(l : ℤ)}) := ⟨hQc.symm⟩
    have hfrob := (GlobalTheory.T.frobG_isArithFrobAt_and_sign_eq_jacobiSym D l h2 hq hd).1 Q
    let c' : D.host.E →+* PadicAlgCl l := (K.1.val : ↥K.1 →ₐ[ℚ_[l]] Om l).toRingHom.comp c
    have hc' : ∀ x, c' x ∈ K.1 := fun x => (c x).2
    have hcl' : (K.1 : Set (PadicAlgCl l)) ⊆ closure (Set.range c') := hcl
    have := (GlobalTheory.T.completion_embeddings_single_frobenius_orbit D.host l h2 hq hd c' K hc' hcl' Q (D.host.sigmaOf φ) hfrob).1
    have hφg : D.host.galE (D.host.sigmaOf φ) = φ :=
      (D.host.gal).apply_symm_apply φ
    rw [hfr, this, hφg]
  have hpos : 0 < n := by
    rw [hfr]
    have := K.2
    exact Module.finrank_pos
  have : NeZero n := ⟨hpos.ne'⟩
  refine ⟨g, ⟨hlen, ?_⟩, ?_⟩
  · have hk : ∀ k : ℕ, g (k : ZMod n) = g 0 * φ⁻¹ ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Nat.cast_succ, step, ih]
        exact (mul_assoc _ _ _).trans (congrArg _ (pow_succ φ⁻¹ k).symm)
    intro a
    have := hk a.val
    rwa [ZMod.natCast_zmod_val] at this
  · intro τ a h
    have : τ = τa a := (hτ a).unique h (hover a)
    subst this
    exact hread a

end GlobalTheory.HTW.Rec
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.WachFunctorLettersInverseFrobeniusOrbitStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.wachFunctor_letters_inverseFrobenius_orbit : ∀ (D : D7) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL) (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1), l ∉ D.host.small → l ≠ D.host.q → l ≠ D.host.d → (K.1 : Set (Om l)) ⊆ closure (Set.range fun x => ((c x : ↥K.1) : Om l)) → K.1 ≤ MaximalUnramifiedExtension l → ∃ g : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → D.R.GG, IsOrbit g (DV.frobG D l)⁻¹ ∧ ∀ τ a, Over W τ a → Reads D.host c κ τ (g a) := by
  first | exact @GlobalTheory.HTW.Rec.reads_orbit_invFrob | exact GlobalTheory.HTW.Rec.reads_orbit_invFrob | (intros; apply GlobalTheory.HTW.Rec.reads_orbit_invFrob <;> assumption)
end
end
