module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowSetFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
public import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmulMemSpanIntegers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsCAtState
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OfFirstStepLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeOperatorPreservesSupLatticeRealSideStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDefiniteSpacesStandardAndLarge
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFamilyIffRationalHecke
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepSplittingCharactersTameLevelResidue
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ExistsIsHeckeSetting
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemOfListProdMem

section

@[expose] public section

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.SupPowNorm

open Formalism.IndefR.Arith

section Clear

variable {Ks : Type} [Field Ks] [NumberField Ks] {WL : Type} [AddCommGroup WL] [Module Ks WL] [Module (𝓞 Ks) WL]
  [IsScalarTower (𝓞 Ks) Ks WL]

theorem exists_smul_mem_span_int {T : Set WL} {g : WL} (hg : g ∈ Submodule.span Ks T) :
    ∃ d : 𝓞 Ks, d ≠ 0 ∧ d • g ∈ Submodule.span (𝓞 Ks) T := by
  first
  | exact @_root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers
  | exact _root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers
  | (apply _root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers <;> assumption)
  | (intros; apply _root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers ..)

end Clear

section Forms

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
  {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  {G : Type} [Group G] (A : FormsL LL Ks WL W G)

theorem exists_pow_smul_mem_MK (hL : WL →ₗ[LL] WL) (T : Finset WL) (hT : ∀ x ∈ T, x ∈ A.MK)
    (hspan : ∀ x ∈ A.WK, x ∈ Submodule.span Ks (T : Set WL)) (hW : ∀ x ∈ A.WK, hL x ∈ A.WK)
    {N p : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (hsup : ∀ la : HeightOneSpectrum (𝓞 Ks), (p : 𝓞 Ks) ∉ la.asIdeal → ∀ (f : WL) (hf : f ∈ A.WK),
      (∀ y, A.nrm la y ⟨f, hf⟩ ≤ 1) → ∀ y, A.nrm la y ⟨hL f, hW f hf⟩ ≤ 1)
    {t : WL} (ht : t ∈ A.MK) : ∃ n : ℕ, ∀ m, n ≤ m → N ^ m • hL t ∈ A.MK := by
  obtain ⟨htW, htb⟩ := ht
  have hg := hW t htW
  obtain ⟨d, hd, hdg⟩ := exists_smul_mem_span_int (hspan _ hg)
  have hdM : d • hL t ∈ A.MK := (Submodule.span_le.2 fun x hx => hT x hx) hdg
  have hb : ∀ la y, FinitePlace.mk la (algebraMap (𝓞 Ks) Ks d) * A.nrm la y ⟨hL t, hg⟩ ≤ 1 := by
    intro la y
    obtain ⟨h1, h2⟩ := hdM
    have := h2 la y
    have e : (⟨d • hL t, h1⟩ : A.WK) = (algebraMap (𝓞 Ks) Ks d) • ⟨hL t, hg⟩ :=
      Subtype.ext (algebraMap_smul Ks d (hL t)).symm
    rwa [e, A.nrm_smul] at this
  have hfin : {la : HeightOneSpectrum (𝓞 Ks) | la.asIdeal ∣ Ideal.span {(p : 𝓞 Ks)}}.Finite := by
    refine Ideal.finite_factors ?_
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hex : ∀ la : HeightOneSpectrum (𝓞 Ks), (p : 𝓞 Ks) ∈ la.asIdeal →
      ∃ n : ℕ, FinitePlace.mk la (N : Ks) ^ n ≤ FinitePlace.mk la (algebraMap (𝓞 Ks) Ks d) := by
    intro la hla
    have hNla : (N : 𝓞 Ks) ∈ la.asIdeal := by
      obtain ⟨k, rfl⟩ := hpN
      push_cast
      exact la.asIdeal.mul_mem_right _ hla
    have h1 : FinitePlace.mk la (N : Ks) < 1 := by
      rw [FinitePlace.mk_apply]
      have := (FinitePlace.norm_lt_one_iff_mem Ks la (N : 𝓞 Ks)).2 hNla
      simpa using this
    have h2 : 0 < FinitePlace.mk la (algebraMap (𝓞 Ks) Ks d) := FinitePlace.pos_iff.2 (by simpa using hd)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one h2 h1
    exact ⟨n, hn.le⟩
  classical
  choose! nf hnf using hex
  refine ⟨hfin.toFinset.sup nf, fun m hm => ?_⟩
  have hmW : N ^ m • hL t ∈ A.WK := by
    rw [← Nat.cast_smul_eq_nsmul Ks]
    exact A.WK.smul_mem _ hg
  refine ⟨hmW, fun la y => ?_⟩
  have e : (⟨N ^ m • hL t, hmW⟩ : A.WK) = ((N : Ks) ^ m) • ⟨hL t, hg⟩ :=
    Subtype.ext (by rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]; rfl)
  rw [e, A.nrm_smul, map_pow]
  have hN1 : FinitePlace.mk la (N : Ks) ≤ 1 := by
    rw [FinitePlace.mk_apply]
    simpa using FinitePlace.norm_le_one Ks la (N : 𝓞 Ks)
  have hN0 : 0 ≤ FinitePlace.mk la (N : Ks) := by positivity
  have h0 := A.nrm_nonneg la y ⟨hL t, hg⟩
  by_cases hla : (p : 𝓞 Ks) ∈ la.asIdeal
  · have hmem : la ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact hla
    have hle : nf la ≤ m := (Finset.le_sup hmem).trans hm
    calc FinitePlace.mk la (N : Ks) ^ m * A.nrm la y ⟨hL t, hg⟩
        ≤ FinitePlace.mk la (N : Ks) ^ nf la * A.nrm la y ⟨hL t, hg⟩ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hN0 hN1 hle) h0
      _ ≤ FinitePlace.mk la (algebraMap (𝓞 Ks) Ks d) * A.nrm la y ⟨hL t, hg⟩ :=
          mul_le_mul_of_nonneg_right (hnf la hla) h0
      _ ≤ 1 := hb la y
  · have := hsup la hla t htW (htb la) y
    calc FinitePlace.mk la (N : Ks) ^ m * A.nrm la y ⟨hL t, hg⟩ ≤ 1 * 1 :=
          mul_le_mul (pow_le_one₀ hN0 hN1) this h0 zero_le_one
      _ = 1 := one_mul 1

end Forms

section Span

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL]
  {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  {G : Type} [Group G] (A : FormsL LL Ks WL W G)

theorem exists_pow_smul_mem_span (hL : WL →ₗ[LL] WL) (T : Finset WL) (hT : ∀ x ∈ T, x ∈ A.MK)
    (hMK : ∀ x ∈ A.MK, x ∈ Submodule.span (𝓞 Ks) (T : Set WL))
    (hspan : ∀ x ∈ A.WK, x ∈ Submodule.span Ks (T : Set WL)) (hW : ∀ x ∈ A.WK, hL x ∈ A.WK)
    {N p : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (hsup : ∀ la : HeightOneSpectrum (𝓞 Ks), (p : 𝓞 Ks) ∉ la.asIdeal → ∀ (f : WL) (hf : f ∈ A.WK),
      (∀ y, A.nrm la y ⟨f, hf⟩ ≤ 1) → ∀ y, A.nrm la y ⟨hL f, hW f hf⟩ ≤ 1) :
    ∃ n : ℕ, ∀ x ∈ Submodule.span (𝓞 LL) (A.MK : Set WL),
      N ^ n • hL x ∈ Submodule.span (𝓞 LL) (A.MK : Set WL) := by
  classical
  have hex : ∀ t ∈ T, ∃ n : ℕ, ∀ m, n ≤ m → N ^ m • hL t ∈ A.MK := fun t ht =>
    exists_pow_smul_mem_MK A hL T hT hspan hW hp hpN hsup (hT t ht)
  choose! nf hnf using hex
  set n := T.sup nf
  have hks : ∀ (a : Ks) (x : WL), hL (a • x) = a • hL x := fun a x => LinearMap.map_smul_of_tower hL a x
  have h0 : ∀ f ∈ Submodule.span (𝓞 Ks) (T : Set WL), N ^ n • hL f ∈ A.MK := by
    intro f hfs
    induction hfs using Submodule.span_induction with
    | mem t ht => exact hnf t ht n (Finset.le_sup ht)
    | zero => rw [map_zero, smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _), smul_add]; exact add_mem hx hy
    | smul a x _ hx =>
      rw [← algebraMap_smul Ks a x, hks, algebraMap_smul, smul_comm]
      exact A.MK.smul_mem a hx
  have h1 : ∀ f ∈ A.MK, N ^ n • hL f ∈ A.MK := fun f hf => h0 f (hMK f hf)
  refine ⟨n, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem f hf => exact Submodule.subset_span (h1 f hf)
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _), smul_add]; exact add_mem hx hy
  | smul b x _ hx =>
    rw [LinearMap.map_smul_of_tower, smul_comm]
    exact Submodule.smul_mem _ b hx

end Span

section Prime

variable {E : Type} [Field E] [NumberField E]

theorem exists_mem_of_list_prod_mem (P : HeightOneSpectrum (𝓞 E)) :
    ∀ l : List (𝓞 E), l.prod ∈ P.asIdeal → ∃ x ∈ l, x ∈ P.asIdeal := by
  intro l
  simpa only [Multiset.prod_coe, Multiset.mem_coe] using
    (P.isPrime.multiset_prod_mem_iff_exists_mem (l : Multiset (𝓞 E))).mp

theorem exists_prime_dvd_card (P : HeightOneSpectrum (𝓞 E)) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 E) ∈ P.asIdeal ∧ p ∣ Nat.card (𝓞 E ⧸ P.asIdeal) := by
  have e : Nat.card (𝓞 E ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hN : Ideal.absNorm P.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 P.ne_bot
  have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem _
  rw [← Nat.prod_primeFactorsList hN, Nat.cast_list_prod] at hmem
  obtain ⟨x, hx, hxP⟩ := exists_mem_of_list_prod_mem P _ hmem
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  exact ⟨p, Nat.prime_of_mem_primeFactorsList hp, hxP, e ▸ Nat.dvd_of_mem_primeFactorsList hp⟩

theorem prime_eq_of_mem (P : HeightOneSpectrum (𝓞 E)) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpP : (p : 𝓞 E) ∈ P.asIdeal) (hqP : (q : 𝓞 E) ∈ P.asIdeal) : p = q := by
  by_contra hne
  have hco : IsCoprime (p : 𝓞 E) (q : 𝓞 E) := ((Nat.coprime_primes hp hq).2 hne).cast
  obtain ⟨u, v, huv⟩ := hco
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (huv ▸ P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ hpP) (P.asIdeal.mul_mem_left _ hqP)))

end Prime

end GlobalTheory.SupPowNorm
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatHeckeKeepsBall

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.RatHeckeBall

theorem ratHecke_keeps_ball_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → ∀ (hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j)), StabC (SOf x) hL' → HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' → ∀ (j k : ℕ) (Pl : PlE (Dof x).host), 1 ≤ j → j ≤ (Dof x).R.m → IsSplitPl (Dof x).host Pl → Pl ∉ SbD (Dof x) → k ≤ (Dof x).R.r → ∀ la : HeightOneSpectrum (𝓞 (SOf x).Ks), (∀ q : ℕ, q.Prime → (q : 𝓞 (Dof x).host.E) ∈ Pl.asIdeal → (q : 𝓞 (SOf x).Ks) ∉ la.asIdeal) → ∀ (f : (SOf x).WL j) (hf : f ∈ ((SOf x).A j).WK) (hg : hL' j k Pl f ∈ ((SOf x).A j).WK), (∀ y, ((SOf x).A j).nrm la y ⟨f, hf⟩ ≤ 1) → ∀ y, ((SOf x).A j).nrm la y ⟨hL' j k Pl f, hg⟩ ≤ 1 := by
  intro hLL hDec hI hT hRT
  have ev : ∀ {Q : Ctx → Prop}, Ev Q → StepW Start fun K _ _ _ _ => Q K := fun h =>
    Step.of_evG ((evG_of_ev h).imp fun _ _ _ _ _ H _ _ _ _ _ _ _ _ _ => H)
  have hId : StepW Start Start := StepW.of_all fun _ _ _ _ _ _ _ h => h
  refine ((hId.and (ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev)).and (ev GlobalTheory.Mem.StdSize.vstd_size_ev)).trans
    (StepW.of_all fun K B f T w hO _ H => ?_)
  intro P x _ hL' hstab hRd j k v hj1 hj2 hsp hPS hk la hla g hg hhg hball
  obtain ⟨hHo, -⟩ := H.1.2 (w.st x.o.Z) hO
  obtain ⟨hStd, hSize⟩ := H.2 (w.st x.o.Z) hO
  have hfin : Finite (TupU w.I (usedOf w.I T P.Wt)) := by
    have hs : ({τ | τ = (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T P.Wt))).1 ∨ τ ∈ tuOf w.I (usedOf w.I T P.Wt)} :
        Set _).Finite :=
      (Set.finite_singleton _).union (tuOf w.I (usedOf w.I T P.Wt)).finite_toSet
    exact hs.to_subtype
  let X := GlobalTheory.TwInputs.RealSide.ofPins x.m.z.geo x.m.z.pins x.m.intersectionNumber_baseChange x.m.inGeo hfin hHo hStd hSize
  have hS := GlobalTheory.T.heckeOperator_preserves_supLattice_realSide hDec hI hT hRT (Dof x) X (idxOf (Dof x) j)
  have hlow : ∀ p ∈ lowAll (Dof x), p ≠ 0 → ((p : ℕ) : 𝓞 (Dof x).host.E) ∉ v.asIdeal := by
    intro p hp hp0 hm
    apply hPS
    rw [SbD, Set.Finite.mem_toFinset]
    exact ⟨p, hp, hp0, hm⟩
  have hgP : ∀ kk : Fin 2, (((Dof x).host.g kk : ℕ) : 𝓞 (Dof x).host.E) ∉ v.asIdeal := fun kk =>
    hlow _ (by fin_cases kk <;> simp [lowAll]) ((Dof x).host.g_prime kk).ne_zero
  have hso : Bridge.SplitOff v (X.R.Sb : Set (Formalism.L2.DIV.Pl (Dof x).host.E)) := by
    have hAll : X.R.Sb = X.R.Pg := X.char.allPl
    have hPg := X.char.lev.Pg
    refine ⟨(GlobalTheory.HeckeTieCompare.isSplitPl_iff v).1 hsp, fun h => ?_, fun Q hQ h => ?_⟩
    · rw [Finset.mem_coe, hAll] at h
      obtain ⟨kk, hkk⟩ := (hPg v).1 h
      exact hgP kk (GlobalTheory.StepLaw.typePrime_mem_of_div hkk)
    · rw [Finset.mem_coe, hAll] at hQ
      obtain ⟨kk, hkk⟩ := (hPg Q).1 hQ
      have hm := GlobalTheory.StepLaw.typePrime_mem_of_div hkk
      rw [h, Formalism.L2.Col.conjIdeal_asIdeal, Formalism.L2.Col.mem_conjP, map_natCast] at hm
      exact hgP kk hm
  obtain ⟨α, Rc, ha, hR⟩ := GlobalTheory.HeckeSupSt.exists_heckeElt X.char.lev X.char.fam (idxOf (Dof x) j) hso hk
  have hg01 : (((Dof x).host.g 0 * (Dof x).host.g 1 : ℕ) : 𝓞 (Dof x).host.E) ∉ v.asIdeal := by
    intro hm
    rw [Nat.cast_mul] at hm
    rcases v.isPrime.mem_or_mem hm with h | h
    exacts [hgP 0 h, hgP 1 h]
  have hd : GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.IsHkData X.R.toRealDat (idxOf (Dof x) j) v k α Rc := ⟨hso, hg01, hk, ha, hR⟩
  have hkd : HkDat x.m.z.R (SbD (Dof x)) (idxOf (Dof x) j) k v α Rc :=
    ⟨hsp, hPS, hlow 2 (by simp [lowAll, lowPr]) two_ne_zero, hk, ha, hR⟩
  have e : GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.hkC X.R.toRealDat (idxOf (Dof x) j) v k = hkNorm x.m.z.R (idxOf (Dof x) j) k v := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.hkC, hkNorm, inv_pow]
    all_goals rfl
  have hK := hS v k α Rc hd (hL' j k v) (fun y => by rw [e]; exact hRd j k v α Rc hj1 hj2 hkd y)
    (fun y hy => hstab j hj1 hj2 k v y hy) la hla
  exact hK.sup ⟨g, hg⟩ hball
end GlobalTheory.RatHeckeBall
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatHeckeKeepsBallStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hecke_reading_eigenvalue_place_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → ∀ (hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j)), StabC (SOf x) hL' → HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' → ∀ (j k : ℕ) (Pl : PlE (Dof x).host), 1 ≤ j → j ≤ (Dof x).R.m → IsSplitPl (Dof x).host Pl → Pl ∉ SbD (Dof x) → k ≤ (Dof x).R.r → ∀ la : HeightOneSpectrum (𝓞 (SOf x).Ks), (∀ q : ℕ, q.Prime → (q : 𝓞 (Dof x).host.E) ∈ Pl.asIdeal → (q : 𝓞 (SOf x).Ks) ∉ la.asIdeal) → ∀ (f : (SOf x).WL j) (hf : f ∈ ((SOf x).A j).WK) (hg : hL' j k Pl f ∈ ((SOf x).A j).WK), (∀ y, ((SOf x).A j).nrm la y ⟨f, hf⟩ ≤ 1) → ∀ y, ((SOf x).A j).nrm la y ⟨hL' j k Pl f, hg⟩ ≤ 1 := by
  first | exact @_root_.GlobalTheory.RatHeckeBall.ratHecke_keeps_ball_alt | exact _root_.GlobalTheory.RatHeckeBall.ratHecke_keeps_ball_alt | (intros; apply _root_.GlobalTheory.RatHeckeBall.ratHecke_keeps_ball_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IntCAtState

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.RatSide

theorem intC_of_lvlPsi_stabC_heckeRd : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → ∀ (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((Dof x).host.g kk)) →* (↥(Dof x).LL0)ˣ) (hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j)), LvlPsi x.m.z.R x.m.z.F x.m.z.cG θ → StabC (SOf x) hL' → HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' → IntC (SOf x) (SbD (Dof x)) θ hL' := by
  intro hL hDec hI hT hRT
  refine ((_root_.GlobalTheory.T.hecke_reading_eigenvalue_place_alt hL hDec hI hT hRT).and (_root_.GlobalTheory.HeightCounting.RatSide.formsC_at_state_alt hL)).trans
    (StepW.of_all fun K B f T w _ _ H P x hA θ hL' _ hstab hrd => ?_)
  obtain ⟨hB, hF⟩ := H
  intro j k Pl hj1 hj2 hsp hnot hk
  obtain ⟨-, -, Tf, hTf, hMK, hspan⟩ := hF P x hA j hj1 hj2
  obtain ⟨p, hp, hpP, hpN⟩ := GlobalTheory.SupPowNorm.exists_prime_dvd_card Pl
  have hW : ∀ y ∈ ((SOf x).A j).WK, hL' j k Pl y ∈ ((SOf x).A j).WK := fun y hy => hstab j hj1 hj2 k Pl y hy
  obtain ⟨n, hn⟩ := GlobalTheory.SupPowNorm.exists_pow_smul_mem_span ((SOf x).A j) (hL' j k Pl) Tf hTf
    (fun y hy => (hMK y hy).2) hspan hW hp hpN fun la hla g hg hb y =>
      hB P x hA hL' hstab hrd j k Pl hj1 hj2 hsp hnot hk la
        (fun q hq hqP => by rw [GlobalTheory.SupPowNorm.prime_eq_of_mem Pl hq hp hqP hpP]; exact hla) g hg (hW g hg) hb y
  exact ⟨n, fun y hy _ => hn y hy⟩
end GlobalTheory.HeightCounting.RatSide
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IntCAtStateStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.intC_state_of_lvlPsi_stabC_heckeRd :
    ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists,
      GlobalTheory.Published.CuspRapidDecay →
      GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt →
      GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform →
      GlobalTheory.HeckeSupSt.HeckeReadTie →
      StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P),
        _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x →
        ∀ (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((Dof x).host.g kk)) →* (↥(Dof x).LL0)ˣ)
          (hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j)),
          LvlPsi x.m.z.R x.m.z.F x.m.z.cG θ → StabC (SOf x) hL' →
          HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' →
          IntC (SOf x) (SbD (Dof x)) θ hL' :=
  _root_.GlobalTheory.HeightCounting.RatSide.intC_of_lvlPsi_stabC_heckeRd
end
end
end
