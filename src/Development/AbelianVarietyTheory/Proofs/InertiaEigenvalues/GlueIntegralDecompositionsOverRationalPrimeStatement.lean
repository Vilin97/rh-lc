module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelFormCompatBaseEmbedding
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGoodOfBddAll
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalSectionBoundedNonzeroMultiple
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCuspFormsAllEmbeddingsOfInclusionReadingStatement
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.ProjectiveLattices.ModelAt
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPartitionOneIntegralAtPlaces

section

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem exists_partition_one_integral_at_places (L : Type) [Field L] [NumberField L]
    (S : Finset (HeightOneSpectrum (𝓞 L))) (hS : S.Nonempty) (Y : S → Finset L)
    (hY : ∀ la, ∀ y ∈ Y la, la.1.valuation L y ≤ 1) :
    ∃ e : S → L, ∑ la, e la = 1 ∧
      ∀ la, ∀ y ∈ Y la, ∀ la' ∈ S, la'.valuation L (e la * y) ≤ 1 := by
  classical
  have hb : ∀ (_la : S) (y : L) (la' : HeightOneSpectrum (𝓞 L)),
      ∃ n : ℕ, WithZero.exp (-(n : ℤ)) * la'.valuation L y ≤ 1 := by
    intro _ y la'
    by_cases hy : la'.valuation L y = 0
    · exact ⟨0, by simp [hy]⟩
    · obtain ⟨m, hm⟩ : ∃ m : ℤ, WithZero.exp m = la'.valuation L y := ⟨_, WithZero.exp_log hy⟩
      refine ⟨m.toNat, ?_⟩
      rw [← hm, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
  choose n hn using hb
  let N : ℕ := ∑ la : S, ∑ y ∈ Y la, ∑ la' ∈ S, n la y la'
  have hN : ∀ la, ∀ y ∈ Y la, ∀ la' ∈ S, n la y la' ≤ N := by
    intro la y hy la' hla'
    calc n la y la' ≤ ∑ la'' ∈ S, n la y la'' :=
          Finset.single_le_sum (f := fun la'' => n la y la'') (fun _ _ => Nat.zero_le _) hla'
      _ ≤ ∑ y' ∈ Y la, ∑ la'' ∈ S, n la y' la'' :=
          Finset.single_le_sum (f := fun y' => ∑ la'' ∈ S, n la y' la'') (fun _ _ => Nat.zero_le _) hy
      _ ≤ N := Finset.single_le_sum (f := fun la => ∑ y' ∈ Y la, ∑ la'' ∈ S, n la y' la'')
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ la)
  let J : S → Ideal (𝓞 L) := fun la => ∏ la' ∈ S.erase la.1, la'.asIdeal ^ N
  have htop : ⨆ la ∈ (Finset.univ : Finset S), J la = ⊤ := by
    by_contra h
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
    have hJM : ∀ la : S, J la ≤ M := fun la =>
      le_trans (le_iSup₂_of_le (f := fun la (_ : la ∈ (Finset.univ : Finset S)) => J la)
        la (Finset.mem_univ _) le_rfl) hle
    obtain ⟨la0, hla0⟩ := hS
    obtain ⟨la1, hla1, h1⟩ := (Ideal.IsPrime.prod_le hM.isPrime).1 (hJM ⟨la0, hla0⟩)
    have hle1 : la1.asIdeal ≤ M := hM.isPrime.le_of_pow_le h1
    have heq : la1.asIdeal = M := la1.isMaximal.eq_of_le hM.ne_top hle1
    have hla1S : la1 ∈ S := Finset.mem_of_mem_erase hla1
    obtain ⟨la2, hla2, h2⟩ := (Ideal.IsPrime.prod_le hM.isPrime).1 (hJM ⟨la1, hla1S⟩)
    have hle2 : la2.asIdeal ≤ la1.asIdeal := heq ▸ hM.isPrime.le_of_pow_le h2
    have h22 : la2.asIdeal = la1.asIdeal := la2.isMaximal.eq_of_le la1.isPrime.ne_top hle2
    exact (Finset.ne_of_mem_erase hla2) (HeightOneSpectrum.ext h22)
  have h1 : (1 : 𝓞 L) ∈ ⨆ la ∈ (Finset.univ : Finset S), J la := htop ▸ Submodule.mem_top
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ _).1 h1
  refine ⟨fun la => ((μ la : 𝓞 L) : L), ?_, ?_⟩
  · have := congrArg (fun x : 𝓞 L => (x : L)) hμ
    simpa using this
  · intro la y hy la' hla'
    rw [map_mul]
    by_cases h : la' = la.1
    · subst h
      calc la.1.valuation L ((μ la : 𝓞 L) : L) * la.1.valuation L y ≤ 1 * 1 :=
            mul_le_mul' (HeightOneSpectrum.valuation_le_one _ _) (hY la y hy)
        _ = 1 := one_mul 1
    · have hmem : (μ la : 𝓞 L) ∈ la'.asIdeal ^ N := by
        have hm : (μ la : 𝓞 L) ∈ J la := (μ la).2
        have hs : la' ∈ S.erase la.1 := Finset.mem_erase.2 ⟨h, hla'⟩
        have : J la ≤ la'.asIdeal ^ N := by
          show ∏ la'' ∈ S.erase la.1, la''.asIdeal ^ N ≤ _
          rw [← Finset.mul_prod_erase _ _ hs]
          exact le_trans Ideal.mul_le_inf inf_le_left
        exact this hm
      have hv : la'.valuation L ((μ la : 𝓞 L) : L) ≤ WithZero.exp (-(N : ℤ)) := by
        rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_dvd,
          Ideal.dvd_span_singleton]
        exact hmem
      calc la'.valuation L ((μ la : 𝓞 L) : L) * la'.valuation L y
          ≤ WithZero.exp (-(N : ℤ)) * la'.valuation L y := mul_le_mul' hv le_rfl
        _ ≤ WithZero.exp (-(n la y la' : ℤ)) * la'.valuation L y := by
            refine mul_le_mul' ?_ le_rfl
            rw [WithZero.exp_le_exp]
            have := hN la y hy la' hla'
            omega
        _ ≤ 1 := hn la y la'

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitScalarSmulCoreIntegralAdelicFormPlaces

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ScaleInt

theorem exists_prime_mem {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 K) ∈ la.asIdeal := by
  have : Finite (𝓞 K ⧸ la.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot la.asIdeal la.ne_bot
  have : la.asIdeal.IsMaximal := la.isMaximal
  let _ : Field (𝓞 K ⧸ la.asIdeal) := Ideal.Quotient.field _
  refine ⟨ringChar (𝓞 K ⧸ la.asIdeal), CharP.char_is_prime (𝓞 K ⧸ la.asIdeal) _, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem exists_avoid {K : Type} [Field K] [NumberField K] (q : Ideal (𝓞 K)) (hq : q.IsPrime)
    (s : Finset (HeightOneSpectrum (𝓞 K))) (hs : ∀ p ∈ s, p.asIdeal ≠ q) (N : HeightOneSpectrum (𝓞 K) → ℕ) :
    ∃ t : 𝓞 K, t ∉ q ∧ ∀ p ∈ s, t ∈ p.asIdeal ^ N p := by
  have hle : ¬ (s.prod fun p => p.asIdeal ^ N p) ≤ q := by
    rw [hq.prod_le]
    rintro ⟨p, hp, hpq⟩
    rcases Nat.eq_zero_or_pos (N p) with h0 | hpos
    · rw [h0, pow_zero, Ideal.one_eq_top, top_le_iff] at hpq
      exact hq.ne_top hpq
    · have h1 : p.asIdeal ≤ q := hq.le_of_pow_le hpq
      exact hs p hp (p.isMaximal.eq_of_le hq.ne_top h1)
  obtain ⟨t, ht, htq⟩ := SetLike.not_le_iff_exists.1 hle
  exact ⟨t, htq, fun p hp => (Ideal.prod_le_inf.trans (Finset.inf_le hp)) ht⟩

theorem le_vLa_of_mem {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)) {t : 𝓞 K} (n : ℕ)
    (ht : t ∈ p.asIdeal ^ n) (ht0 : t ≠ 0) : (n : ℤ) ≤ vLa p (t : K) := by
  have h := (p.intValuation_le_pow_iff_mem t n).2 ht
  have hne : p.intValuation t ≠ 0 := HeightOneSpectrum.intValuation_ne_zero p t ht0
  have e : p.valuation K (t : K) = p.intValuation t := p.valuation_of_algebraMap t
  unfold vLa
  rw [e]
  have := (WithZero.log_le_log hne (by simp)).2 h
  simp at this
  omega

theorem vLa_eq_zero_of_not_mem {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)) {t : 𝓞 K}
    (ht : t ∉ p.asIdeal) : vLa p (t : K) = 0 := by
  unfold vLa
  rw [(HeightOneSpectrum.valuation_eq_one_iff_notMem p).mpr ht, WithZero.log_one, neg_zero]

end GlobalTheory.ScaleInt

namespace GlobalTheory.ScaleInt



theorem smul_mem_baseInt : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ (i : Fin D.R.m) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)), κ.LastPos →
    ∀ (q : Ideal (𝓞 T.Q.c.F)), q.IsPrime → ∀ (P : Set (HeightOneSpectrum (𝓞 T.Q.c.F))), P.Finite →
    ∀ ψ ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA κ) κ.n {p | p.asIdeal = q},
      ∃ t : 𝓞 T.Q.c.F, t ∉ q ∧ T.σ₀ (t : T.Q.c.F) • ψ ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA κ) κ.n P := by
  intro D T hT i κ hκ q hq P hP ψ hψ
  obtain ⟨f, ⟨hfs, hfh, hfv⟩, rfl⟩ := hψ
  have hj : InR D ((i : ℕ) + 1) := inR i
  have hcusp : f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.U ((i : ℕ) + 1)) (wtA κ) κ.n := GlobalTheory.T.mem_cuspForms_allEmbeddings_of_inclusion_reading D T hT _ hj κ hκ f hfs hfh
  have hbd : ∀ p : HeightOneSpectrum (𝓞 T.Q.c.F), ∃ κ' : T.Q.c.F, κ' ≠ 0 ∧
      GlobalTheory.GoodPts.BddAll (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p κ' f := by
    intro p
    obtain ⟨pr, hpr, hmem⟩ := exists_prime_mem p
    exact GlobalTheory.CuspBound.exists_bddAll_cusp _ _ _ _ _ _ _ (T.U ((i : ℕ) + 1)) (hT.unf _ hj) p pr hpr hmem
      (goodAt_of_two_primes hT.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne pr hpr) _ _ f
      (dom_wtA κ) hcusp
  choose κ' hκ0 hκb using hbd
  obtain ⟨t, htq, htm⟩ := exists_avoid q hq (hP.toFinset.filter fun p => p.asIdeal ≠ q)
    (fun p hp => (Finset.mem_filter.1 hp).2) (fun p => (vLa p (κ' p)).toNat)
  have ht0 : t ≠ 0 := fun h => htq (h ▸ q.zero_mem)
  have htK : (t : T.Q.c.F) ≠ 0 := by exact_mod_cast ht0
  refine ⟨t, htq, (t : T.Q.c.F) • f, ⟨(sec _ _ _ _).smul_mem _ hfs, ?_, ?_⟩, ?_⟩
  · rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ hfh
  · intro la hla v hv
    have hV := isVal_valSet la v hv
    rw [hV.smul _ _ htK]
    by_cases hlq : la.asIdeal = q
    · have h0 : vAdd la (t : T.Q.c.F) = 0 := vLa_eq_zero_of_not_mem la (hlq ▸ htq)
      rw [h0]
      simpa using hfv la hlq v hv
    · have hmem : la ∈ hP.toFinset.filter fun p => p.asIdeal ≠ q :=
        Finset.mem_filter.2 ⟨hP.mem_toFinset.2 hla, hlq⟩
      have hge : (vLa la (κ' la) : ℤ) ≤ vAdd la (t : T.Q.c.F) :=
        (Int.self_le_toNat _).trans (le_vLa_of_mem la _ (htm la hmem) ht0)
      obtain ⟨y, rfl⟩ := hv
      have hb := (GlobalTheory.GoodPtsModel.bddAll_iff_vAtV (hκ0 la) f).1 (hκb la) y
      exact hb.trans (add_le_add (by exact_mod_cast hge) le_rfl)
  · simp only [CoreJ.phiJ, map_smulₛₗ, LinearMap.map_smul, smul_comm ((lieFac _ _ _ : ℝ) : ℂ)]
    rfl

end GlobalTheory.ScaleInt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitScalarSmulCoreIntegralAdelicFormPlacesStatement

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_unitScalar_smul_coreIntegralAdelicForm_places : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ (i : Fin D.R.m) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)), κ.LastPos → ∀ (q : Ideal (𝓞 T.Q.c.F)), q.IsPrime → ∀ (P : Set (HeightOneSpectrum (𝓞 T.Q.c.F))), P.Finite → ∀ ψ ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA κ) κ.n {p | p.asIdeal = q}, ∃ t : 𝓞 T.Q.c.F, t ∉ q ∧ T.σ₀ (t : T.Q.c.F) • ψ ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA κ) κ.n P := by
  first | exact @GlobalTheory.ScaleInt.smul_mem_baseInt | exact GlobalTheory.ScaleInt.smul_mem_baseInt | (intros; apply GlobalTheory.ScaleInt.smul_mem_baseInt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlueIntegralDecompositionsOverRationalPrime

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DescGlue

open GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries

theorem finite_of_overPrime {L : Type} [Field L] [NumberField L] (l : ℕ) (hl : l.Prime)
    (S : Set (HeightOneSpectrum (𝓞 L))) (h : OverPrime l S) : S.Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 L)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  refine (Ideal.finite_factors h0).subset fun la hla => ?_
  show la.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact h la hla

theorem finite_below {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (φ : K →+* L)
    {S : Set (HeightOneSpectrum (𝓞 L))} (hS : S.Finite) : (below φ S).Finite := by
  have e : below φ S = ⋃ la ∈ S, {p : HeightOneSpectrum (𝓞 K) |
      p.asIdeal = la.asIdeal.comap (RingOfIntegers.mapRingHom φ)} := by
    ext p; simp [below]
  rw [e]
  exact hS.biUnion fun la _ => Set.Subsingleton.finite fun p1 h1 p2 h2 =>
    HeightOneSpectrum.ext (h1.trans h2.symm)



theorem glue : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → ∀ l : ℕ, l.Prime → ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTowerCover T i l C → C.IsPinned (wtA (κ i)) (κ i).n → ∀ S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F)), GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.OverPrime l S → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.UnramAt C.inc S → ∀ φ ∈ C.intForms (wtA (κ i)) (κ i).n S, (∀ k ∈ T.Kf ((i : ℕ) + 1) T.σ₀, ∀ h, φ (h * k) = φ h) → ∀ (m : ℕ) (x : Fin m → C.d.c₂.F) (ψ : Fin m → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, ψ a ∈ baseForms T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n) → φ = ∑ a, C.σ₂ (x a) • ψ a → (∀ la ∈ S, ∃ (m' : ℕ) (x' : Fin m' → ℂ) (ψ' : Fin m' → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IntVal C.σ₂ {la} (x' a)) ∧ (∀ a, ψ' a ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n (GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below C.inc {la})) ∧ φ = ∑ a, x' a • ψ' a) → ∃ (m' : ℕ) (x' : Fin m' → ℂ) (ψ' : Fin m' → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IntVal C.σ₂ S (x' a)) ∧ (∀ a, ψ' a ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n (GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below C.inc S)) ∧ φ = ∑ a, x' a • ψ' a := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hT h1 h2 h3 h4 h5 h6 i hVS hV hFP l hl C hC hPin S hS hUn φ hφmem hKf
    m x ψ hψ hφ hloc
  classical
  have hσ : ∀ t : T.Q.c.F, C.σ₂ (C.inc t) = T.σ₀ t := fun t => by
    rw [← RingHom.comp_apply, hC.1.2.2.1]
  have hfin : S.Finite := finite_of_overPrime l hl S hS
  rcases S.eq_empty_or_nonempty with hS0 | hSne
  · subst hS0
    refine ⟨m, fun a => C.σ₂ (x a), ψ, fun a => ⟨x a, rfl, fun la h => absurd h (Set.notMem_empty la)⟩,
      fun a => ?_, hφ⟩
    obtain ⟨f, ⟨hf1, hf2⟩, hf⟩ := hψ a
    exact ⟨f, ⟨hf1, hf2, fun p hp => by
      obtain ⟨la, hla, _⟩ := hp
      exact absurd hla (Set.notMem_empty la)⟩, hf⟩
  set S' := hfin.toFinset with hS'
  have hmem : ∀ la : S', la.1 ∈ S := fun la => hfin.mem_toFinset.1 la.2
  choose m' x' ψ' hx' hψ' hφ' using fun la : S' => hloc la.1 (hmem la)
  choose a' ha' hav using fun (la : S') (a : Fin (m' la)) => hx' la a
  have hset : ∀ la : S', below C.inc {la.1} =
      {p | p.asIdeal = la.1.asIdeal.comap (RingOfIntegers.mapRingHom C.inc)} := fun la => by
    ext p; simp [below]
  choose t ht htψ using fun (la : S') (a : Fin (m' la)) =>
    GlobalTheory.T.exists_unitScalar_smul_coreIntegralAdelicForm_places D T hT i (κ i) (GlobalTheory.AdTh.lastPos_of_kapIs h6.kap i)
      (la.1.asIdeal.comap (RingOfIntegers.mapRingHom C.inc))
      (Ideal.IsPrime.comap _ (hK := la.1.isPrime)) (below C.inc S) (finite_below C.inc hfin) (ψ' la a)
      (hset la ▸ hψ' la a)
  have hte : ∀ (la : S') (a : Fin (m' la)), la.1.valuation _ (C.inc (t la a : T.Q.c.F)) = 1 := fun la a => by
    have e : C.inc (t la a : T.Q.c.F) = ((RingOfIntegers.mapRingHom C.inc (t la a) : 𝓞 C.d.c₂.F) : C.d.c₂.F) := rfl
    rw [e]
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem la.1).mpr fun h => ht la a (Ideal.mem_comap.2 h)
  have ht0 : ∀ (la : S') (a : Fin (m' la)), T.σ₀ (t la a : T.Q.c.F) ≠ 0 := fun la a => by
    refine (map_ne_zero _).2 (RingOfIntegers.coe_ne_zero_iff.mpr ?_)
    rintro h0
    exact ht la a (h0 ▸ Ideal.zero_mem _)
  let Y : S' → Finset C.d.c₂.F := fun la => Finset.univ.image fun a => a' la a / C.inc (t la a : T.Q.c.F)
  have hY : ∀ la, ∀ y ∈ Y la, la.1.valuation _ y ≤ 1 := by
    intro la y hy
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hy
    rw [map_div₀, hte, div_one]
    exact hav la a la.1 (Set.mem_singleton _)
  have hne : S'.Nonempty := by
    obtain ⟨la, h⟩ := hSne
    exact ⟨la, hfin.mem_toFinset.2 h⟩
  obtain ⟨e, he1, he⟩ := GlobalTheory.exists_partition_one_integral_at_places _ S' hne Y hY
  let ι := Σ la : S', Fin (m' la)
  let ε := Fintype.equivFin ι
  let X : ι → ℂ := fun s => C.σ₂ (e s.1 * (a' s.1 s.2 / C.inc (t s.1 s.2 : T.Q.c.F)))
  let Ψ : ι → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ) := fun s => T.σ₀ (t s.1 s.2 : T.Q.c.F) • ψ' s.1 s.2
  have key : ∀ s : ι, X s • Ψ s = C.σ₂ (e s.1) • (x' s.1 s.2 • ψ' s.1 s.2) := by
    intro s
    simp only [X, Ψ, smul_smul, map_mul, map_div₀, hσ, ha']
    congr 1
    field_simp [ht0 s.1 s.2]
  refine ⟨Fintype.card ι, fun k => X (ε.symm k), fun k => Ψ (ε.symm k), fun k => ⟨_, rfl, fun la'' h'' =>
    he _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)) la'' (hfin.mem_toFinset.2 h'')⟩,
    fun k => htψ _ _, ?_⟩
  symm
  calc ∑ k, X (ε.symm k) • Ψ (ε.symm k) = ∑ s : ι, X s • Ψ s := Equiv.sum_comp ε.symm (fun s => X s • Ψ s)
    _ = ∑ s : ι, C.σ₂ (e s.1) • (x' s.1 s.2 • ψ' s.1 s.2) := Finset.sum_congr rfl fun s _ => key s
    _ = ∑ la : S', ∑ a : Fin (m' la), C.σ₂ (e la) • (x' la a • ψ' la a) := Fintype.sum_sigma _
    _ = ∑ la : S', C.σ₂ (e la) • φ := Finset.sum_congr rfl fun la _ => by rw [← Finset.smul_sum, ← hφ' la]
    _ = φ := by rw [← Finset.sum_smul, ← map_sum, he1, map_one, one_smul]

end GlobalTheory.DescGlue
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlueIntegralDecompositionsOverRationalPrimeStatement

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.glue_integral_decompositions_over_rationalPrime : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → ∀ l : ℕ, l.Prime → ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTowerCover T i l C → C.IsPinned (wtA (κ i)) (κ i).n → ∀ S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F)), GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.OverPrime l S → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.UnramAt C.inc S → ∀ φ ∈ C.intForms (wtA (κ i)) (κ i).n S, (∀ k ∈ T.Kf ((i : ℕ) + 1) T.σ₀, ∀ h, φ (h * k) = φ h) → ∀ (m : ℕ) (x : Fin m → C.d.c₂.F) (ψ : Fin m → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, ψ a ∈ baseForms T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n) → φ = ∑ a, C.σ₂ (x a) • ψ a → (∀ la ∈ S, ∃ (m' : ℕ) (x' : Fin m' → ℂ) (ψ' : Fin m' → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IntVal C.σ₂ {la} (x' a)) ∧ (∀ a, ψ' a ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n (GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below C.inc {la})) ∧ φ = ∑ a, x' a • ψ' a) → ∃ (m' : ℕ) (x' : Fin m' → ℂ) (ψ' : Fin m' → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IntVal C.σ₂ S (x' a)) ∧ (∀ a, ψ' a ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n (GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below C.inc S)) ∧ φ = ∑ a, x' a • ψ' a := by
  first | exact @GlobalTheory.DescGlue.glue | exact GlobalTheory.DescGlue.glue | (intros; apply GlobalTheory.DescGlue.glue <;> assumption)
end
end
