module

public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeSplitOne
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DegOneIffSurjective
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorizationStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharInfTrivialOfTrivAtDegOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharTrivialAtPlaceOfDegOneCofiniteTrivialStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.AgreementAtAlmostAllSplitPrimes

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.N

namespace GlobalTheory.IndefiniteRowSideFullHecke.AgreementAtAlmostAllSplitPrimes

def AgreeAtAlmostAllSplit {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}
    (A : NAut N) (χ χ' : A.CG 1) : Prop :=
  {w : PlE H | IsSplitPl H w ∧ A.locG χ w ≠ A.locG χ' w}.Finite

def HeckeCharEqOfSplit {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N) : Prop :=
  ∀ χ χ' : A.CG 1, AgreeAtAlmostAllSplit A χ χ' → χ = χ'

theorem agreeAtAlmostAllSplit_iff {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}
    (A : NAut N) (χ χ' : A.CG 1) :
    AgreeAtAlmostAllSplit A χ χ' ↔
      ∀ᶠ w in Filter.cofinite, IsSplitPl H w → A.locG χ w = A.locG χ' w := by
  simp only [AgreeAtAlmostAllSplit, Filter.eventually_cofinite, Classical.not_imp]

end GlobalTheory.IndefiniteRowSideFullHecke.AgreementAtAlmostAllSplitPrimes
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.EventuallyResidueDegreeOnePrimeMovedByGalois

section

@[expose] public section

open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit

namespace GlobalTheory.HeckeSplit

theorem exists_int_moved (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (c : E ≃ₐ[F] E) (hc : c ≠ 1) : ∃ θ : 𝓞 E, c (θ : E) ≠ (θ : E) := by
  by_contra h
  push_neg at h
  apply hc
  ext z
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) z
  simp only [map_div₀, AlgEquiv.one_apply]
  exact congrArg₂ (· / ·) (h a) (h b)

theorem finite_setOf_mem_asIdeal (E : Type) [Field E] [NumberField E] (δ : 𝓞 E) (h : δ ≠ 0) :
    {w : HeightOneSpectrum (𝓞 E) | δ ∈ w.asIdeal}.Finite := by
  have := Ideal.finite_factors (R := 𝓞 E) (I := Ideal.span {δ}) (by simpa using h)
  refine this.subset fun w hw => ?_
  simp only [Set.mem_setOf_eq] at hw ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact hw

theorem eventually_degOne_moved : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [Algebra.IsQuadraticExtension F E] (c : E ≃ₐ[F] E), c ≠ 1 →
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, DegOne F w →
      ∃ x : 𝓞 E, x ∈ w.asIdeal ∧ ∀ y : 𝓞 E, (y : E) = c (x : E) → y ∉ w.asIdeal := by
  intro F E _ _ _ _ _ _ c hc
  obtain ⟨θ, hθ⟩ := exists_int_moved F E c hc
  have hint : IsIntegral ℤ (c (θ : E)) := θ.isIntegral_coe.map c.toRingHom.toIntAlgHom
  set θ' : 𝓞 E := ⟨c (θ : E), hint⟩ with hθ'
  have hδ : θ - θ' ≠ 0 := by
    intro h0
    apply hθ
    have := congrArg (fun t : 𝓞 E => (t : E)) h0
    push_cast at this
    exact (sub_eq_zero.mp this).symm
  refine (finite_setOf_mem_asIdeal E (θ - θ') hδ).subset ?_ |> Filter.eventually_cofinite.mpr
  intro w hw
  simp only [Set.mem_setOf_eq] at hw ⊢
  by_contra hnot
  apply hw
  intro hdeg
  obtain ⟨u, hu⟩ := hdeg θ
  refine ⟨θ - algebraMap (𝓞 F) (𝓞 E) u, hu, fun y hy hyw => hnot ?_⟩
  have hcu : c ((algebraMap (𝓞 F) (𝓞 E) u : 𝓞 E) : E) = ((algebraMap (𝓞 F) (𝓞 E) u : 𝓞 E) : E) := by
    have : ((algebraMap (𝓞 F) (𝓞 E) u : 𝓞 E) : E) = algebraMap F E (u : F) := rfl
    rw [this, AlgEquiv.commutes]
  have hy' : y = θ' - algebraMap (𝓞 F) (𝓞 E) u := by
    apply RingOfIntegers.ext
    rw [hy]
    push_cast
    rw [map_sub, hcu]
    rfl
  have := w.asIdeal.sub_mem hu hyw
  rw [hy'] at this
  convert this using 1
  ring

end GlobalTheory.HeckeSplit
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.EventuallyResidueDegreeOnePrimeMovedByGaloisStatement

section

@[expose] public section

open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit

theorem _root_.GlobalTheory.T.eventually_residueDegreeOne_prime_moved_by_galois : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E] (c : E ≃ₐ[F] E), c ≠ 1 → ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, DegOne F w → ∃ x : 𝓞 E, x ∈ w.asIdeal ∧ ∀ y : 𝓞 E, (y : E) = c (x : E) → y ∉ w.asIdeal := by
  first | exact @GlobalTheory.HeckeSplit.eventually_degOne_moved | exact GlobalTheory.HeckeSplit.eventually_degOne_moved | (intros; apply GlobalTheory.HeckeSplit.eventually_degOne_moved <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharInfTrivialOfTrivAtDegOneStatement

section

@[expose] public section

open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit

theorem _root_.GlobalTheory.T.heckeChar_inf_trivial_of_trivAt_degOne : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] [Algebra.IsQuadraticExtension F E] (χ : Ideles E →* ℂˣ), IsHeckeChar E χ → (∀ᶠ w in Filter.cofinite, DegOne F w → TrivAt χ w) → ∀ x : (InfiniteAdeleRing E)ˣ, χ (infIdele E x) = 1 := by
  first | exact @GlobalTheory.HeckeInfTriv.inf_trivial_of_trivAt_degOne | exact GlobalTheory.HeckeInfTriv.inf_trivial_of_trivAt_degOne | (intros; apply GlobalTheory.HeckeInfTriv.inf_trivial_of_trivAt_degOne <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharCmEqOneOfTrivialDegreeOne

section

@[expose] public section

open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit

namespace GlobalTheory.HeckeSplit

theorem heckeChar_eq_one_of_degOne : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
    [Algebra.IsQuadraticExtension F E] (χ : Ideles E →* ℂˣ), IsHeckeChar E χ →
    (∀ᶠ w in Filter.cofinite, DegOne F w → TrivAt χ w) → χ = 1 := by
  intro F E _ _ _ _ _ _ _ _ χ hχ hdeg
  have hinf := GlobalTheory.T.heckeChar_inf_trivial_of_trivAt_degOne F E χ hχ hdeg
  have hfin := GlobalTheory.T.heckeChar_trivialAtPlace_of_degOne_cofinite_trivial F E χ hχ hdeg hinf
  ext1 x
  have hfact := (GlobalTheory.T.continuous_ideleChar_local_factorization E χ hχ.1).2.2 x ∅ (fun v _ => hfin v _)
  rw [hfact, hinf]
  simp

end GlobalTheory.HeckeSplit
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharCmEqOneOfTrivialDegreeOneStatement

section

@[expose] public section

open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit

theorem _root_.GlobalTheory.T.heckeChar_cm_eq_one_of_trivial_degree_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] [Algebra.IsQuadraticExtension F E] (χ : Ideles E →* ℂˣ), IsHeckeChar E χ → (∀ᶠ w in Filter.cofinite, DegOne F w → TrivAt χ w) → χ = 1 := by
  first | exact @GlobalTheory.HeckeSplit.heckeChar_eq_one_of_degOne | exact GlobalTheory.HeckeSplit.heckeChar_eq_one_of_degOne | (intros; apply GlobalTheory.HeckeSplit.heckeChar_eq_one_of_degOne <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharEqOfSplitOfTied

section

@[expose] public section

noncomputable section

namespace GlobalTheory.HeckeSplitRow

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.N Formalism.L2.Host

def HeckeCharTie {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) : Prop :=
  ∃ e : A.CG 1 → HChar H.E, Function.Injective e ∧
    (∀ π w, A.unr (A.locG π w) ↔ (e π).UnrAt w) ∧
    ∀ π w, (e π).UnrAt w → A.frobEig (A.locG π w) = {(((e π).val w)⁻¹ : ℂˣ).1}

theorem heckeCharTie_of_tied {D : D7} {C : CharFrame D} {nch : NChoice D} {Tp : TupTied D C nch}
    (T : NCharTied D C nch Tp) : HeckeCharTie D.nd D.naut :=
  ⟨fun π => (T.e1 π).1, fun _ _ h => T.e1.injective (Subtype.ext h), T.unr_iff, T.frob⟩

theorem loc_eq_one {L : Type} [Field L] [NumberField L] (χ : HChar L) (v : HeightOneSpectrum (𝓞 L))
    (hu : χ.UnrAt v) (hv : χ.val v = 1) : χ.loc v = 1 := by
  ext x : 1
  set p := atFin v (unif v) with hp
  have hpv : Valued.v (p : v.adicCompletion L) = WithZero.exp (-1 : ℤ) := unif_spec v
  have hx0 : Valued.v (x : v.adicCompletion L) ≠ 0 := by simp
  set n : ℤ := WithZero.log (Valued.v (x : v.adicCompletion L)) with hn
  have hxn : Valued.v (x : v.adicCompletion L) = WithZero.exp n := (WithZero.exp_log hx0).symm
  have hunit : IsUnitAt v (x * p ^ n) := by
    unfold IsUnitAt
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hpv, hxn, ← WithZero.exp_zsmul,
      ← WithZero.exp_add]
    simp
  have h1 := hu _ hunit
  have hp1 : χ.loc v p = 1 := hv
  rw [map_mul, map_zpow, hp1, one_zpow, mul_one] at h1
  exact h1

theorem complexConj_eq {R : Ranks} (H : Host R) [IsCMField H.E] (z : H.E) :
    IsCMField.complexConj H.E z = H.conj z := by
  apply H.φ₀.injective
  rw [NumberField.IsCMField.complexEmbedding_complexConj]
  exact (H.toHostAx.conjE_apply H.φ₀ z).symm

theorem eq_one_of_split {R : Ranks} (H : Host R) (ν : HChar H.E)
    (h : ∀ᶠ w in Filter.cofinite, IsSplitPl H w → ν.UnrAt w ∧ ν.val w = 1) : ν = 1 := by
  have : IsCMField H.E := H.isCMField_hostE
  apply Subtype.ext
  refine GlobalTheory.T.heckeChar_cm_eq_one_of_trivial_degree_one (maximalRealSubfield H.E) H.E ν.1 ν.2 ?_
  filter_upwards [h, GlobalTheory.T.eventually_residueDegreeOne_prime_moved_by_galois (maximalRealSubfield H.E) H.E (IsCMField.complexConj H.E)
    (IsCMField.complexConj_ne_one H.E)] with w hw hs hd
  obtain ⟨x, hx, hy⟩ := hs hd
  have hsp : IsSplitPl H w := ⟨x, hx, fun y hyx => hy y (by rw [complexConj_eq]; exact hyx)⟩
  exact (GlobalTheory.HeckeSplit.trivAt_iff H.E ν w).2 (loc_eq_one ν w (hw hsp).1 (hw hsp).2)

theorem heckeCharEqOfSplit_of_tie : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂)
    (A : NAut N), HeckeCharTie N A → GlobalTheory.IndefiniteRowSideFullHecke.AgreementAtAlmostAllSplitPrimes.HeckeCharEqOfSplit N A := by
  rintro R H what₂ N A ⟨e, hinj, hunr, hfrob⟩ χ χ' hag
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AgreementAtAlmostAllSplitPrimes.agreeAtAlmostAllSplit_iff] at hag
  apply hinj
  rw [← mul_inv_eq_one]
  apply eq_one_of_split H
  filter_upwards [hag, A.locG_unr_ae χ, A.locG_unr_ae χ'] with w hw h1 h2 hs
  have u1 := (hunr χ w).1 h1
  have u2 := (hunr χ' w).1 h2
  refine ⟨fun x hx => ?_, ?_⟩
  · change (e χ).loc w x * ((e χ').loc w x)⁻¹ = 1
    rw [u1 x hx, u2 x hx, inv_one, mul_one]
  · have hf := hfrob χ w u1
    rw [hw hs, hfrob χ' w u2, Multiset.singleton_inj, Units.val_inj, inv_inj] at hf
    rw [HChar.val_mul, HChar.val_inv, hf, mul_inv_cancel]

theorem heckeSplitOne_of_tie {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N) (h : HeckeCharTie N A) : GlobalTheory.ThetaExh.HeckeSplitOne N A := fun χ χ' hw =>
  heckeCharEqOfSplit_of_tie R H what₂ N A h χ χ' ((GlobalTheory.IndefiniteRowSideFullHecke.AgreementAtAlmostAllSplitPrimes.agreeAtAlmostAllSplit_iff A χ χ').2 hw)

end GlobalTheory.HeckeSplitRow
end
end
end
