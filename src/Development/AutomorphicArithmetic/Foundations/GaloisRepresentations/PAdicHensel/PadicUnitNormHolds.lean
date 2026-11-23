module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PAdFour
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PBlockMat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PCongrScale
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PDefSign
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PFinCls
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PFinCongr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm
import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PInfCongr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenKGLInvEntries
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyStableSubspaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PLocRoot
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PLocUnit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PNormTwo
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdeleEquivOfLocal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PPadicSqFin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PPadicUnitNorm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PRelOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PScale
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PSplitCongr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PTrivMat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PUnitCls
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PZSqFin
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PHenselV

section

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pHenselV :
    HenselV := by
  intro F _ _ v f a₀ hf h0 h1
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
  haveI : IsPrecomplete (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) (v.adicCompletionIntegers F) :=
    Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.completion_integers_precomplete v hϖ
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) (v.adicCompletionIntegers F) := {}
  haveI := IsAdicComplete.henselianRing (v.adicCompletionIntegers F)
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))
  obtain ⟨a, ha, hm⟩ := HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) f hf a₀
    (by rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact h0)
    (h1.map (Ideal.Quotient.mk _))
  refine ⟨a, ha, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm
  exact hm
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PIsoEx

section

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pIsoEx :
    NormTwo → BlockMat → IsoEx := by
  intro hN hB E _ _ _ A n hn
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨x, y, hxy, hint⟩ := hN E A
  have hinv : ∀ z, cF E (cF E z) = z := fun z => GlobalTheory.CompanionTheory.OnlyStab.conjFin_invol z
  have hfix : cF E (algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.c : E)) =
      algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.c : E) := by
    refine (conjFin_algebraMap _ _).trans (congrArg _ ?_)
    change IsCMField.complexConj E (A.c : E) = (A.c : E)
    rw [← A.bar_eq, A.c_real]
  obtain ⟨a, ha, hS⟩ := hB _ (cF E) hinv _ x y hfix hxy m
  refine ⟨a, ?_, ?_⟩
  · have hd : (Matrix.diagonal fun i => ((A.dg (2 * m + 1) i : 𝓞 E) : E)).map
        (algebraMap E (FiniteAdeleRing (𝓞 E) E)) =
        Matrix.diagonal (fun i : Fin (2 * m + 1) => if (i : ℕ) = 0 then 1 else
          algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.c : E)) := by
      rw [Matrix.diagonal_map (map_zero _)]
      congr 1
      funext i
      simp only [Arith.dg]
      split_ifs <;> simp
    rw [hd]
    exact ha
  · intro w q hq hg hqw
    obtain ⟨h1, h2, h3, h4⟩ := hint w q hq hg hqw
    have hc : algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.c : E) ∈
        (w.adicCompletionIntegers E).toSubring.comap (pLoc E w) := by
      change Valued.v (algebraMap E (w.adicCompletion E) (A.c : E)) ≤ 1
      exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (A.c : E)).trans_le
        (HeightOneSpectrum.valuation_le_one w A.c)
    have hall := hS ((w.adicCompletionIntegers E).toSubring.comap (pLoc E w)) h1 h2 h3 h4 hc
    rw [GlobalTheory.HenQ.Basic.mem_KGL_iff]
    refine ⟨fun i j => (hall i j).1, fun i j => ?_⟩
    rw [← map_inv]
    exact (hall i j).2
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PLocFour

section

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pLocFour :
    LocFour := by
  intro F _ _ v tr nm hΔ u hu
  haveI : CharZero (HeightOneSpectrum.adicCompletion F v) :=
    (RingHom.charZero_iff (algebraMap F (HeightOneSpectrum.adicCompletion F v)).injective).mp inferInstance
  have h2 : (2 : HeightOneSpectrum.adicCompletion F v) ≠ 0 := two_ne_zero
  have hD : ((tr : HeightOneSpectrum.adicCompletion F v) ^ 2 - 4 * nm) ≠ 0 := by
    have h := (Int.cast_ne_zero (α := HeightOneSpectrum.adicCompletion F v)).mpr hΔ
    push_cast at h
    exact h
  set D : HeightOneSpectrum.adicCompletion F v := (tr : HeightOneSpectrum.adicCompletion F v) ^ 2 - 4 * nm
    with hDdef
  let c : Fin 5 → HeightOneSpectrum.adicCompletion F v := ![1, -(D / 4), 1, -(D / 4), -u]
  have hc : ∀ i, c i ≠ 0 := by
    intro i
    fin_cases i <;> simp [c, hD, hu]
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.LocalQuad.isotropic_adicCompletion_of_five_le F v (ι := Fin 5) (by simp) c
  obtain ⟨z, hz4, hz⟩ := GlobalTheory.HermLocal.exists_zero_coord h2 hc hx0 hx 4
  have hz' : z 0 ^ 2 + -(D / 4) * z 1 ^ 2 + z 2 ^ 2 + -(D / 4) * z 3 ^ 2 + -u * z 4 ^ 2 = 0 := by
    rw [Fin.sum_univ_five] at hz
    simpa [c] using hz
  obtain ⟨w, hw⟩ : ∃ w, z 4 * w = 1 := ⟨(z 4)⁻¹, mul_inv_cancel₀ hz4⟩
  refine ⟨z 0 * w - tr / 2 * (z 1 * w), z 1 * w, z 2 * w - tr / 2 * (z 3 * w), z 3 * w, ?_⟩
  unfold qf
  rw [hDdef] at hz'
  linear_combination w ^ 2 * hz' + u * (z 4 * w + 1) * hw
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PPadMap

section

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pPadMap :
    PadMap := by
  intro F _ _ w
  set u : HeightOneSpectrum (𝓞 ℚ) := HeightOneSpectrum.under (𝓞 ℚ) w with hu
  set v : HeightOneSpectrum ℤ := GlobalTheory.NormLevelCompare.primeCorr.symm u with hv
  have hw : HeightOneSpectrum.under (𝓞 ℚ) w = GlobalTheory.NormLevelCompare.primeCorr v := by
    rw [hv, Equiv.apply_symm_apply]
  haveI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v : ℕ)) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  let f₁ := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toAlgEquiv.toRingEquiv.toRingHom
  let f₂ := (Padic.adicCompletionEquiv (𝓞 ℚ)
    (Rat.HeightOneSpectrum.primesEquiv v)).toAlgEquiv.toRingEquiv.toRingHom
  refine ⟨v, ((GlobalTheory.LFun.complMap (F := ℚ) (E := F) hw).comp f₂).comp f₁, ?_⟩
  intro q hq
  have hgen : Rat.HeightOneSpectrum.natGenerator v = Rat.HeightOneSpectrum.natGenerator u := by
    change (Rat.HeightOneSpectrum.primesEquiv v).1 = (Rat.HeightOneSpectrum.primesEquiv u).1
    simp [hv, GlobalTheory.NormLevelCompare.primeCorr]
  set p := Rat.HeightOneSpectrum.natGenerator u with hp
  have hdvd : (p : ℤ) ∣ q := by
    have hfix : Rat.IsIntegralClosure.intEquiv ℤ q = q := by
      simpa using map_intCast (Rat.IsIntegralClosure.intEquiv ℤ) q
    have hmem : q ∈ v.asIdeal.map (Rat.IsIntegralClosure.intEquiv ℤ) := by
      rw [← hfix]
      exact (Ideal.apply_mem_of_equiv_iff).2 hq
    rw [← Rat.HeightOneSpectrum.span_natGenerator, Ideal.mem_span_singleton, hgen] at hmem
    exact hmem
  have hpu : ((p : ℕ) : 𝓞 ℚ) ∈ u.asIdeal := by
    have h := (Rat.HeightOneSpectrum.natGenerator_dvd_iff u (n := p)).1 dvd_rfl
    rw [← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) p] at h
    exact (Ideal.apply_mem_of_equiv_iff).1 h
  have hpw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal := by
    have h : algebraMap (𝓞 ℚ) (𝓞 F) (p : 𝓞 ℚ) ∈ w.asIdeal := hpu
    simpa using h
  obtain ⟨k, rfl⟩ := hdvd
  push_cast
  exact Ideal.mul_mem_right _ _ (by exact_mod_cast hpw)
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PSplitRep

section

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pSplitRep :
    SplitRep := by
  intro R _ tr nm ρ hρ hd u
  obtain ⟨w, hw⟩ := hd.exists_right_inv
  refine ⟨1 - ((tr : R) - ρ) * ((u - 1) * w), (u - 1) * w, ?_⟩
  unfold qf
  linear_combination ((u - 1) * w) ^ 2 * hρ + (u - 1) * hw
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PZUnitNorm

section

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pZUnitNorm :
    PadicUnitNorm → ZUnitNorm := by
  intro hP v D hv u hu
  haveI : Fact (Rat.HeightOneSpectrum.primesEquiv v : ℕ).Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  have hint : ∀ z : v.adicCompletion ℚ, Valued.v z ≤ 1 →
      ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v z‖ ≤ 1 := by
    intro z hz
    exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).mapsTo
      ((HeightOneSpectrum.mem_adicCompletionIntegers ℤ ℚ v).2 hz)
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, map_zero] at hu
    exact zero_ne_one hu
  have hn : ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u‖ = 1 := by
    apply le_antisymm (hint u hu.le)
    have h1 := hint u⁻¹ (by rw [map_inv₀, hu, inv_one])
    rw [map_inv₀, norm_inv] at h1
    have hne : Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u ≠ 0 := fun h =>
      hu0 ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).injective
        (h.trans (map_zero _).symm))
    exact (inv_le_one₀ (norm_pos_iff.2 hne)).1 h1
  have hdiv : ¬ ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℤ) ∣ 2 * D := by
    intro hd
    apply hv
    have hm : 2 * D ∈ Ideal.span {((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ)} :=
      Ideal.mem_span_singleton.2 hd
    rw [Rat.HeightOneSpectrum.span_natGenerator, Ideal.mem_map_of_equiv] at hm
    obtain ⟨x, hx, hxe⟩ := hm
    have hid : Rat.IsIntegralClosure.intEquiv ℤ x = x := by
      simpa using eq_intCast (Rat.IsIntegralClosure.intEquiv ℤ : ℤ →+* ℤ) x
    rw [hid] at hxe
    rw [← hxe]
    exact hx
  obtain ⟨x, y, hxy⟩ := hP _ D hdiv _ hn
  refine ⟨(Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm x,
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm y, ?_⟩
  have h2 := congrArg (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm hxy
  simpa using h2
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNormHolds

section

@[expose] public section

namespace UpperTheory.Gal.G1

theorem LocFour_holds : LocFour := pLocFour
theorem HenselV_holds : HenselV := pHenselV
theorem SplitRep_holds : SplitRep := pSplitRep
theorem BlockMat_holds : BlockMat := pBlockMat
theorem PadMap_holds : PadMap := pPadMap
theorem Scale_holds : Scale := pScale
theorem PadicUnitNorm_holds : PadicUnitNorm := pPadicUnitNorm
theorem PadicSqFin_holds : PadicSqFin := pPadicSqFin
theorem TrivMat_holds : TrivMat := pTrivMat
theorem CongrScale_holds : CongrScale := pCongrScale
theorem SplitCongr_holds : SplitCongr := pSplitCongr
theorem InfCongr_holds : InfCongr := pInfCongr
theorem DefSign_holds : DefSign := pDefSign
theorem RelOf_holds : RelOf := pRelOf
theorem LocUnit_holds : LocUnit := pLocUnit HenselV_holds
theorem LocRoot_holds : LocRoot := pLocRoot HenselV_holds
theorem ZUnitNorm_holds : ZUnitNorm := pZUnitNorm PadicUnitNorm_holds
theorem ZSqFin_holds : ZSqFin := pZSqFin PadicSqFin_holds
theorem AdFour_holds : AdFour := pAdFour LocFour_holds LocUnit_holds LocRoot_holds SplitRep_holds
theorem UnitCls_holds : UnitCls := pUnitCls Scale_holds ZUnitNorm_holds ZSqFin_holds
theorem FinCongr_holds : FinCongr := pFinCongr PadMap_holds LocRoot_holds TrivMat_holds CongrScale_holds SplitCongr_holds DefSign_holds
theorem NormTwo_holds : NormTwo := pNormTwo AdFour_holds
theorem FinCls_holds : FinCls := pFinCls UnitCls_holds FinCongr_holds InfCongr_holds DefSign_holds RelOf_holds
theorem IsoEx_holds : IsoEx := pIsoEx NormTwo_holds BlockMat_holds

end UpperTheory.Gal.G1
end
end
