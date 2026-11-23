module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PrimeProj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.CenExHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.NsmulIntegIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PDatEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PFrameEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PGoodOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PInIdUnit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PLevBasic
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PNearNbhd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CyclotomicConjugation.ConjLoc
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PProjLev
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PSiteTriv
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PStabOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.SameKTrans
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.SpanLePow
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.SatCard
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.NhdsBasisLevelSubgroup
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CharConjHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ExistsIdempotentHeckeOperatorWithRegularSupportAlt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.AuxiliaryInertOddPrime
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.CnjApply
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.RelIndexNeZeroOfOpen
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.SpecData
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ValOfNotMem

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PCongOf

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl

theorem UpperTheory.Gal.Int.Geo.Pl.congOf_of :
    LevBasic → TjOK → TjIdx → CongOf := by
  intro hL hT hI E _ _ _ A n p _ S F x hx N w σ J L _ g θ ϑ hD hm
  obtain ⟨-, h2, h3, -⟩ := hL p S.D S.G S.L
  obtain ⟨l1, l2, l3, l4, l5⟩ := σ.lv
  refine ⟨σ.q, σ.r, Ideal.span {((ordCompl[σ.q] N.1 : ℕ) : 𝓞 E)} * σ.𝔞, σ.K₀, σ.atp,
    ⟨ordCompl[σ.q] N.1, σ.𝔞, l1, l2, l3, l4, l5, rfl⟩, σ.isLev,
    h2 _ _ _ _ (h3 N.1) σ.isLev ((Ideal.span_singleton_le_iff_mem _).2 σ.mem), σ.mem, hD, ?_⟩
  intro i hi
  obtain ⟨j, ⟨hin, hK, hH, hM⟩, hθ⟩ := hm i hi
  refine ⟨j, hK, (hT E A n p S F x hx N w σ i hin _ hH).2, ?_, ?_, ?_⟩
  · rw [hM]; exact Dvd.intro_left _ rfl
  · intro _
    exact hI E A n p S F x hx N w σ i hin _ hH
  · rw [hθ, idx, hK]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PPrimeProj

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL satEig)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 Plc GLw AfQ sim mat comp rat loc lev SameK IsCen Shape IsForm IsKap mOf)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Int.Geo.Pl

open UpperTheory.Gal.CertificateRingHomMap (Sim mem_Sim cj)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap below)

def cutU {R : Type} [Ring R] (e : R) (he : e * e = e) (hc : ∀ x, x * e = e * x) : Rˣ →* Rˣ :=
  Units.map
    { toFun := fun x => e * x + (1 - e)
      map_one' := by simp
      map_mul' := fun x y => by
        have h1 : e * x * (e * y) = e * (x * y) := by rw [mul_assoc, ← mul_assoc x, hc, mul_assoc, ← mul_assoc, he]
        have h2 : e * x * (1 - e) = 0 := by rw [← hc, mul_assoc, mul_sub, mul_one, he, sub_self, mul_zero]
        have h3 : (1 - e) * (e * y) = 0 := by rw [← mul_assoc, sub_mul, one_mul, he, sub_self, zero_mul]
        have h4 : (1 - e) * (1 - e) = 1 - e := by rw [mul_sub, mul_one, sub_mul, one_mul, he, sub_self, sub_zero]
        rw [add_mul, mul_add, mul_add, h1, h2, h3, h4, add_zero, zero_add] }

theorem sim_cut {A B : Type} [CommRing A] [CommRing B] (σ : A →+* A) (i : B →+* A) (n : ℕ) (e : B) (he : e * e = e)
    (hσ : σ (i e) = i e) : ∃ π : Sim σ i n →* Sim σ i n, ∀ g, (π g).1.1.val = i e • g.1.1.val + (1 - i e) • 1 := by
  have hie : i e * i e = i e := by rw [← map_mul, he]
  have h1 : (i e • (1 : Matrix (Fin n) (Fin n) A)) * (i e • 1) = i e • 1 := by simp [smul_smul, hie]
  have h2 : ∀ x : Matrix (Fin n) (Fin n) A, x * (i e • 1) = (i e • 1) * x := by simp
  have hv : ∀ g : GL (Fin n) A, (cutU _ h1 h2 g).val = i e • g.val + (1 - i e) • 1 := fun g => by
    show (i e • (1 : Matrix (Fin n) (Fin n) A)) * g.val + (1 - i e • 1) = _
    simp [sub_smul]
  refine ⟨(((cutU _ h1 h2).prodMap (cutU e he fun x => mul_comm _ _)).comp (Sim σ i n).subtype).codRestrict _ fun g => ?_, fun g => hv _⟩
  have hg := mem_Sim.1 g.2
  refine mem_Sim.2 ?_
  show ((cutU _ h1 h2 g.1.1).val.map σ)ᵀ * (cutU _ h1 h2 g.1.1).val = i (e * g.1.2.val + (1 - e)) • 1
  have h3 : ((i e • g.1.1.val + (1 - i e) • (1 : Matrix (Fin n) (Fin n) A)).map σ)ᵀ = i e • (g.1.1.val.map σ)ᵀ + (1 - i e) • 1 := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp [hσ]
    · simp [hσ, Matrix.one_apply, hab, Ne.symm hab]
  have h4 : i e * (1 - i e) = 0 := by rw [mul_sub, mul_one, hie, sub_self]
  have h5 : (1 - i e) * (1 - i e) = 1 - i e := by rw [sub_mul, one_mul, h4, sub_zero]
  rw [hv, h3, add_mul, mul_add, mul_add]
  simp only [smul_mul_smul_comm, hg, hie, h4, h5, mul_comm (1 - i e) (i e), zero_smul, add_zero, zero_add, smul_smul, mul_one,
    map_add, map_mul, map_sub, map_one, add_smul]

theorem nat_mem_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (q : ℕ) (u : Plc E) :
    (q : 𝓞 E) ∈ (cj u).asIdeal ↔ (q : 𝓞 E) ∈ u.asIdeal := by
  have h := (CertificateRingHomMap.ZetaNonvanishing₂.conjLoc E 0 u).2.2.1 q
  have key : ∀ w : Plc E, (q : 𝓞 E) ∈ w.asIdeal ↔ Valued.v ((q : ℕ) : w.adicCompletion E) < 1 := fun w => by
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have : (((q : ℕ) : E) : w.adicCompletion E) = (q : w.adicCompletion E) := map_natCast (algebraMap E (w.adicCompletion E)) q
    have h2 : ((q : 𝓞 E) : E) = q := map_natCast (algebraMap (𝓞 E) E) q
    rw [← this, ← h2]
  rw [key, key, h]

theorem primeProj_holds : PrimeProj := by
  intro E _ _ _ n q _
  let e : AfQ := ⟨fun v => if (q : 𝓞 ℚ) ∈ v.asIdeal then 1 else 0, Filter.Eventually.of_forall fun v => by
    show (if (q : 𝓞 ℚ) ∈ v.asIdeal then 1 else 0) ∈ v.adicCompletionIntegers ℚ
    split_ifs
    exacts [one_mem _, zero_mem _]⟩
  have hev : ∀ v, e v = if (q : 𝓞 ℚ) ∈ v.asIdeal then 1 else 0 := fun _ => rfl
  have he : e * e = e := FiniteAdeleRing.ext (R := 𝓞 ℚ) ℚ fun v => by
    show e v * e v = e v
    rw [hev]; split_ifs <;> simp
  have hp : ∀ w : Plc E, pLoc E w (finiteAdeleMap ℚ E e) = if (q : 𝓞 E) ∈ w.asIdeal then 1 else 0 := fun w => by
    show GroundTheory.Global.SemiLocal.completionMap (below ℚ w) w (e (below ℚ w)) = _
    have : (q : 𝓞 ℚ) ∈ (below ℚ w).asIdeal ↔ (q : 𝓞 E) ∈ w.asIdeal := by
      show algebraMap (𝓞 ℚ) (𝓞 E) q ∈ w.asIdeal ↔ _
      rw [map_natCast]
    rw [hev]
    by_cases h : (q : 𝓞 E) ∈ w.asIdeal <;> simp [h, this]
  have hσ : conjFin (GlobalTheory.SplitPts.conjE E) (finiteAdeleMap ℚ E e) = finiteAdeleMap ℚ E e :=
    FiniteAdeleRing.ext (R := 𝓞 E) E fun w => by
      have hq : ∀ b : Af E, b w = pLoc E w b := fun _ => rfl
      rw [hq, hq, pLoc_conjFin, hp, hp]
      have := nat_mem_cj q w
      by_cases h : (q : 𝓞 E) ∈ w.asIdeal <;> simp [h, this]
  obtain ⟨π, hπ⟩ := sim_cut (conjFin (GlobalTheory.SplitPts.conjE E)) (finiteAdeleMap ℚ E) n e he hσ
  have hc : ∀ (g : GUf E n) (w : Plc E) a b, (comp w g).val a b = pLoc E w (g.1.1.val a b) := fun _ _ _ _ => rfl
  refine ⟨π, fun g w => ⟨fun h => ?_, fun h => ?_⟩⟩ <;> ext a b <;> rw [hc, hπ]
  · simp [hp, h, hc]
  · by_cases hab : a = b <;> simp [hp, h, hab, Matrix.one_apply]

end UpperTheory.Gal.Int.Geo.Pl
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.ExistsUnitaryGroupDatumOfVectorExponentSpectral

section

@[expose] public section

namespace UpperTheory.Gal.Int.Geo.Pl

theorem tjOK_holds : TjOK := tjOK_of sides_holds dict_holds levBasic_holds

theorem tjIdx_holds : TjIdx := tjIdx_of sides_holds dict_holds levBasic_holds

theorem memEx_holds : MemEx := memEx_of sides_holds dict_holds levBasic_holds

theorem siteTriv_holds : SiteTriv := siteTriv_of sides_holds levBasic_holds

theorem siteEx_holds : SiteEx :=
  siteEx_of sides_holds dict_holds levBasic_holds (stabOf_of nearNbhd_holds primeProj_holds dict_holds)

theorem goodOf_holds : GoodOf :=
  goodOf_of levBasic_holds tjOK_holds (projLev_of dict_holds primeProj_holds levBasic_holds inIdUnit_holds)

theorem congOf_holds : CongOf := congOf_of levBasic_holds tjOK_holds tjIdx_holds

theorem exists_unitaryGroupDatum_of_vector_exponent_spectral (h1 : VecEx) (h2 : ExpOf) (h3 : SpecTop) : PlanEx :=
  planEx_of ⟨frameEx_holds, h1, h3, h2, sides_holds, levBasic_holds, memEx_holds, siteTriv_holds, siteEx_holds, goodOf_holds,
    congOf_holds, datEx_holds, CertificateRingHomMap.rootsAlg_holds, satCard, intCof_holds⟩

end UpperTheory.Gal.Int.Geo.Pl
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.SpecTopG

section

@[expose] public section

theorem UpperTheory.Gal.Spc.specTopG :
    UpperTheory.Gal.Int.Geo.Pl.WtOf → UpperTheory.Gal.Spc.SpecTopG := by
  intro hW E _ _ _ A n p _ S F x U w₀ Up V hodd hsc hgen hoff hq X
  obtain ⟨r, W, hrX, haux⟩ := UpperTheory.Gal.Spc.auxiliary_prime_holds E A n p S x U w₀ Up V hgen X
  refine ⟨r, haux.prime, hrX, haux.ne, ?_⟩
  intro N hrN hst J g θ hseen
  obtain ⟨L, hw, Ty, hTy⟩ := UpperTheory.Gal.Spc.tyEx E A n p S F x U w₀ Up V hoff r W haux N hrN hst
  have hx : UpperTheory.Gal.Spc.Extra S F.j := by
    rw [F.j_tr]
    exact ⟨fun w hp => UpperTheory.Gal.Spc.plTr E A n p S F.tr w hp,
      fun q hq' hqp g hg => UpperTheory.Gal.Spc.regTr E A n p S F.tr q hq' hqp g hg⟩
  exact UpperTheory.Gal.Spc.specData hW E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst
    L hw Ty hTy hx J g θ hseen
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.SpecTopHolds

section

@[expose] public section

namespace UpperTheory.Gal.Int.Geo.Pl

theorem specTop_holds : SpecTop := UpperTheory.Gal.Spc.specTopG wtOf_holds

theorem planEx_holds : PlanEx := exists_unitaryGroupDatum_of_vector_exponent_spectral vecEx_holds expOf_holds specTop_holds

end UpperTheory.Gal.Int.Geo.Pl
end
end
