module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatHeckeCharacterTrivialCongruentUnits
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFFiniteIdeleUpToExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdeleSndSelf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOneOfMemLev
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOneOfNormOneValuationSubOneSmallStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDegreeOneAvoiding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimePlacesSplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOneOfMemLev
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealSubfieldHeckeCharFinitePartEqOneStatement
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmIdeleConjMemCongruenceUnitIdelesConjPlaces

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.HeckeUnrExt
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap ideleConj finiteCompletionMap)

namespace GlobalTheory.HeckeConjLev

theorem ideleMap_mem_levT (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (T : Set (HeightOneSpectrum (𝓞 K))) (T' : Set (HeightOneSpectrum (𝓞 L)))
    (hT : ∀ w ∈ T', w.under (𝓞 K) ∈ T) (N : ℕ) (y : Ideles K) (hy : y ∈ levT K T N) :
    ideleMap K L y ∈ levT L T' N := by
  have hc : ∀ w : HeightOneSpectrum (𝓞 L), (ideleMap K L y).val.2 w =
      finiteCompletionMap K L w (y.val.2 (w.under (𝓞 K))) := fun w => rfl
  refine ⟨fun w => ?_, fun w hw => ?_⟩
  · show Valued.v ((ideleMap K L y).val.2 w) = 1
    have h : Valued.v (y.val.2 (w.under (𝓞 K))) = 1 := hy.1 _
    rw [hc, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, h, one_pow]
  · show Valued.v ((ideleMap K L y).val.2 w - 1) ≤ Valued.v (N : w.adicCompletion L)
    rw [hc, ← map_one (finiteCompletionMap K L w), ← map_sub, ← map_natCast (finiteCompletionMap K L w),
      GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap]
    exact pow_le_pow_left₀ zero_le (hy.2 _ (hT w hw)) _

theorem under_under (F K L : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra F K] [Algebra K L] [Algebra F L]
    (h : ∀ x : F, algebraMap K L (algebraMap F K x) = algebraMap F L x) (w : HeightOneSpectrum (𝓞 L)) :
    (w.under (𝓞 K)).under (𝓞 F) = w.under (𝓞 F) := by
  haveI : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun x => (h x).symm
  exact HeightOneSpectrum.ext (Ideal.under_under w.asIdeal)

theorem ideleConj_mem_levT (E : Type) [Field E] [NumberField E] [IsCMField E]
    (T : Set (HeightOneSpectrum (𝓞 E))) (N : ℕ) (u : Ideles E) (hu : u ∈ levT E T N) :
    ideleConj (maximalRealSubfield E) E u ∈ levT E {w | ∀ w' : HeightOneSpectrum (𝓞 E),
      w'.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → w' ∈ T} N :=
  @ideleMap_mem_levT E E _ _ _ _
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra T
    {w | ∀ w' : HeightOneSpectrum (𝓞 E),
      w'.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → w' ∈ T}
    (fun w hw => hw _ (@under_under (maximalRealSubfield E) E E _ _ _ _ _ _ _
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra _
      (fun x => (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).commutes x) w)) N u hu

end GlobalTheory.HeckeConjLev
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmIdeleConjMemCongruenceUnitIdelesConjPlacesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.HeckeUnrExt
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap ideleConj)

theorem _root_.GlobalTheory.T.cmIdeleConj_mem_congruenceUnitIdeles_conj_places : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (T : Set (HeightOneSpectrum (𝓞 E))) (N : ℕ) (u : Ideles E), u ∈ levT E T N → ideleConj (maximalRealSubfield E) E u ∈ levT E {w | ∀ w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → w' ∈ T} N := by
  first | exact @GlobalTheory.HeckeConjLev.ideleConj_mem_levT | exact GlobalTheory.HeckeConjLev.ideleConj_mem_levT | (intros; apply GlobalTheory.HeckeConjLev.ideleConj_mem_levT <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOtherSplitPlaceWithDistinctRealPlace

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.HeckeUnrExt
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap ideleConj)

namespace GlobalTheory.OtherSplitPlace

theorem exists_isSplitAt_under_ne : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (w₀ : HeightOneSpectrum (𝓞 E)), ∃ w₁ : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w₁ ∧
      w₁.under (𝓞 (maximalRealSubfield E)) ≠ w₀.under (𝓞 (maximalRealSubfield E)) := by
  intro E _ _ _ w₀
  obtain ⟨p, hp, hmp, hs⟩ := GlobalTheory.LargeSplitPrime.exists_splitsCompl E (Ideal.absNorm w₀.asIdeal)
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _

  have hsplit : ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal → GlobalTheory.UnitaryBC.IsSplitAt w := by
    intro w hw
    have hv : (p : 𝓞 (maximalRealSubfield E)) ∈ (w.under (𝓞 (maximalRealSubfield E))).asIdeal := by
      show algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w.asIdeal
      rwa [map_natCast]
    obtain ⟨a, b, hab, ha, hb⟩ :=
      GlobalTheory.SplitPlace.isSplit_of_norm h2 hp (fun u hu => hs u.asIdeal u.isMaximal hu) _ hv
    by_cases h : a = w
    · exact ⟨b, fun e => hab (h.trans e.symm), HeightOneSpectrum.ext hb⟩
    · exact ⟨a, h, HeightOneSpectrum.ext ha⟩

  haveI hPmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hinj : Function.Injective (algebraMap ℤ (𝓞 E)) := (algebraMap ℤ (𝓞 E)).injective_int
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E)
    (Ideal.span {(p : ℤ)}) (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  have hpQ : (p : 𝓞 E) ∈ Q := by
    have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := by
      change (p : ℤ) ∈ Ideal.under ℤ Q
      rw [hQ]
      exact Ideal.subset_span rfl
    simpa using this
  have hp0 : (p : 𝓞 E) ≠ 0 := by exact_mod_cast hp.ne_zero
  let w₁ : HeightOneSpectrum (𝓞 E) := ⟨Q, hQmax.isPrime, fun h => hp0 (by rw [h] at hpQ; simpa using hpQ)⟩
  refine ⟨w₁, hsplit w₁ hpQ, fun heq => ?_⟩

  have hp₀ : (p : 𝓞 E) ∈ w₀.asIdeal := by
    have hv : (p : 𝓞 (maximalRealSubfield E)) ∈ (w₁.under (𝓞 (maximalRealSubfield E))).asIdeal := by
      show algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w₁.asIdeal
      rw [map_natCast]; exact hpQ
    rw [heq] at hv
    have : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w₀.asIdeal := hv
    rwa [map_natCast] at this
  have hN : ((Ideal.absNorm w₀.asIdeal : ℕ) : 𝓞 E) ∈ w₀.asIdeal := Ideal.absNorm_mem _
  have hN0 : 0 < Ideal.absNorm w₀.asIdeal :=
    Nat.pos_of_ne_zero (fun h => w₀.ne_bot (Ideal.absNorm_eq_zero_iff.mp h))
  have hcop : Nat.Coprime p (Ideal.absNorm w₀.asIdeal) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h => absurd (Nat.le_of_dvd hN0 h) (not_le.mpr hmp))
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.mpr hcop).map (Int.castRingHom (𝓞 E))
  apply w₀.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)
  · simpa using hp₀
  · simpa using hN

end GlobalTheory.OtherSplitPlace
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOtherSplitPlaceWithDistinctRealPlaceStatement

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.HeckeUnrExt
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap ideleConj)

theorem _root_.GlobalTheory.T.exists_other_split_place_with_distinct_real_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w₀ : HeightOneSpectrum (𝓞 E)), ∃ w₁ : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w₁ ∧ w₁.under (𝓞 (maximalRealSubfield E)) ≠ w₀.under (𝓞 (maximalRealSubfield E)) := by
  first | exact @GlobalTheory.OtherSplitPlace.exists_isSplitAt_under_ne | exact GlobalTheory.OtherSplitPlace.exists_isSplitAt_under_ne | (intros; apply GlobalTheory.OtherSplitPlace.exists_isSplitAt_under_ne <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicHeckeCharSplit

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section


open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap ideleConj) in
open GlobalTheory.HeckeUnrExt in
theorem GlobalTheory.HeckeUnrExt.exists_ext_unr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar (maximalRealSubfield E)) (b : ℤ), χ.IsAlg (fun _ => b) → (∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal ∧ χ.UnrAt (w.under (𝓞 (maximalRealSubfield E)))) → ∀ w₀ : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w₀ → ∃ (κ : HChar E) (m : (E →+* ℂ) → ℤ), κ.IsAlg m ∧ GlobalTheory.HeightCounting.Blocks.resReal κ = χ ∧ κ.UnrAt w₀ ∧ ∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → κ.UnrAt w := by
  intro E _ _ _ ψ a hψ hns w₀ _
  classical
  obtain ⟨M, hM, hlev⟩ := GlobalTheory.Mem.HeckeLevel.exists_level_nat _ ψ
  obtain ⟨w₁, hw₁s, hw₁⟩ := GlobalTheory.T.exists_other_split_place_with_distinct_real_place E w₀
  set K : ℕ := Module.finrank ℚ E + 1 with hK
  set Q : ℕ := Ideal.absNorm w₁.asIdeal ^ K with hQ
  have hQ0 : 0 < Q := pow_pos (Nat.pos_of_ne_zero fun h => w₁.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)) _
  set N : ℕ := 3 * M * Q with hN
  have hN0 : 0 < N := by positivity
  let T : Set (HeightOneSpectrum (𝓞 E)) := {w | GlobalTheory.UnitaryBC.IsSplitAt w ∧ w ≠ w₀}
  let T' : Set (HeightOneSpectrum (𝓞 E)) := {w | ∀ w' : HeightOneSpectrum (𝓞 E),
      w'.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → w' ∈ T}
  have hw₁T : w₁ ∈ T' := fun w' e => by
    refine ⟨?_, fun h => hw₁ (h ▸ e).symm⟩
    by_cases h : w' = w₁
    · exact h ▸ hw₁s
    · exact ⟨w₁, fun h' => h h'.symm, e.symm⟩
  have hT'T : T' ⊆ T := fun w hw => hw w rfl
  have hF : ∀ b : Ideles (maximalRealSubfield E), ideleMap _ E b ∈ levT E T N → ψ.1 b = kap E a (ideleMap _ E b) := by
    intro b hb
    let z : (InfiniteAdeleRing (maximalRealSubfield E))ˣ := Units.map (MonoidHom.fst _ _) b
    have e : b = Units.map (MonoidHom.inl _ _) z * GlobalTheory.Mem.Chr.finPartI _ b :=
      Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)
    have h1 : ψ.1 (GlobalTheory.Mem.Chr.finPartI _ b) = 1 :=
      GlobalTheory.T.realSubfield_heckeChar_finitePart_eq_one E ψ M hlev (fun w hw => (hns w hw).2) w₀ N ⟨3 * Q, by rw [hN]; ring⟩ b hb
    have h2 : kap E a (ideleMap _ E b) = kap E a (ideleMap _ E (Units.map (MonoidHom.inl _ _) z)) := by
      apply Units.ext
      rw [coe_kap, coe_kap]
      rfl
    rw [h2, ← psi_eq_kap E ψ a hψ z]
    conv_lhs => rw [e, map_mul, h1, mul_one]
  have hprin : ∀ ε : Eˣ, diagUnits E ε ∈ levT E T' N → (∀ φ : E →+* ℂ, ‖φ ε‖ = 1) → ε = 1 := by
    intro ε hε hn
    refine Units.ext (GlobalTheory.T.eq_one_of_norm_one_valuation_sub_one_small E (ε : E) w₁ K (by omega) (fun v => ?_) hn ?_)
    · have e : Valued.v (algebraMap E (v.adicCompletion E) (ε : E)) = 1 := hε.1 v
      rw [GlobalTheory.UpIdeleMod.valued_algebraMap] at e
      exact e.le
    · have e : Valued.v (algebraMap E (w₁.adicCompletion E) (ε : E) - 1) ≤ Valued.v (N : w₁.adicCompletion E) := hε.2 w₁ hw₁T
      rw [← map_one (algebraMap E (w₁.adicCompletion E)), ← map_sub,
        ← map_natCast (algebraMap E (w₁.adicCompletion E)), GlobalTheory.UpIdeleMod.valued_algebraMap,
        GlobalTheory.UpIdeleMod.valued_algebraMap] at e
      refine e.trans ?_
      have eN : ((N : ℕ) : E) = algebraMap (𝓞 E) E ((3 * M : ℕ) : 𝓞 E) * algebraMap (𝓞 E) E ((Q : ℕ) : 𝓞 E) := by
        rw [← map_mul, ← Nat.cast_mul, map_natCast]
      rw [eN, map_mul]
      refine (mul_le_of_le_one_left' (HeightOneSpectrum.valuation_le_one _ _)).trans ?_
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_mem]
      rw [hQ, Nat.cast_pow]
      exact Ideal.pow_mem_pow (Ideal.absNorm_mem w₁.asIdeal) K
  obtain ⟨ξ, hξ⟩ := glue
    (((ideleMap (maximalRealSubfield E) E).coprod (levT E T N).subtype).coprod (diagUnits E))
    ((MonoidHom.coprod ψ.1 ((kap E a).comp (levT E T N).subtype)).coprod 1) (by
      rintro ⟨⟨b, u, hu⟩, k⟩ h
      change ideleMap (maximalRealSubfield E) E b * u * diagUnits E k = 1 at h
      change ψ.1 b * kap E a u * 1 = 1
      let c := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E
      have h' := congrArg (ideleConj (maximalRealSubfield E) E) h
      have c1 : ideleConj (maximalRealSubfield E) E (ideleMap _ E b) = ideleMap _ E b :=
        Units.ext (GlobalTheory.UnitaryHeckeBaseChange.adeleConj_adeleMap _)
      have c2 : ideleConj (maximalRealSubfield E) E (diagUnits E k) =
          diagUnits E (Units.map c.toRingEquiv.toRingHom.toMonoidHom k) :=
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj_principalIdele _ E k
      have c3 : ideleConj (maximalRealSubfield E) E u ∈ levT E T' N := GlobalTheory.T.cmIdeleConj_mem_congruenceUnitIdeles_conj_places E T N u hu
      rw [map_mul, map_mul, map_one, c1, c2, ← h, mul_assoc, mul_assoc, mul_right_inj] at h'
      have h3 : diagUnits E (Units.map c.toRingEquiv.toRingHom.toMonoidHom k / k) =
          u / ideleConj (maximalRealSubfield E) E u := by
        rw [_root_.map_div, div_eq_div_iff_mul_eq_mul, mul_comm, h']
      have h4 := hprin _ (h3 ▸ div_mem (levT_anti E hT'T N hu) c3) fun φ => by
        rw [Units.val_div_eq_div_val, map_div₀, norm_div]
        have : φ (Units.map c.toRingEquiv.toRingHom.toMonoidHom k : Eˣ) = starRingEnd ℂ (φ k) :=
          GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.embedding_conj (maximalRealSubfield E) E φ k
        rw [this, Complex.norm_conj, div_self (by simp)]
      have h5 : IsCMField.complexConj E k = k := congrArg Units.val (div_eq_one.1 h4)
      have h6 : (k : E) ∈ maximalRealSubfield E := (IsCMField.complexConj_eq_self_iff E (k : E)).1 h5
      let k0 : (maximalRealSubfield E)ˣ := Units.mk0 ⟨k, h6⟩ fun h0 => k.ne_zero (congrArg Subtype.val h0)
      have h7 : ideleMap _ E (diagUnits _ k0) = diagUnits E k :=
        (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap_principalIdele _ E k0).trans (congrArg (diagUnits E) (Units.ext rfl))
      have h8 : ideleMap _ E (b * diagUnits _ k0) = u⁻¹ := by
        rw [map_mul, h7, eq_inv_iff_mul_eq_one, mul_right_comm, h]
      have h9 := hF _ (h8 ▸ inv_mem hu)
      rw [h8, map_mul, ψ.2.2, mul_one, map_inv] at h9
      rw [h9, inv_mul_cancel, one_mul])
  have hu : ∀ u ∈ levT E T N, ξ u = kap E a u := fun u hu => by
    simpa using hξ ((1, ⟨u, hu⟩), 1)
  let κ : HChar E := ⟨ξ, ?_, fun k => by simpa using hξ ((1, 1), k)⟩
  swap
  · refine continuous_of_continuousAt_one ξ ((continuous_kap E a).continuousAt.congr ?_)
    filter_upwards [levT_mem_nhds E T (N := N) (by omega)] with x hx
    exact (hu x hx).symm
  have hloc : ∀ w, w ∉ T → κ.UnrAt w := by
    intro w hw x hx
    have hmem : localIdele E w x ∈ levT E T N := by
      refine ⟨fun v => ?_, fun v hv => ?_⟩
      · by_cases hvw : v = w
        · subst hvw
          rw [GlobalTheory.HeckeProduct.localIdele_snd_self]
          exact hx
        · rw [GlobalTheory.HeckeProduct.localIdele_snd_ne E w v hvw]
          exact map_one _
      · have hvw : v ≠ w := fun e => hw (e ▸ hv)
        rw [GlobalTheory.HeckeProduct.localIdele_snd_ne E w v hvw]
        show Valued.v ((1 : v.adicCompletion E) - 1) ≤ _
        rw [sub_self, map_zero]
        exact zero_le
    show ξ (localIdele E w x) = 1
    rw [hu _ hmem]
    apply Units.ext
    rw [kap_of_fst a _ (1 : E) (by rw [GlobalTheory.HeckeProduct.localIdele_fst, map_one])]
    simp
  refine ⟨κ, fun φ => if (InfinitePlace.mk φ).embedding = φ then a else 0, fun k => ?_,
    Subtype.ext (MonoidHom.ext fun b => ?_), hloc w₀ fun h => h.2 rfl, fun w hw => hloc w fun h => hw h.1⟩
  · have h1 : infDiag k ∈ levT E T N := by
      refine lev_le_levT E T N ⟨fun v => ?_, fun v => ?_⟩
      · rw [coe_infDiag']
        exact map_one _
      · rw [coe_infDiag']
        show Valued.v ((1 : v.adicCompletion E) - 1) ≤ _
        rw [sub_self, map_zero]
        exact zero_le
    change ((ξ (infDiag k) : ℂˣ) : ℂ) = _
    rw [hu _ h1, kap_of_fst a _ (k : E) (by rw [coe_infDiag']), prod_type]
  · change ξ (ideleMap _ E b) = ψ.1 b
    simpa using hξ ((b, 1), 1)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicHeckeCharSplitStatement

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

theorem _root_.GlobalTheory.T.exists_algebraic_hecke_char_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar (maximalRealSubfield E)) (b : ℤ), χ.IsAlg (fun _ => b) → (∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal ∧ χ.UnrAt (w.under (𝓞 (maximalRealSubfield E)))) → ∀ w₀ : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w₀ → ∃ (κ : HChar E) (m : (E →+* ℂ) → ℤ), κ.IsAlg m ∧ GlobalTheory.HeightCounting.Blocks.resReal κ = χ ∧ κ.UnrAt w₀ ∧ ∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → κ.UnrAt w := by
  first | exact @GlobalTheory.HeckeUnrExt.exists_ext_unr | exact GlobalTheory.HeckeUnrExt.exists_ext_unr | (intros; apply GlobalTheory.HeckeUnrExt.exists_ext_unr <;> assumption)
end
end
