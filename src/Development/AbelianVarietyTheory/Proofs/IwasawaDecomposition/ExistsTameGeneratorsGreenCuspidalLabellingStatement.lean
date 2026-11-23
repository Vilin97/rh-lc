module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseChangeNonempty
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspParamOfGreenParametrisationStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoupledTameInertiaGeneratorStatement
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivariantLabelMapTwistCuspidalLabel
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPlaceIsTeichmullerLiftFbarStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTupleConditionOfIdempotentZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GreenSeriesIdempotentEqClassFunctionIdempotentStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaTwoPlacesOverSamePrimeTrivialMeetStatement
public import Formalism.LocalToGlobal.UnitaryNorms.CharHost
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameInertiaRepresentativeResidue
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapSplit
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivariantLabelMapTwistCuspidalLabelStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.exists_equivariant_labelMap_twist_cuspidalLabel : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv K), Formalism.IrreducibleCountingLemmas.TYPES.CuspParam K C → ∃ O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap K C, Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O ∧ LabTwLawO O ∧ ∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) K)), 1 ≤ d → CategoryTheory.Simple τ → Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ → Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel C τ (O.lab d τ) := by
  first | exact @GlobalTheory.CuspTwist.exists_labelMap_twist_cuspLabel | exact GlobalTheory.CuspTwist.exists_labelMap_twist_cuspLabel | (intros; apply GlobalTheory.CuspTwist.exists_labelMap_twist_cuspLabel <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MuZeroCharLocKCongruentRationalInteger

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.MuZeroCong

theorem locK_eq_of_sub_mem : ∀ {R : Ranks} {H : Host R} (P : PiBar H) (W : Omg H) (e : ↥(R.Psi) → ℚ) (j : ℕ) (χ : HChar H.E), IsMu0 P W e j χ → ∀ (k : Fin 2) (w : HeightOneSpectrum (𝓞 H.E)), P.Div k w → ∀ (u : 𝓞 H.E) (hu : (u : H.E) ≠ 0) (a : ℕ) (ha : a.Coprime (H.g k)), u - (a : 𝓞 H.E) ∈ w.asIdeal → χ.locK w (Units.mk0 (u : H.E) hu) = (W.om k (ZMod.unitOfCoprime a ha) ^ (2 * (j + 1)))⁻¹ := by
  intro R H P W e j χ hχ k w hw u hu a ha hua
  have hg : ((H.g k : ℕ) : 𝓞 H.E) ∈ w.asIdeal := by
    have h1 := P.pb_over k
    rw [← hw, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at h1
    exact h1
  have ha_nm : ((a : ℕ) : 𝓞 H.E) ∉ w.asIdeal := by
    intro haw
    apply w.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have hb := Nat.gcd_eq_gcd_ab a (H.g k)
    rw [Nat.Coprime.gcd_eq_one ha, Nat.cast_one] at hb
    have h1 : (1 : 𝓞 H.E) = ((a : ℕ) : 𝓞 H.E) * ((Nat.gcdA a (H.g k) : ℤ) : 𝓞 H.E)
        + ((H.g k : ℕ) : 𝓞 H.E) * ((Nat.gcdB a (H.g k) : ℤ) : 𝓞 H.E) := by
      have := congrArg (Int.cast : ℤ → 𝓞 H.E) hb
      push_cast at this
      exact this
    rw [h1]
    exact add_mem (Ideal.mul_mem_right _ _ haw) (Ideal.mul_mem_right _ _ hg)
  have hu_nm : u ∉ w.asIdeal := by
    intro huw
    apply ha_nm
    have := Ideal.sub_mem _ huw hua
    simpa using this
  have ha0 : ((a : ℕ) : H.E) ≠ 0 := by
    intro h0
    apply ha_nm
    have : ((a : ℕ) : 𝓞 H.E) = 0 := by
      apply RingOfIntegers.coe_injective
      push_cast
      exact h0
    rw [this]
    exact zero_mem _
  set A : H.Eˣ := Units.mk0 ((a : ℕ) : H.E) ha0 with hA
  set U : H.Eˣ := Units.mk0 (u : H.E) hu with hU
  have hsplit : U = (U * A⁻¹) * A := by group
  have hval : ∀ r : 𝓞 H.E, Valued.v (((r : H.E)) : w.adicCompletion H.E) = w.intValuation r := by
    intro r
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact w.valuation_of_algebraMap r
  have hYval : ((U * A⁻¹ : H.Eˣ) : H.E) = (u : H.E) * ((a : ℕ) : H.E)⁻¹ := by
    simp [hA, hU]
  have hvu : w.intValuation u = 1 := (w.intValuation_eq_one_iff_mem_primeCompl u).mpr hu_nm
  have hva : w.intValuation ((a : ℕ) : 𝓞 H.E) = 1 :=
    (w.intValuation_eq_one_iff_mem_primeCompl _).mpr ha_nm
  have hvd : w.intValuation (u - ((a : ℕ) : 𝓞 H.E)) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    rw [w.intValuation_le_pow_iff_mem, pow_one]
    exact hua
  have hacoe : (((a : ℕ) : 𝓞 H.E) : H.E) = ((a : ℕ) : H.E) := by push_cast; rfl
  have hv' : ∀ x : H.E, Valued.v (algebraMap H.E (w.adicCompletion H.E) x) = w.valuation H.E x :=
    fun x => w.valuedAdicCompletion_eq_valuation' x
  have hY1 : χ.locK w (U * A⁻¹) = 1 := by
    show χ.loc w (atFin w (U * A⁻¹)) = 1
    apply hχ.tame w
    · show Valued.v (algebraMap H.E (w.adicCompletion H.E) ((U * A⁻¹ : H.Eˣ) : H.E)) = 1
      rw [hv', hYval, Valuation.map_mul, Valuation.map_inv, ← hacoe]
      rw [show (u : H.E) = algebraMap (𝓞 H.E) H.E u from rfl,
        show (((a : ℕ) : 𝓞 H.E) : H.E) = algebraMap (𝓞 H.E) H.E ((a : ℕ) : 𝓞 H.E) from rfl,
        w.valuation_of_algebraMap, w.valuation_of_algebraMap, hvu, hva, inv_one, mul_one]
    · show Valued.v (algebraMap H.E (w.adicCompletion H.E) ((U * A⁻¹ : H.Eˣ) : H.E) - 1) ≤ _
      rw [← map_one (algebraMap H.E (w.adicCompletion H.E)), ← map_sub, hv', hYval]
      have hq : (u : H.E) * ((a : ℕ) : H.E)⁻¹ - 1
          = algebraMap (𝓞 H.E) H.E (u - ((a : ℕ) : 𝓞 H.E)) * (algebraMap (𝓞 H.E) H.E ((a : ℕ) : 𝓞 H.E))⁻¹ := by
        rw [map_sub, map_natCast]
        field_simp
      rw [hq, Valuation.map_mul, Valuation.map_inv, w.valuation_of_algebraMap, w.valuation_of_algebraMap, hva,
        inv_one, mul_one]
      exact hvd
  have hAv := hχ.atg k w hw a ha A rfl
  rw [hsplit, map_mul, hY1, one_mul, hAv]

end GlobalTheory.MuZeroCong
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MuZeroCharLocKCongruentRationalIntegerStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.muZeroChar_locK_congruent_rational_integer : ∀ {R : Ranks} {H : Host R} (P : PiBar H) (W : Omg H) (e : ↥(R.Psi) → ℚ) (j : ℕ) (χ : HChar H.E), IsMu0 P W e j χ → ∀ (k : Fin 2) (w : HeightOneSpectrum (𝓞 H.E)), P.Div k w → ∀ (u : 𝓞 H.E) (hu : (u : H.E) ≠ 0) (a : ℕ) (ha : a.Coprime (H.g k)), u - (a : 𝓞 H.E) ∈ w.asIdeal → χ.locK w (Units.mk0 (u : H.E) hu) = (W.om k (ZMod.unitOfCoprime a ha) ^ (2 * (j + 1)))⁻¹ := by
  first | exact @GlobalTheory.MuZeroCong.locK_eq_of_sub_mem | exact GlobalTheory.MuZeroCong.locK_eq_of_sub_mem | (intros; apply GlobalTheory.MuZeroCong.locK_eq_of_sub_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameInertiaRepresentativeResidueStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.tameInertia_representative_residue : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)) (g : ℕ) [Fact g.Prime], IsPlaceOver (F := E) A P → normV P = g → ((g : ℕ) : 𝓞 E) ∈ P.asIdeal → ((g : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → ∀ (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (σ : G E Ω) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g), σ ∈ Ine (F := E) A → IsGenSys ζ → TameCoupled A κ σ ζ → (∀ A' : ValuationSubring Ω, IsPlaceOver (F := E) A' P → σ ∈ Ine (F := E) A' → σ ≠ 1 → A' = A) → ∀ u : 𝓞 E, NX.TameRep P 1 σ u → ∃ a : ℕ, a.Coprime g ∧ u - (a : 𝓞 E) ∈ P.asIdeal ∧ algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (a : ZMod g) = ζ 1 := by
  first | exact @GlobalTheory.tameRep_residue | exact GlobalTheory.tameRep_residue | (intros; apply GlobalTheory.tameRep_residue <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTameGeneratorsGreenCuspidalLabelling

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting.TameGrp

theorem isGenSys_gen {g : ℕ} [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) : IsGenSys L.gen := by
  intro d hd
  refine ⟨L.gen_order d hd, fun d' hdd hd' => ?_⟩
  obtain ⟨e, rfl⟩ := hdd
  have he : 0 < e := Nat.pos_of_mul_pos_left hd'
  exact L.gen_norm d e hd he

theorem prod_rootsBar_X_sub_one_pow {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (n : ℕ) :
    ((Formalism.CyclotomicNorms.rootsBar ((X - 1 : (ZMod g)[X]) ^ n)).map fun x => X - Polynomial.C (t x)).prod = (X - 1 : ℂ[X]) ^ n := by
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one, Polynomial.roots_pow,
    ← Polynomial.C_1, Polynomial.roots_X_sub_C, Multiset.map_nsmul, Multiset.prod_nsmul, Multiset.map_singleton,
    Multiset.prod_singleton, map_one, Polynomial.C_1]




theorem exists_tame_generators_cuspidal_labelling : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D), (∀ j g, ∃ z : ℤ, eExp D j g = z) → GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W → ∃ (L : Lay0 D) (hZ : L.ZOk) (hη : L.EtaOk), IsEmpty L.nd.Loc ∧ GlobalTheory.Mem.Top.TypesTrue L.ntypes cf.P cf.W ∧ L.nd.PlG = D.nd.PlG ∧ HEq L.naut.plGw D.naut.plGw ∧ HEq L.ntypes.cenAmb D.ntypes.cenAmb ∧ HEq L.ntypes.cenMt D.ntypes.cenMt ∧ (∃ Gs : GrpSide (setK D L hZ hη), ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; Gs.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen) ∧ ChiTOk (setK D L hZ hη) (cfK L hZ hη cf) ∧ L.loc = D.loc ∧ HEq (@NData.Om _ _ _ L.nd) (@NData.Om _ _ _ D.nd) ∧ HEq (@NData.instOm _ _ _ L.nd) (@NData.instOm _ _ _ D.nd) ∧ HEq (@NData.algOm _ _ _ L.nd) (@NData.algOm _ _ _ D.nd) ∧ HEq (@NData.plOm _ _ _ L.nd) (@NData.plOm _ _ _ D.nd) := by
  intro hG _ D hE cf _ hT
  haveI : IsEmpty D.nd.Loc := hE

  have htame : ∀ k (v : D.nd.PlG k), haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      ∃ κ : IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k),
        ∃ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)),
          TameGenAt (D.nd.plOm.1 (D.naut.plGw k v)) σ ∧
            TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) κ σ (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen := by
    intro k v
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    haveI := D.nd.acOm
    exact GlobalTheory.T.exists_coupled_tame_inertia_generator D.host.E D.nd.Om (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) (D.nd.plOm.2 _)
      (D.host.g k) (D.naut.plGw_over k v)
      (Formalism.MainNotions.Gaps.LevGap.natCast_notMem_sq_of_split _ (D.host.g_prime k) (D.nd.g_split k) _ (D.naut.plGw_over k v))
      _ (isGenSys_gen _)
  choose kv tg tg_mem tg_gen tg_coup using htame

  let N1 := ndLab D.nd D.nd.lab D.nd.lab_monic
  haveI : IsEmpty N1.Loc := hE
  let A : NAut N1 := GlobalTheory.Mem.GaloisStage.nAut N1 D.naut.plGw D.naut.plGw_over D.naut.plGw_inj D.naut.plGw_nconj
  obtain ⟨C⟩ := GlobalTheory.MemN.nonempty_nbc_of_isEmpty_loc _ _ _ N1 A hE
  have hl1 : ∀ k v (L : A.LP (A.plGw k v)), (A.items₂ k (A.plGw k v) L).natDegree = A.lpDim L →
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      A.inePol L (D.ntypes.tg k v) =
        ((Formalism.CyclotomicNorms.rootsBar (A.items₂ k (A.plGw k v) L)).map fun x => X - Polynomial.C (D.ntypes.teichC k x)).prod :=
    fun k v L _ => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      (prod_rootsBar_X_sub_one_pow (D.ntypes.teichC k) _).symm
  let D1 := setAut D hE D.nd.lab D.nd.lab_monic A C D.ntypes.tg_mem D.ntypes.tg_gen hl1
  let X1 : NTypes D1.naut :=
    { D1.ntypes with
      tg := tg
      tg_mem := tg_mem
      tg_gen := tg_gen
      heckeLoc_gamma_places := fun i => hE.elim i
      inertiaCharpoly_type := fun k v L _ => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
        (prod_rootsBar_X_sub_one_pow (D.ntypes.teichC k) _).symm
      chiT_tg := fun i => hE.elim i }
  let D2 := setTy D1 hE X1 D1.nStage_trivialCharacter_compat D1.nStage_trivialCharacter_coeff_eq
  let L : Lay0 D := lay0 D2
  have hZ : L.ZOk := ⟨fun i => hE.elim i, fun i => hE.elim i⟩
  have hη : L.EtaOk := D.etaJ_tie
  refine ⟨L, hZ, hη, hE, ⟨hT.pl, hT.teich, hT.chi, hT.ser⟩, rfl, HEq.rfl, HEq.rfl, HEq.rfl, ?_, ?_, rfl,
    HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
  · have hteich := fun k => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      GlobalTheory.T.exists_place_isTeichmuller_lift_Fbar (D.host.g k) (D.ntypes.teichC k) (D.ntypes.teichC_inj k)
    choose tA tκ hTe using hteich
    have hlab : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
        ∃ O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k))
          (convC (D.ntypes.teichC k) (D.ntypes.teichC_inj k) (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen (isGenSys_gen _)),
          Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O ∧ LabTwLawO O ∧
            ∀ f, D.ntypes.eSer k f = eSerO O D.R.r f := by
      intro k
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      obtain ⟨O, hO1, hO2, hO3⟩ := GlobalTheory.T.exists_equivariant_labelMap_twist_cuspidalLabel (ZMod (D.host.g k)) _
        (GlobalTheory.T.cuspParam_of_greenParametrisation hG (D.host.g k) (D.ntypes.teichC k) (D.ntypes.teichC_inj k)
          (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen (isGenSys_gen _))
      have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
      exact ⟨O, hO1, hO2, fun f => (hT.ser k f).trans
        (GlobalTheory.T.greenSeriesIdempotent_eq_classFunctionIdempotent hG _ _ _ _ _ (hT.teich k) O hO3 D.R.r f hr)⟩
    choose O hOe hOt hOs using hlab
    exact ⟨{ tA := tA, tκ := tκ, teichC_def := hTe
             ζ := fun k => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen
             ζ_gen := fun k => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; isGenSys_gen _
             O := O, eSer_def := hOs, kv := kv, tg_tame := tg_coup, O_equiv := hOe, O_tw := hOt }, fun _ => rfl⟩
  · intro k v j u hu hrep
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    haveI := D.nd.acOm
    have hP := D.nd.plOm.2 (D.naut.plGw k v)
    obtain ⟨a, ha, hua, hga⟩ := GlobalTheory.T.tameInertia_representative_residue D.host.E D.nd.Om (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v)
      (D.host.g k) hP (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) (D.naut.plGw_over k v))
      (D.naut.plGw_over k v)
      (Formalism.MainNotions.Gaps.LevGap.natCast_notMem_sq_of_split _ (D.host.g_prime k) (D.nd.g_split k) _ (D.naut.plGw_over k v))
      (kv k v) (tg k v) _ (tg_mem k v) (isGenSys_gen _) (tg_coup k v)
      (fun A' hA' hσ hne => GlobalTheory.T.inertia_two_places_over_same_prime_trivial_meet D.host.E D.nd.Om _ _ _ hP hA' (tg k v) (tg_mem k v) hσ hne) u hrep
    refine ⟨(D.nd.chiT k v j)⁻¹, Or.inr rfl, ?_⟩
    change ((((cf.mu0 j).locK (D.naut.plGw k v)) (Units.mk0 (((show 𝓞 D.host.E from u) : 𝓞 D.host.E) : D.host.E) hu) : ℂˣ) : ℂ) =
      (D.ntypes.teichC k) ((algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)))
        (((D.nd.chiT k v j)⁻¹ : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)))
    rw [GlobalTheory.T.muZeroChar_locK_congruent_rational_integer cf.P cf.W _ _ _ (cf.isMu0 j) k _ (hT.pl k v) u hu a ha hua, hT.teich k, hT.chi k v j]
    have hlabel := (GlobalTheory.Mem.Top.isCharLab_omLab cf.W k).2 (ZMod.unitOfCoprime a ha) (by simpa using hga)
    have key : ∀ z : Formalism.CyclotomicNorms.Fbar (D.host.g k), z ≠ 0 →
        (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).teich z⁻¹ = ((GlobalTheory.Mem.TypePl.labDat (D.host.g k)).teich z)⁻¹ :=
      fun z hz => eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel₀ hz, map_one])
    rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, hlabel, Units.val_inv_eq_inv_val, map_inv₀, key _ (by
      rw [Units.val_pow_eq_pow_val, map_pow]
      exact pow_ne_zero _ ((_root_.map_ne_zero _).2 (Units.ne_zero _))), Units.val_pow_eq_pow_val, map_pow, map_pow]

end GlobalTheory.HeightCounting.TameGrp

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTameGeneratorsGreenCuspidalLabellingStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.exists_tame_generators_green_cuspidal_labelling : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D), (∀ j g, ∃ z : ℤ, eExp D j g = z) → GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W → ∃ (L : Lay0 D) (hZ : L.ZOk) (hη : L.EtaOk), IsEmpty L.nd.Loc ∧ GlobalTheory.Mem.Top.TypesTrue L.ntypes cf.P cf.W ∧ L.nd.PlG = D.nd.PlG ∧ HEq L.naut.plGw D.naut.plGw ∧ HEq L.ntypes.cenAmb D.ntypes.cenAmb ∧ HEq L.ntypes.cenMt D.ntypes.cenMt ∧ (∃ Gs : GrpSide (setK D L hZ hη), ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; Gs.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen) ∧ ChiTOk (setK D L hZ hη) (cfK L hZ hη cf) ∧ L.loc = D.loc ∧ HEq (@NData.Om _ _ _ L.nd) (@NData.Om _ _ _ D.nd) ∧ HEq (@NData.instOm _ _ _ L.nd) (@NData.instOm _ _ _ D.nd) ∧ HEq (@NData.algOm _ _ _ L.nd) (@NData.algOm _ _ _ D.nd) ∧ HEq (@NData.plOm _ _ _ L.nd) (@NData.plOm _ _ _ D.nd) := by
  first | exact @GlobalTheory.HeightCounting.TameGrp.exists_tame_generators_cuspidal_labelling | exact GlobalTheory.HeightCounting.TameGrp.exists_tame_generators_cuspidal_labelling | (intros; apply GlobalTheory.HeightCounting.TameGrp.exists_tame_generators_cuspidal_labelling <;> assumption)
end
end
