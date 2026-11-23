module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaCmType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormGroupIffEverywhereNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmQuadraticCharacterEqProdRealSigns
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeUnitPhaseProdEqOneOfCongruentOneStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenIdeleSubgroupCongruenceModQStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHeckeCharacterPhaseTypeCm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianEvaluationTranslation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCongruenceKernelIdeleCharacterTrivialAtInfStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHeckeCharacterExtendingBaseCharacte
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIntegralTensorAdeleMultiplesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensorCongruenceOfSupportedAtInfinityStatement

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EtaEqProdSignK

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
namespace GlobalTheory.EtaSignReal
open GlobalTheory.QuadSymbol GlobalTheory.IdeleNormChar GlobalTheory.AdelicU
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem eta_eq_prod_sign_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ η : (AF F)ˣ →* Circle, IsEtaF E η → ∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) →
      (η a : ℂ) = ∏ w, piInf (B.emb w) ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) /
        ((‖piInf (B.emb w) ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)‖ : ℝ) : ℂ) := by
  intro F E _ _ _ _ _ σ B hB η hη a ha
  have hcm := hB.cm
  haveI : Algebra.IsQuadraticExtension F E := ⟨hcm.2.2.1⟩
  haveI := hcm.1
  rw [eq_signToCircle η hη, MonoidHom.comp_apply, normSign_eq_prod (finComp_eq_one ha), map_prod]
  rw [show ((∏ w : InfinitePlace F, signToCircle (eta F E w.Completion (infComp a w)) : Circle) : ℂ) =
      ∏ w : InfinitePlace F, ((signToCircle (eta F E w.Completion (infComp a w)) : Circle) : ℂ) from
    map_prod Circle.coeHom _ _]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hw : w.IsReal := IsTotallyReal.isReal w
  rw [piInf_idFF hw]
  set r := InfinitePlace.Completion.ringEquivRealOfIsReal hw ((infComp a w : (w.Completion)ˣ) : w.Completion)
  have hx := mem_normGroup_iff_pos hcm hw (B.emb w) (infComp a w)
  have hr0 : r ≠ 0 := (map_ne_zero _).2 (infComp a w).ne_zero
  rw [Complex.norm_real, Real.norm_eq_abs]
  by_cases hpos : 0 < r
  · rw [eta_eq_one_iff.2 (hx.2 hpos), map_one, abs_of_pos hpos, div_self (by exact_mod_cast hr0)]
    rfl
  · have hneg : r < 0 := lt_of_le_of_ne (not_lt.1 hpos) hr0
    rw [eta_eq_neg_one_iff.2 (fun h => hpos (hx.1 h)), abs_of_neg hneg]
    change ((if (-1 : ℤˣ) = 1 then (1 : Circle) else -1 : Circle) : ℂ) = _
    rw [if_neg (by decide)]
    push_cast
    rw [div_neg, div_self (by exact_mod_cast hr0)]
end GlobalTheory.EtaSignReal
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EtaCharacterArchimedeanFormula

section

@[expose] public section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

theorem _root_.GlobalTheory.T.eta_character_archimedean_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ η : (AF F)ˣ →* Circle, IsEtaF E η → ∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) →
      (η a : ℂ) = ∏ w, piInf (B.emb w) ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) /
        ((‖piInf (B.emb w) ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)‖ : ℝ) : ℂ) := by
  first | exact @_root_.GlobalTheory.EtaSignReal.eta_eq_prod_sign_k | exact _root_.GlobalTheory.EtaSignReal.eta_eq_prod_sign_k | (intros; apply _root_.GlobalTheory.EtaSignReal.eta_eq_prod_sign_k <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsWeilCharK

section

@[expose] public section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.WeilTypeChar
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem exists_weil_char_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∃ ξ : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF ξ ∧ HasExp B.emb ξ (fun _ => 1) := by
  intro F E _ _ _ _ _ σ B hB
  haveI : IsCMField E := isCMField_of_cmExt hB.cm
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨q, hq1, hq⟩ := Nat.exists_infinite_primes (max 3 (Nat.card (Units.torsion E) + 1))
  have hq2 : 2 < q := by omega
  have htq : Nat.card (Units.torsion E) < q := by omega
  have ht : ¬ q ∣ Nat.card (Units.torsion E) := fun h => absurd (Nat.le_of_dvd Nat.card_pos h) (by omega)
  obtain ⟨U, hU, hUinf, hUk⟩ := GlobalTheory.T.exists_open_idele_subgroup_congruence_mod_q F E q hq.ne_zero
  obtain ⟨χ, hχc, hχ1, hχU, hχk⟩ := GlobalTheory.exists_unitary_char_of_open_subgroup_and_hom (AF F ⊗[F] E)ˣ Eˣ U hU
    (Units.map (incAF F E).toMonoidHom) 1 (chiInf B.emb) (continuous_chiInf B.emb) (norm_chiInf B.emb)
    (fun _ => by simp) (fun k hk => by
      obtain ⟨u, hu, hu1⟩ := hUk k hk
      refine Units.ext ?_
      rw [chiInf_apply, MonoidHom.one_apply, Units.val_one]
      have e : ∀ w, piInf (B.emb w) ((Units.map (incAF F E).toMonoidHom k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
          (B.emb w).1 ((u : 𝓞 E) : E) := fun w => by
        rw [hu]
        exact GlobalTheory.ThK.EvAt0.ZPartArc.piInf_inclR' (B.emb w) (k : E)
      simp only [e]
      exact (GlobalTheory.T.cmType_unit_phase_prod_eq_one_of_congruent_one F E σ hB.cm B.emb q hq hq2 ht u hu1).symm)
  refine ⟨GlobalTheory.unitaryCharToCircle χ hχ1, ⟨?_, fun k => ?_⟩, fun z hz => ?_⟩
  · exact Continuous.subtype_mk (Units.continuous_val.comp hχc) _
  · apply Circle.ext
    show ((χ (Units.map (incAF F E).toMonoidHom k) : ℂˣ) : ℂ) = 1
    rw [hχk]; rfl
  · show ((χ z : ℂˣ) : ℂ) = _
    rw [hχU z (hUinf z hz), chiInf_apply]
    simp
end GlobalTheory.WeilTypeChar
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsHeckeCharacterTrivialExponent

section

@[expose] public section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

theorem _root_.GlobalTheory.T.exists_hecke_character_trivial_exponent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∃ ξ : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF ξ ∧ HasExp B.emb ξ (fun _ => 1) := by
  first | exact @_root_.GlobalTheory.WeilTypeChar.exists_weil_char_k | exact _root_.GlobalTheory.WeilTypeChar.exists_weil_char_k | (intros; apply _root_.GlobalTheory.WeilTypeChar.exists_weil_char_k <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsExtendHeckeK

section

@[expose] public section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open GlobalTheory.HeckeExtend
noncomputable section
namespace GlobalTheory.HeckeExtend
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem exists_extend_hecke_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ lam : (AF F)ˣ →* Circle, Continuous lam →
      (∀ a : Fˣ, lam (Units.map (algebraMap F (AF F)).toMonoidHom a) = 1) →
      (∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) → lam a = 1) →
      ∃ lam' : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF lam' ∧
        (∀ z : (AF F ⊗[F] E)ˣ, At (evI F) ((z : AF F ⊗[F] E) - 1) → lam' z = 1) ∧
        ∀ a, lam' (idFF F E a) = lam a := by
  intro F E _ _ _ _ _ σ B hB lam hc h1 hinf
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨M, hM, hMk⟩ := GlobalTheory.T.exists_congruence_kernel_ideleCharacter_trivialAtInfinity F lam hc hinf
  let V : Subgroup (AF F ⊗[F] E)ˣ := (Units.map (incAF F E).toMonoidHom).range ⊔ WE F E (8 * M)
  have hkey : ∀ a : (AF F)ˣ, idFF F E a ∈ V → lam a = 1 := key σ hB.cm M hM lam h1 hMk
  have hN : 0 < 8 * M := by positivity
  have hWo : IsOpen (WE F E (8 * M) : Set (AF F ⊗[F] E)ˣ) := by
    have ho := GlobalTheory.T.isOpen_integralTensorAdeleMultiples F E (8 * M) hN
    have hcv : Continuous fun z : (AF F ⊗[F] E)ˣ => (z : AF F ⊗[F] E) - 1 :=
      Units.continuous_val.sub continuous_const
    have hci : Continuous fun z : (AF F ⊗[F] E)ˣ => ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 :=
      Units.continuous_coe_inv.sub continuous_const
    exact (ho.preimage hcv).inter (ho.preimage hci)
  have hVo : IsOpen (V : Set (AF F ⊗[F] E)ˣ) := Subgroup.isOpen_mono le_sup_right hWo
  let ψ0 : (AF F)ˣ →* (AF F ⊗[F] E)ˣ ⧸ V := (QuotientGroup.mk' V).comp (idFF F E)
  have hker : ψ0.ker ≤ lam.ker := fun a ha => hkey a ((QuotientGroup.eq_one_iff _).1 ha)
  letI : DivisibleBy (Additive Circle) ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn u => by
    obtain ⟨t, ht⟩ := Circle.exp_surjective u.toMul
    refine ⟨Additive.ofMul (Circle.exp (t / n)), ?_⟩
    show Additive.ofMul (Circle.exp (t / n) ^ n) = u
    rw [← Circle.exp_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hn), ht]
    rfl
  letI : DivisibleBy (Additive Circle) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨ρ, hρ⟩ := (Module.Baer.of_divisible (Additive Circle)).extension_property_addMonoidHom
    (MonoidHom.toAdditive (QuotientGroup.kerLift ψ0)) (QuotientGroup.kerLift_injective ψ0)
    (MonoidHom.toAdditive (QuotientGroup.lift ψ0.ker lam hker))
  let κ : (AF F ⊗[F] E)ˣ ⧸ V →* Circle := MonoidHom.toAdditive.symm ρ
  have hκ : ∀ x, κ (QuotientGroup.kerLift ψ0 x) = QuotientGroup.lift ψ0.ker lam hker x :=
    fun x => DFunLike.congr_fun hρ (Additive.ofMul x)
  have hV1 : ∀ z ∈ V, κ.comp (QuotientGroup.mk' V) z = 1 := fun z hz => by
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).2 hz, map_one]
  refine ⟨κ.comp (QuotientGroup.mk' V), ⟨?_, fun x => hV1 _ (le_sup_left (a := (Units.map (incAF F E).toMonoidHom).range)
    ⟨x, rfl⟩)⟩, fun z hz => hV1 z (le_sup_right (a := (Units.map (incAF F E).toMonoidHom).range) ?_), fun a => hκ (a : (AF F)ˣ ⧸ ψ0.ker)⟩
  · refine continuous_of_continuousAt_one _ ?_
    unfold ContinuousAt
    rw [map_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hVo.mem_nhds (one_mem V)] with z hz
    exact (hV1 z hz).symm
  · have hN' := hN
    refine ⟨GlobalTheory.T.mem_tensorCongruence_of_supported_at_infinity F E _ hN' _ hz, GlobalTheory.T.mem_tensorCongruence_of_supported_at_infinity F E _ hN' _ ?_⟩
    intro u hu
    have e : ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 = -(((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * ((z : AF F ⊗[F] E) - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
    rw [e, smul_neg, ← mul_smul_comm, hz u hu, mul_zero, neg_zero]
end GlobalTheory.HeckeExtend
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExtendCharacterToNormGroup

section

@[expose] public section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

theorem _root_.GlobalTheory.T.extend_character_to_norm_group : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ lam : (AF F)ˣ →* Circle, Continuous lam →
      (∀ a : Fˣ, lam (Units.map (algebraMap F (AF F)).toMonoidHom a) = 1) →
      (∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) → lam a = 1) →
      ∃ lam' : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF lam' ∧
        (∀ z : (AF F ⊗[F] E)ˣ, At (evI F) ((z : AF F ⊗[F] E) - 1) → lam' z = 1) ∧
        ∀ a, lam' (idFF F E a) = lam a := by
  first | exact @_root_.GlobalTheory.HeckeExtend.exists_extend_hecke_k | exact _root_.GlobalTheory.HeckeExtend.exists_extend_hecke_k | (intros; apply _root_.GlobalTheory.HeckeExtend.exists_extend_hecke_k <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsEtaCmTypeK

section

@[expose] public section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.EtaCMType
theorem exists_eta_cmType_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∃ η : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF η ∧ ResEtaF η 1 ∧ HasExp B.emb η (fun _ => 1) := by
  intro F E _ _ _ _ _ σ B hB
  obtain ⟨ξ, hξ, hξe⟩ := _root_.GlobalTheory.T.exists_hecke_character_trivial_exponent F E σ B hB
  obtain ⟨η₀, hη₀, huniq⟩ := GlobalTheory.IdeleNormChar.globalNormIndexTwo F E hB.cm.2.2.1
  have hη₀' : IsEtaF E η₀ := hη₀
  let lam : (AF F)ˣ →* Circle := ξ.comp (idFF F E) * η₀⁻¹
  have hlam : ∀ a, lam a = ξ (idFF F E a) * (η₀ a)⁻¹ := fun a => rfl
  have hlc : Continuous lam := by
    have : Continuous fun a => ξ (idFF F E a) * (η₀ a)⁻¹ :=
      (hξ.1.comp continuous_idFF).mul (hη₀.1.inv)
    exact this
  have hlF : ∀ a : Fˣ, lam (Units.map (algebraMap F (AF F)).toMonoidHom a) = 1 := by
    intro a
    rw [hlam, idFF_rat, hξ.2, hη₀.2.1, inv_one, one_mul]
  have hlinf : ∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) → lam a = 1 := by
    intro a ha
    have e1 := hξe _ (at_idFF a ha)
    have e2 := _root_.GlobalTheory.T.eta_character_archimedean_formula F E σ B hB η₀ hη₀' a ha
    have e3 : ξ (idFF F E a) = η₀ a := by
      apply Circle.ext
      rw [e1, e2]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [zpow_one]
    rw [hlam, e3, mul_inv_cancel]
  obtain ⟨lam', hl'H, hl'inf, hl'res⟩ := _root_.GlobalTheory.T.extend_character_to_norm_group F E σ B hB lam hlc hlF hlinf
  refine ⟨ξ * lam'⁻¹, ⟨hξ.1.mul hl'H.1.inv, fun x => ?_⟩, ⟨⟨η₀, hη₀'⟩, fun η hη a => ?_⟩, fun z hz => ?_⟩
  · change ξ _ * (lam' _)⁻¹ = 1
    rw [hξ.2, hl'H.2, inv_one, one_mul]
  · change ξ _ * (lam' _)⁻¹ = _
    rw [huniq η hη, hl'res, hlam, pow_one, mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel_comm]
  · change ((ξ z * (lam' z)⁻¹ : Circle) : ℂ) = _
    rw [hl'inf z hz, inv_one, mul_one]
    exact hξe z hz
end GlobalTheory.EtaCMType
end
end
end
end
