module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.SphOfWit
public import Formalism.ConjugateSelfDual.Statement
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitChartUniformiserAndResidueCard
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoTame
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseChangeIsomorphicFields
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcPolar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.EmbPadic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExPlaceIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExQuad
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsAlgebraicHeckeCharCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsQuadraticSignCharacter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusEigenvaluesDual
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharSignFixed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PolOfSatOfThetaSat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ThetaSatakeParametersInverse
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.BcAtt0
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.ConjAlgebraMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfBcPolar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocCompC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocCompR
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSatLoc

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormEqNormV

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

namespace GlobalTheory.LiftAbsPow

open GlobalTheory.CuspRep.InfType

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M]

theorem v_map_eq_one {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
    (i : v.adicCompletion K ≃+* w.adicCompletion M) (hi : Continuous i) {x : v.adicCompletion K}
    (hx : Valued.v x = 1) : Valued.v (i x) = 1 := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have h0 : Valued.v (i x) ≠ 0 := by simpa using hx0
  have h1 : Valued.v (i x) ≤ 1 := (GlobalTheory.TypeBlockFix.v_map_le_one_iff v w i hi x).2 hx.le
  have h2 : Valued.v (i x⁻¹) ≤ 1 := (GlobalTheory.TypeBlockFix.v_map_le_one_iff v w i hi _).2 (by rw [map_inv₀, hx, inv_one])
  rw [map_inv₀, map_inv₀] at h2
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (i x) * (Valued.v (i x))⁻¹ := (mul_inv_cancel₀ h0).symm
    _ ≤ Valued.v (i x) * 1 := mul_le_mul' le_rfl h2
    _ = Valued.v (i x) := mul_one _

theorem v_map_unif {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
    (i : v.adicCompletion K ≃+* w.adicCompletion M) (hi : Continuous i) {p : v.adicCompletion K}
    (hp : Valued.v p = WithZero.exp (-1)) : Valued.v (i p) = WithZero.exp (-1) := by
  have hp0 : p ≠ 0 := by rintro rfl; rw [map_zero] at hp; exact WithZero.exp_ne_zero hp.symm
  have hlt : Valued.v (i p) < 1 := (GlobalTheory.TypeBlockFix.v_map_lt_one_iff v w i hi p).2 (by
    rw [hp, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
  have key : ∀ z : w.adicCompletion M, Valued.v z < 1 → Valued.v z ≤ Valued.v (i p) := fun z hz => by
    have hy : Valued.v (i.symm z) < 1 := (GlobalTheory.TypeBlockFix.v_map_lt_one_iff v w i hi _).1 (by simpa using hz)
    rw [GlobalTheory.SplitUnif.lt_one_iff, ← hp] at hy
    have h3 : Valued.v (i.symm z / p) ≤ 1 := by
      rw [map_div₀]
      exact div_le_one_of_le₀ hy zero_le
    have h4 := (GlobalTheory.TypeBlockFix.v_map_le_one_iff v w i hi _).2 h3
    rw [map_div₀, map_div₀, RingEquiv.apply_symm_apply] at h4
    have hip : 0 < Valued.v (i p) := by
      rw [zero_lt_iff]; simpa using hp0
    exact (div_le_one₀ hip).1 h4
  obtain ⟨q, hq⟩ := w.valuation_exists_uniformizer M
  have hq' : Valued.v ((q : M) : w.adicCompletion M) = WithZero.exp (-1) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hq]
  refine le_antisymm ((GlobalTheory.SplitUnif.lt_one_iff _).1 hlt) ?_
  rw [← hq']
  exact key _ (by rw [hq', ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)

theorem v_map_eq {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
    (i : v.adicCompletion K ≃+* w.adicCompletion M) (hi : Continuous i) (x : v.adicCompletion K) :
    Valued.v (i x) = Valued.v x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨p0, hp0⟩ := v.valuation_exists_uniformizer K
  set p : v.adicCompletion K := (p0 : v.adicCompletion K)
  have hp : Valued.v p = WithZero.exp (-1) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hp0]
  have hpne : p ≠ 0 := by rintro h; rw [h, map_zero] at hp; exact WithZero.exp_ne_zero hp.symm
  have hvx : Valued.v x ≠ 0 := by simpa using hx
  set k := WithZero.log (Valued.v x)
  have hk : Valued.v x = WithZero.exp k := (WithZero.exp_log hvx).symm
  obtain ⟨u, hu, e⟩ : ∃ u, Valued.v u = 1 ∧ x = u * (p ^ k)⁻¹ := by
    refine ⟨x * p ^ k, ?_, ?_⟩
    · rw [map_mul, map_zpow₀, hp, hk, ← WithZero.exp_zsmul, ← WithZero.exp_add, smul_eq_mul]
      simp
    · field_simp
  rw [e]
  simp only [map_mul, map_inv₀, map_zpow₀]
  rw [v_map_eq_one i hi hu, hu, v_map_unif i hi hp, hp]

theorem card_residue (v : HeightOneSpectrum (𝓞 K)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) = Ideal.absNorm v.asIdeal := by
  have hF : ∀ s : 𝓞 K, Valued.v (algebraMap K (v.adicCompletion K) s) = v.intValuation s := fun s =>
    (v.valuedAdicCompletion_eq_valuation' _).trans (HeightOneSpectrum.valuation_of_algebraMap v s)
  exact GlobalTheory.SplitUnif.card_residueField v (algebraMap K (v.adicCompletion K)) v (fun _ => rfl) fun s => by
    rw [hF, HeightOneSpectrum.intValuation_lt_one_iff_mem]

theorem absNorm_eq {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
    (i : v.adicCompletion K ≃+* w.adicCompletion M) (hi : Continuous i) :
    Ideal.absNorm v.asIdeal = Ideal.absNorm w.asIdeal := by
  let ψ : v.adicCompletionIntegers K ≃+* w.adicCompletionIntegers M :=
    { toFun := fun a => ⟨i a, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2
        ((v_map_eq i hi a).le.trans ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 a.2))⟩
      invFun := fun b => ⟨i.symm b, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by
        rw [← v_map_eq i hi, RingEquiv.apply_symm_apply]
        exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 b.2)⟩
      left_inv := fun a => Subtype.ext (i.symm_apply_apply a)
      right_inv := fun b => Subtype.ext (i.apply_symm_apply b)
      map_mul' := fun a b => Subtype.ext (map_mul i (a : v.adicCompletion K) (b : v.adicCompletion K))
      map_add' := fun a b => Subtype.ext (map_add i (a : v.adicCompletion K) (b : v.adicCompletion K)) }
  rw [← card_residue v, ← card_residue w]
  exact Nat.card_congr (IsLocalRing.ResidueField.mapEquiv ψ).toEquiv

end GlobalTheory.LiftAbsPow

namespace GlobalTheory.LiftAbsPow

open GlobalTheory.CuspRep.InfType GlobalTheory.HeckeGal.Model

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M]

end GlobalTheory.LiftAbsPow

namespace GlobalTheory.LiftAbsPow

open GlobalTheory.CuspRep.InfType GlobalTheory.HeckeGal.Model

theorem absNorm_eq_normV {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Ideal.absNorm v.asIdeal = normV v := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

end GlobalTheory.LiftAbsPow
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PolarOfLift

section

@[expose] public section




section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Kato.WeilSphericalRecords
private theorem isIrr_comp {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ} {r : Γ →* GL (Fin n) k} {φ : Γ' →* Γ}
    (h : ∀ g, ∃ g', r g = r (φ g')) (hr : IsIrr r) : IsIrr (r.comp φ) :=
  ⟨hr.1, fun _ _ _ => trivial, fun W hW hi => hr.2.2 W hW fun g v hv => by
    obtain ⟨g', e⟩ := h g
    rw [e]
    exact hi g' v hv⟩
private theorem range_of_sign {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω]
    [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (hK : Module.finrank ℚ K = 2) {H : Type} [Group H] {r : G ℚ Ω →* H} {s : G ℚ Ω}
    (hs : s ∉ (Bc.res ℚ Ω K).range) (h1 : r s = 1) (g : G ℚ Ω) : ∃ g', r g = r (Bc.res ℚ Ω K g') := by
  obtain ⟨δ, -, -, ⟨ha, hb⟩, -⟩ := UpperTheory.exists_quadratic_sign_character ℚ K Ω l hK
  by_cases hg : δ g = 1
  · obtain ⟨g', rfl⟩ := (ha g).1 hg
    exact ⟨g', rfl⟩
  · have e : δ (g * s) = 1 := by
      rw [map_mul, (hb g).resolve_left hg, (hb s).resolve_left (mt (ha s).1 hs)]
      simp
    obtain ⟨g', e'⟩ := (ha _).1 e
    exact ⟨g', by rw [e', map_mul, h1, mul_one]⟩
private theorem dualTw_det {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) :
    DualTw r (Matrix.GeneralLinearGroup.det.comp r) := by
  refine ⟨⟨!![0, 1; -1, 0], !![0, -1; 1, 0], ?_, ?_⟩, fun s => ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_fin_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_fin_two]
  · have e : (r s : Matrix (Fin 2) (Fin 2) k) = !![(r s : Matrix (Fin 2) (Fin 2) k) 0 0, (r s : Matrix (Fin 2) (Fin 2) k) 0 1;
        (r s : Matrix (Fin 2) (Fin 2) k) 1 0, (r s : Matrix (Fin 2) (Fin 2) k) 1 1] := Matrix.eta_fin_two _
    simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.val_det_apply, Matrix.coe_units_inv]
    rw [e, Matrix.det_fin_two_of]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
private theorem polar_of_lift (hP : _root_.UpperTheory.V.Af.Hypotheses') {K Ω : Type} [Field K] [NumberField K] [IsCMField K] (hK : Module.finrank ℚ K = 2)
    {l : ℕ} [Fact l.Prime] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω]
    (ι : Qbar l ≃+* ℂ) (r : G ℚ Ω →* GL (Fin 2) (Qbar l)) (wt : ℤ) (θ : G ℚ Ω →* (Qbar l)ˣ) (π : TR.CuspSub ℚ 2)
    (Q : CuspSub K 2) (hBC : Br.IsBC0 π Q) (hC : AttC ι (r.comp (Bc.res ℚ Ω K)) Q) (hθ : IsCycWt l wt θ) (hd : DualTw r θ) :
    ∃ χ, GlobalTheory.ContraPair.PolarizedPair Q χ := by
  haveI : IsScalarTower ℚ (maximalRealSubfield K) Ω := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : IsAlgClosure (maximalRealSubfield K) Ω :=
    ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.trans (maximalRealSubfield K) K Ω⟩
  have hθ' : IsCycWt l (wt + (((2 : ℕ) : ℤ) - 1))
      (θ.comp (Bc.res ℚ Ω (maximalRealSubfield K)) * cycBar (maximalRealSubfield K) Ω l ^ (((2 : ℕ) : ℤ) - 1)) := by
    obtain ⟨M, χ, hM, hχ, rfl⟩ := hθ
    refine ⟨M, χ.comp (Bc.res ℚ Ω (maximalRealSubfield K)), hM, fun s hs => hχ _ hs, ?_⟩
    rw [zpow_add, mul_right_comm]
    rfl
  obtain ⟨hc, χ, art, a, ha⟩ := UpperTheory.exists_algebraic_heckeChar_cyclotomic hP.litN.aut.art _ Ω l ι _ _ hθ'
  have hL : IsLAdicCharOf ι χ _ := ⟨hc, art, a, ha⟩
  obtain ⟨χ', μ', hL', hN, hres, hs⟩ := UpperTheory.heckeChar_sign_fixed K Ω hK l ι χ _ hL 2
  have hres' : μ'.comp (Bc.res (maximalRealSubfield K) Ω K) =
      θ.comp (Bc.res ℚ Ω K) * cycBar K Ω l ^ (((2 : ℕ) : ℤ) - 1) := hres.trans rfl
  refine ⟨χ', hs, UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse hP.litN.aut.js.1 hP.litN.aut.gk K 2 one_le_two Q _ ?_⟩
  have hd' : DualTw (r.comp (Bc.res ℚ Ω K)) (θ.comp (Bc.res ℚ Ω K)) := let ⟨Q, hQ⟩ := hd; ⟨Q, fun s => hQ _⟩
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal :=
    (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  filter_upwards [Bc.normGal K Ω l ι χ' μ' hL', Br.bcConj0 ℚ K 2 π Q hBC, hC.2, hl] with w ⟨hu, he⟩ ⟨B, hB, hB'⟩ ⟨B₁, hB₁, hF⟩ hw
  obtain rfl := hB.unique hB₁
  rw [hres'] at he
  exact ⟨hu, B, B, hB, hB', UpperTheory.frobenius_eigenvalues_dual K Ω l ι 2 _ _ hd' w hw B _ hF he⟩
private theorem qV_eq {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) : Formalism.UG.qV E w = Ideal.absNorm w.asIdeal := by
  rw [Formalism.UG.qV]
private theorem absNorm_rat {l : ℕ} (hp : l.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    Ideal.absNorm v.asIdeal = l := by
  have hN : Ideal.absNorm (Ideal.span {((l : ℕ) : 𝓞 ℚ)}) = l := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one]
  have hd : Ideal.absNorm v.asIdeal ∣ l :=
    hN ▸ Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hv)
  refine ((Nat.dvd_prime hp).1 hd).resolve_left ?_
  rw [Ideal.absNorm_eq_one_iff]
  exact v.isPrime.ne_top
private theorem sat_iff (hP : _root_.UpperTheory.V.Af.Hypotheses') {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Algebra ℚ K]
    (π : TR.CuspSub ℚ 2) (Q : CuspSub K 2) (hBC : IsBC π Q) (v : HeightOneSpectrum (𝓞 ℚ)) (w : HeightOneSpectrum (𝓞 K))
    (i : v.adicCompletion ℚ ≃+* w.adicCompletion K) (hi : IsCompl i) (B : Multiset ℂˣ) :
    π.HasSat v B ↔ (CG.mk Q).HasSat w B := by
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := _root_.UpperTheory.V.Af.local_comp_real_of_printed_results hP ℚ 2 π v
  obtain ⟨⟨σ', hσ'⟩, hiso'⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results hP K 2 Q w
  have hc := hi.1
  obtain ⟨e, he⟩ := hBC.split v w i hi.1 hi.2 σ σ' hσ hσ'
  have c1 := (_root_.UpperTheory.V.Af.satake_local_of_printed_results hP ℚ 2 v σ).2 _ π.finPart (hiso σ hσ) B
  have c2 := (_root_.UpperTheory.V.Af.satake_local_of_printed_results hP K 2 w σ').2 _ Q.finPart (hiso' σ' hσ') B
  have hq : Formalism.UG.qV K w = Formalism.UG.qV ℚ v := by
    rw [qV_eq, qV_eq, GlobalTheory.LiftAbsPow.absNorm_eq i hc]
  refine ⟨fun hB => (CG.hasSat_mk _ _ _).2 (c2.2 (GlobalTheory.IsoPull.hasSatGL_of_ringEquiv i (GlobalTheory.LiftAbsPow.v_map_eq i hc) hq e
    (fun g x => (he g x).symm) (c1.1 hB))), fun hB => c1.2 ?_⟩
  refine GlobalTheory.IsoPull.hasSatGL_of_ringEquiv i.symm (fun y => ?_) hq.symm e.symm (fun g x => ?_) (c2.1 ((CG.hasSat_mk _ _ _).1 hB))
  · have := GlobalTheory.LiftAbsPow.v_map_eq i hc (i.symm y)
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm
  · apply e.injective
    rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]
    congr 2
    exact (Units.ext (Matrix.ext fun _ _ => (i.apply_symm_apply _)) :
      Matrix.GeneralLinearGroup.map i.toRingHom (Matrix.GeneralLinearGroup.map i.symm.toRingHom g) = g)
end UpperTheory.V.Z.Kato.WeilSphericalRecords
theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.base_change_split_of_printed_quad_bc :
    _root_.UpperTheory.V.Af.Hypotheses' → Z.Bc.QuadBC2 → BcSplit := by
  intro hP hQ l _ hl Ω _ _ _ ι V π hr hirr ⟨M, hM, hk⟩ hreg hatt v A hlv hv
  have hθ : IsCycWt l 0 (GlobalTheory.Ord2.dt V) := ⟨M, _, hM, hk, by rw [zpow_zero, one_mul]⟩
  have hd : DualTw V (GlobalTheory.Ord2.dt V) := dualTw_det V
  obtain ⟨K, _, _, _, _, _, _, hK, hemb, v₀, A₀, ⟨B₀, -, hB₀⟩, hA₀, s, hs, hs'⟩ := Cq.exQuad Ω l hl _ hatt.2
  have hI : IsIrr (V.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) :=
    isIrr_comp (range_of_sign l hK hs' ((hB₀ A₀ hA₀).1 s hs)) hirr
  obtain ⟨Q, hBC⟩ := (hQ ℚ K hK π hreg).resolve_left fun ⟨η, hη, ht⟩ => _root_.UpperTheory.V.Af.Bc.noTwist_of_prints hP ℚ K Ω l ι hK 2 V π hr hatt hI η hη ht
  have hBC0 := (Br.IsBCw.of_isBC hBC).toIsBC0
  have hC := Br.bcAtt0 ℚ K Ω l ι 2 V π Q hBC0
  have hA : AttC ι (V.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) Q :=
    hC.2 hatt ((Bc.irrBasic.1 _ Unit _ 2 _).2.1 hI)
  obtain ⟨O, _, _, _, Bw, hj⟩ := exists_bridge (l := l) hv hlv
  have hjK : ∀ x : K, Bw.j (algebraMap K Ω x) ∈ Bw.Kw.1 := fun x => by
    obtain ⟨y, hy⟩ := Cq.embPadic K hK l hemb (Bw.j.comp (algebraMap K Ω)) x
    exact (hy ▸ Bw.Kw.1.algebraMap_mem y :)
  obtain ⟨w, hw, i, hi⟩ := Cq.exPlaceIso ℚ K Ω l A v hv O Bw hj hjK
  refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, Q, w, hK, hI, hC.1 hreg, polar_of_lift hP hK ι V 0 _ π Q hBC0 hA hθ hd, hA, hw, ?_, ?_, ?_,
    fun B => sat_iff hP π Q hBC v w i ⟨hi.cont, hi.loc⟩ B⟩
  · have h1 := (hv ((l : ℕ) : 𝓞 ℚ)).2 hlv
    refine (hw ((l : ℕ) : 𝓞 K)).1 ?_
    simpa using h1
  · rw [← GlobalTheory.LiftAbsPow.absNorm_eq_normV, ← GlobalTheory.LiftAbsPow.absNorm_eq i hi.cont]
    exact absNorm_rat Fact.out v hlv
  · intro g hg x
    apply Bw.j.injective
    have := Bw.e_comm ⟨g, hg⟩ (algebraMap K Ω x)
    rw [← this]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 (Bw.e ⟨g, hg⟩).2 _ (hjK x)
end
end
end
end
