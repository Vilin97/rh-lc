module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjSplit
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeVectorIffInverseDoubleCosets
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSatakeGLOfHasSatakeParametersPrincipalSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLeOneIffOfContinuousStatement
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import ReciprocityTheory.Automorphisms.PlaceA
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDEqSumOfAgree
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitHeckeOperatorInverseConjugatePlaceCosetSumStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLeOneIffOfContinuous
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAdicCompletionEquivUniformiser

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnifMap

theorem unif_to_unif : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 F))
    (w : HeightOneSpectrum (𝓞 E)) (i : v.adicCompletion F ≃+* w.adicCompletion E), Continuous i →
    ∀ ϖ : v.adicCompletion F, Valued.v ϖ = WithZero.exp (-1 : ℤ) → Valued.v (i ϖ) = WithZero.exp (-1 : ℤ) := by
  intro F E _ _ _ _ v w i hi ϖ hϖ
  have hle := GlobalTheory.T.valued_le_one_iff_of_continuous_ringEquiv F E v w i hi
  have key : ∀ x : WithZero (Multiplicative ℤ), x ≠ 0 → x < 1 → x ≤ WithZero.exp (-1 : ℤ) := by
    intro x hx h1
    rw [← WithZero.exp_log hx] at h1 ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
    rw [WithZero.exp_le_exp]; omega
  have hlt : ∀ y, Valued.v (i y) < 1 ↔ Valued.v y < 1 := by
    intro y
    by_cases hy : y = 0
    · simp [hy]
    · have hiy : i y ≠ 0 := by simpa using hy
      have e1 := (Valued.v (R := w.adicCompletion E)).one_lt_val_iff (inv_ne_zero hiy)
      have e2 := (Valued.v (R := v.adicCompletion F)).one_lt_val_iff (inv_ne_zero hy)
      rw [inv_inv] at e1 e2
      rw [← e1, ← e2, ← not_le, ← not_le, ← map_inv₀ i, hle]
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hiϖ0 : i ϖ ≠ 0 := by simpa using hϖ0
  have hϖ1 : Valued.v ϖ < 1 := by
    rw [hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hup : Valued.v (i ϖ) < 1 := (hlt ϖ).2 hϖ1
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer E w
  set z : w.adicCompletion E := (π : w.adicCompletion E)
  have hz : Valued.v z = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hπ
  set y := i.symm z
  have hy1 : Valued.v y < 1 := by
    rw [← hlt, RingEquiv.apply_symm_apply, hz, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hy0 : y ≠ 0 := by
    intro h; rw [h, map_zero] at hy1
    have : z = 0 := by simpa [y] using h
    rw [this, map_zero] at hz; exact WithZero.exp_ne_zero hz.symm
  have hdiv : Valued.v (y / ϖ) ≤ 1 := by
    rw [map_div₀, hϖ, div_le_one₀ (by simp)]
    exact key _ (by simpa using hy0) hy1
  have h2 := (hle _).2 hdiv
  rw [map_div₀, map_div₀, RingEquiv.apply_symm_apply, hz] at h2
  have hlow : WithZero.exp (-1 : ℤ) ≤ Valued.v (i ϖ) := by
    rwa [div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hiϖ0))] at h2
  exact le_antisymm (key _ (by simpa using hiϖ0) hup) hlow

end GlobalTheory.UnifMap
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAdicCompletionEquivUniformiserStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.continuous_adicCompletion_equiv_uniformiser : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 F))
    (w : HeightOneSpectrum (𝓞 E)) (i : v.adicCompletion F ≃+* w.adicCompletion E), Continuous i →
    ∀ ϖ : v.adicCompletion F, Valued.v ϖ = WithZero.exp (-1 : ℤ) → Valued.v (i ϖ) = WithZero.exp (-1 : ℤ) := by
  first | exact @GlobalTheory.UnifMap.unif_to_unif | exact GlobalTheory.UnifMap.unif_to_unif | (intros; apply GlobalTheory.UnifMap.unif_to_unif <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SatakeEigenvalueInvNormalisedEqEsymm

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SatEigArith

theorem esymm_map_mul_const' (c : ℂ) (s : Multiset ℂ) (k : ℕ) :
    (s.map (· * c)).esymm k = c ^ k * s.esymm k := by
  simp only [Multiset.esymm, Multiset.powersetCard_map, Multiset.map_map, Function.comp_def]
  rw [← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun t ht => ?_)
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
    (Multiset.mem_powersetCard.1 ht).2, Multiset.map_id', mul_comm]

theorem exponent_eq (q n k : ℕ) (hq : 0 < q) (hk : k ≤ n) :
    (q : ℂ) ^ (k * (k - 1) / 2) * ((q : ℂ) ^ (k * (n - 1)))⁻¹ * (q : ℂ) ^ (((k : ℂ) * ((n : ℂ) - k)) / 2) =
      ((q : ℂ) ^ (((1 - (n : ℝ)) / 2 : ℝ) : ℂ)) ^ k := by
  have hQ : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · simp
  have h2 : ((k * (k - 1) / 2 : ℕ) : ℂ) = (k : ℂ) * ((k : ℂ) - 1) / 2 := by
    have h0 := Nat.div_mul_cancel (even_iff_two_dvd.mp (Nat.even_mul_pred_self k))
    have e : ((k * (k - 1) / 2 * 2 : ℕ) : ℂ) = ((k * (k - 1) : ℕ) : ℂ) := by rw [h0]
    simp only [Nat.cast_mul, Nat.cast_ofNat] at e
    rw [eq_div_iff two_ne_zero, e, Nat.cast_sub (show 1 ≤ k from hk1)]
    push_cast
    ring
  have h3 : ((k * (n - 1) : ℕ) : ℂ) = (k : ℂ) * ((n : ℂ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (show 1 ≤ n by omega)]
    push_cast
    ring
  rw [← Complex.cpow_natCast, ← Complex.cpow_natCast, ← Complex.cpow_neg, ← Complex.cpow_add _ _ hQ,
    ← Complex.cpow_add _ _ hQ, ← Complex.cpow_mul_nat, h2, h3]
  congr 1
  push_cast
  ring

theorem satEig_inv_normalised : ∀ (q n k : ℕ), 0 < q → k ≤ n → ∀ (α : Fin n → ℂˣ),
    (q : ℂ) ^ (k * (k - 1) / 2) * (((q : ℂ) ^ (k * (n - 1)))⁻¹ *
        GlobalTheory.LFun.satEig q n ((Finset.univ.val.map α).map (·⁻¹)) k) =
      ((Finset.univ.val.map fun i => ((α i : ℂ))⁻¹).map (· * (q : ℂ) ^ (((1 - (n : ℝ)) / 2 : ℝ) : ℂ))).esymm k := by
  intro q n k hq hk α
  rw [esymm_map_mul_const', GlobalTheory.LFun.satEig, ← mul_assoc, ← mul_assoc, exponent_eq q n k hq hk]
  congr 2
  simp [Multiset.map_map, Function.comp_def, Units.val_inv_eq_inv_val]

end GlobalTheory.SatEigArith
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SatakeEigenvalueInvNormalisedEqEsymmStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.satakeEigenvalue_inv_normalised_eq_esymm : ∀ (q n k : ℕ), 0 < q → k ≤ n → ∀ (α : Fin n → ℂˣ),
    (q : ℂ) ^ (k * (k - 1) / 2) * (((q : ℂ) ^ (k * (n - 1)))⁻¹ *
        GlobalTheory.LFun.satEig q n ((Finset.univ.val.map α).map (·⁻¹)) k) =
      ((Finset.univ.val.map fun i => ((α i : ℂ))⁻¹).map (· * (q : ℂ) ^ (((1 - (n : ℝ)) / 2 : ℝ) : ℂ))).esymm k := by
  first | exact @GlobalTheory.SatEigArith.satEig_inv_normalised | exact GlobalTheory.SatEigArith.satEig_inv_normalised | (intros; apply GlobalTheory.SatEigArith.satEig_inv_normalised <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceHeckeOperatorEigenvalueConjSpherical

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HeckeEigConj
open GlobalTheory.HeckeEigConj

theorem tN_eig : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L)
    (ϖ : s.v.adicCompletion (maximalRealSubfield L)), IsUnif L s.v ϖ → ∀ J : Subgroup (GAf L n),
    (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax L n)) →
    ∀ (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L))) (α : Fin n → ℂˣ),
    GlobalTheory.SmGL.HasSatake σ.ρ α →
    ∀ (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* (GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L), Continuous i →
    (∀ x : L, i ((GlobalTheory.HeckeFrob.conjSplit s).i x) = algebraMap L ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L) x) →
    ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (T : σ.V →ₗ[ℂ] (GAf L n → W)),
    GlobalTheory.HeckeFrob.IsLocMap (GlobalTheory.HeckeFrob.conjSplit s) σ i T →
    ∀ e ∈ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SplitWeil.KO ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L) (Fin n)),
    ∀ k, 1 ≤ k → k ≤ n →
      ((normV (GlobalTheory.HeckeFrob.conjSplit s).w : ℕ) : ℂ) ^ (k * (k - 1) / 2) • NG.tN J s ϖ k (T e) =
        (GlobalTheory.HeckeFrob.twEig (GlobalTheory.HeckeFrob.conjSplit s).w α).esymm k • T e := by
  intro L _ _ _ n s ϖ hϖ J hJ σ α hα i hi hiL W _ _ T hT e he k hk1 hkn
  classical
  have hK : ∀ a, i a ∈ Formalism.UG.Ov L (GlobalTheory.HeckeFrob.conjSplit s).w ↔
      a ∈ (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := fun a =>
    GlobalTheory.IsoInteg.valued_le_one_iff_of_continuous (maximalRealSubfield L) L s.v _ i hi a
  have heK : e ∈ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n) := by
    rw [← GlobalTheory.HeckeEigConj.KO_eq_KGL L (GlobalTheory.HeckeFrob.conjSplit s).w n]; exact he
  have hφK : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ →
      Matrix.GeneralLinearGroup.map i.toRingHom ((GlobalTheory.HeckeFrob.conjSplit s).loc n κ) ∈
        GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n := fun κ hκ ht => by
    rw [GlobalTheory.HeckeEigConj.map_loc_conjSplit L n s i κ]
    exact (GlobalTheory.LFun.ConjPlace.mem_iff_invT i hK _).1 ((GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s ht).2 hκ)
  obtain ⟨α0, -, hT0⟩ := GlobalTheory.HeckeScalarSph.exists_tSet_eq (n := n) s ϖ k hϖ
  obtain ⟨R, hR1, hR2⟩ := GlobalTheory.HeckeScalarSph.exists_repsU (n := n) s.v α0
  have hR1' : ∀ γ ∈ R, γ ∈ tSet L n s ϖ k := fun γ hγ => (hT0 γ).2 (hR1 γ hγ)
  have hR2' : ∀ x ∈ tSet L n s ϖ k, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n := fun x hx => hR2 x ((hT0 x).1 hx)
  have hD : ∀ x ∈ tSet L n s ϖ k, TrivOutside {s.v} x := fun x hx => hx.1
  have hrt : ∀ x, TrivOutside {s.v} x → NG.rt L n x (T e) =
      T (σ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom ((GlobalTheory.HeckeFrob.conjSplit s).loc n x)) e) :=
    fun x hx => (hT x hx e).symm
  have hfix : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ (T e) = T e := fun κ hκ ht => by
    rw [hrt κ ht, GlobalTheory.LGrp.mem_fixed.1 heK _ (hφK κ hκ ht)]
  have hsum := heckeD_eq_sum_of_agree J hJ hD hR1' hR2' hfix
  have hloc := GlobalTheory.T.splitHeckeOperator_inverse_conjugatePlace_cosetSum L n s ϖ hϖ k hkn i hi σ.ρ R hR1' hR2' e heK
  have key : NG.heckeD J (tSet L n s ϖ k) (T e) = T (GlobalTheory.LFun.heckeVec σ.ρ (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n)
      (fun g => Formalism.UG.Tj ℂ n (Formalism.UG.Ov L (GlobalTheory.HeckeFrob.conjSplit s).w) (i ϖ) k g⁻¹) e) := by

    rw [hsum, hloc, map_sum]
    exact Finset.sum_congr rfl fun γ hγ => hrt γ (hD γ (hR1' γ hγ))
  obtain ⟨hq1, hq2⟩ := norms_eq s
  by_cases he0 : e = 0
  · subst he0
    simp only [map_zero, smul_zero]
    funext g
    simp [NG.tN, NG.heckeD]
  have hSat := (GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake L (GlobalTheory.HeckeFrob.conjSplit s).w n σ.V σ.ρ α hα).2 e heK he0
  have hU : Formalism.UG.IsUnifV L (GlobalTheory.HeckeFrob.conjSplit s).w (i ϖ) :=
    GlobalTheory.T.continuous_adicCompletion_equiv_uniformiser (maximalRealSubfield L) L s.v _ i hi ϖ hϖ
  have hinv := (GlobalTheory.ChainOnto.SatInv.satVec_iff_inv L (GlobalTheory.HeckeFrob.conjSplit s).w n σ.V σ.ρ e _ he0 heK
    (by simp)).1 hSat (i ϖ) hU k hkn
  rw [NG.tN, key, hinv, map_smul, smul_smul, smul_smul, hq1, hq2]
  congr 1
  rw [mul_assoc]
  exact GlobalTheory.T.satakeEigenvalue_inv_normalised_eq_esymm (normV (GlobalTheory.HeckeFrob.conjSplit s).w) n k
    (Nat.pos_of_ne_zero (hq1 ▸ GlobalTheory.LFun.qV_ne_zero (GlobalTheory.HeckeFrob.conjSplit s).w)) hkn α

end GlobalTheory.HeckeEigConj

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceHeckeOperatorEigenvalueConjSphericalStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.split_place_hecke_operator_eigenvalue_conj_spherical : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L)
    (ϖ : s.v.adicCompletion (maximalRealSubfield L)), IsUnif L s.v ϖ → ∀ J : Subgroup (GAf L n),
    (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax L n)) →
    ∀ (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L))) (α : Fin n → ℂˣ),
    GlobalTheory.SmGL.HasSatake σ.ρ α →
    ∀ (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* (GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L), Continuous i →
    (∀ x : L, i ((GlobalTheory.HeckeFrob.conjSplit s).i x) = algebraMap L ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L) x) →
    ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (T : σ.V →ₗ[ℂ] (GAf L n → W)),
    GlobalTheory.HeckeFrob.IsLocMap (GlobalTheory.HeckeFrob.conjSplit s) σ i T →
    ∀ e ∈ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SplitWeil.KO ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L) (Fin n)),
    ∀ k, 1 ≤ k → k ≤ n →
      ((normV (GlobalTheory.HeckeFrob.conjSplit s).w : ℕ) : ℂ) ^ (k * (k - 1) / 2) • NG.tN J s ϖ k (T e) =
        (GlobalTheory.HeckeFrob.twEig (GlobalTheory.HeckeFrob.conjSplit s).w α).esymm k • T e := by
  first | exact @GlobalTheory.HeckeEigConj.tN_eig | exact GlobalTheory.HeckeEigConj.tN_eig | (intros; apply GlobalTheory.HeckeEigConj.tN_eig <;> assumption)
end
end
