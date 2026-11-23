module

public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.ClassMapD
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsRc
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SglobDzBigDef
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSplitPlace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DepthZeroIdentityFiniteTypeOfTypePrimeComponentStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LabLPIsLabelActK
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrincipalCongruenceFixedVectorsLeSmoothVectors
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroSupercuspidalCuspidalModule
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTypePlaceCompletionIdentStatement
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodLem
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsCompIrrSmParamStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsIsRc
public import Development.DiscreteGroups.GlobalIrreducibility.LocTypeOfSerParamLe
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NeZeroOfMemRoots
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelOfIsCuspOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FixedNeBotOfEquiv
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharInOfIsCharLab
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameParamRecordLe
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameSupportCompatible
public import Development.DiscreteGroups.GlobalIrreducibility.SerLocOfTiesLe
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowTruthOfLabelTie

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM

namespace GlobalTheory.LabPin
open GlobalTheory.TypeRec
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem principalCongruence_fixed_vector_rational_local_field {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ}
    (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E)))
    (h : GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.SplitWeil.KOne ((D.naut.plGw k v).adicCompletion D.host.E) (Fin n)) ≠ ⊥) :
    fixK1 (pull I k v τ).ρ ≠ ⊥ := by
  have hw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
  have hle : ∀ t : ℚ_[D.host.g k], ‖t‖ ≤ 1 → ‖I.i k v t‖ ≤ 1 := fun t ht =>
    GlobalTheory.TypeRec.Model.emb_le (D.naut.plGw k v) (D.host.g k) (I.i k v).toRingHom (I.cont k v) t ht
  have hlt : ∀ t : ℚ_[D.host.g k], ‖t‖ < 1 → ‖I.i k v t‖ < 1 := by
    intro t ht
    have hp := (Fact.out : (D.host.g k).Prime)
    have h2 : ‖t‖ ≤ ((D.host.g k : ℕ) : ℝ) ^ (-1 : ℤ) :=
      (Padic.norm_le_pow_iff_norm_lt_pow_add_one t (-1)).2 (by simpa using ht)
    have hp0 : ((D.host.g k : ℕ) : ℚ_[D.host.g k]) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    have h3 : ‖t / ((D.host.g k : ℕ) : ℚ_[D.host.g k])‖ ≤ 1 := by
      rw [norm_div, Padic.norm_p, div_le_one₀ (by have := hp.one_lt; positivity)]
      simpa using h2
    have e : I.i k v t = ((D.host.g k : ℕ) : (D.naut.plGw k v).adicCompletion D.host.E) *
        I.i k v (t / ((D.host.g k : ℕ) : ℚ_[D.host.g k])) := by
      rw [← map_natCast (I.i k v) (D.host.g k), ← map_mul, mul_div_cancel₀ _ hp0]
    rw [e, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (hle _ h3))
      (Formalism.BasicNotions.Examples₂.LocF.norm_l_lt (D.naut.plGw k v) (D.host.g k) hw)
  have hint : ∀ (q : GL (Fin n) ℤ_[D.host.g k]) a b,
      (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom (GlobalTheory.GLp.inc (D.host.g k) n q)).1 a b ∈
        (D.naut.plGw k v).adicCompletionIntegers D.host.E := by
    intro q a b
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2
      (Valued.toNormedField.norm_le_one_iff.1 (hle _ (PadicInt.norm_le_one (q.1 a b))))
  have hone : ∀ a b : Fin n, (1 : Matrix (Fin n) (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E)) a b =
      I.i k v (((1 : Matrix (Fin n) (Fin n) ℤ_[D.host.g k]) a b : ℤ_[D.host.g k]) : ℚ_[D.host.g k]) := by
    intro a b
    by_cases h' : a = b
    · subst h'; simp
    · simp [Matrix.one_apply_ne h']
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨y, (Submodule.mem_iInf _).2 fun z => ?_, hy0⟩
  have hu : Matrix.GeneralLinearGroup.map (I.i k v).toRingHom (GlobalTheory.GLp.inc (D.host.g k) n z) ∈
      GlobalTheory.SplitWeil.KOne ((D.naut.plGw k v).adicCompletion D.host.E) (Fin n) := by
    rw [← (GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne (D.naut.plGw k v) n).2, GlobalTheory.AdelicU.mem_princ_iff,
      GlobalTheory.AdelicU.mem_GLint_iff]
    refine ⟨⟨fun a b => hint _ a b, fun a b => ?_⟩, fun a b => ?_⟩
    · rw [← map_inv, ← map_inv]
      exact hint _ a b
    · have hz : GlobalTheory.GLp.red (D.host.g k) n z = 1 := z.2
      have hab : PadicInt.toZMod ((z : GL (Fin n) ℤ_[D.host.g k]).1 a b) =
          (1 : Matrix (Fin n) (Fin n) (ZMod (D.host.g k))) a b :=
        congrArg (fun m : GL (Fin n) (ZMod (D.host.g k)) => m.1 a b) hz
      have h4 : (z : GL (Fin n) ℤ_[D.host.g k]).1 a b - (1 : Matrix (Fin n) (Fin n) ℤ_[D.host.g k]) a b ∈
          RingHom.ker (PadicInt.toZMod (p := D.host.g k)) := by
        rw [RingHom.mem_ker, map_sub, hab]
        by_cases h' : a = b
        · subst h'; simp
        · simp [Matrix.one_apply_ne h']
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at h4
      have h5 := hlt _ h4
      apply Valued.toNormedField.norm_lt_one_iff.1
      rw [Matrix.sub_apply, hone a b]
      convert h5 using 2
      rw [PadicInt.coe_sub, map_sub]
      rfl
  change τ.ρ (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom (GlobalTheory.GLp.inc (D.host.g k) n z)) y - y = 0
  rw [sub_eq_zero]
  exact GlobalTheory.Parabolic.mem_fixed.1 hy _ hu

theorem principalCongruenceFixedVectors_ne_bot_of_iso {g : ℕ} [Fact g.Prime] {n : ℕ} {π π' : QRep g n} (e : π ≅ π') (h : fixK1 π'.ρ ≠ ⊥) :
    fixK1 π.ρ ≠ ⊥ := by
  intro hb
  apply h
  rw [Submodule.eq_bot_iff] at hb ⊢
  intro x hx
  have hy : (e.inv.hom x) ∈ fixK1 π.ρ := by
    simp only [fixK1, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hx ⊢
    intro q
    rw [← Rep.hom_comm_apply, hx q]
  have h0 := hb _ hy
  have : e.hom.hom (e.inv.hom x) = x := by simp
  rw [← this, h0, map_zero]

end GlobalTheory.LabPin

namespace GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end GlobalTheory.LabPin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroSupercuspidalCuspidalModuleStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.depthZeroSupercuspidal_cuspidalModule : ∀ (g : ℕ) [Fact g.Prime], TameGen.DepthZeroCuspidal g := by
  first | exact @GlobalTheory.DepthZeroCusp.depthZeroCuspidal | exact GlobalTheory.DepthZeroCusp.depthZeroCuspidal | (intros; apply GlobalTheory.DepthZeroCusp.depthZeroCuspidal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClassMapCorrespondence

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TypeRec

theorem pull_iso_of_cls_eq {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ}
    (σ τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E)))
    (h : GlobalTheory.LocLanglands.cls σ = GlobalTheory.LocLanglands.cls τ) : Nonempty (pull I k v σ ≅ pull I k v τ) := by
  have h1 : σ.cl = τ.cl := by
    have := (Sigma.mk.inj_iff.1 h).2
    exact eq_of_heq this
  obtain ⟨φ⟩ := GlobalTheory.SmGL.IrrRep.cl_eq_iff.1 h1
  exact ⟨Rep.mkIso (Representation.Equiv.mk φ.toLinearEquiv fun g =>
    φ.toIntertwiningMap.isIntertwining' (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom g))⟩

end GlobalTheory.TypeRec

end
end
end

-- Source module: Development.DiscreteGroups.GlobalIrreducibility.ActKEEqSelfLe

section

@[expose] public section

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys

noncomputable section

namespace DiscreteGroups.sglob.DzType.Rt


open GlobalTheory.SerSys.LabLoc in
theorem actK_e_eq_self_le : ∀ (g : ℕ) [Fact g.Prime] (S : Sys g) (τ : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ine : ∀ n, QRep g n → ℂ[X]) (b : ℕ), Set.InjOn τ {x | x ≠ 0} → DiscreteGroups.sglob.DzType.Rt.SerParamLe b S.e τ ine → ∀ (n : ℕ), n ≤ b → ∀ (π : QRep g n), IrrSm π → ∀ f : (ZMod g)[X], f.Monic → f.coeff 0 ≠ 0 → ine n π = ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (τ x)).prod → ∀ v ∈ fixK1 π.ρ, actK π.ρ (S.e n f) v = v := by
  intro g _ S τ ine b hτ hP n hn π hπ f hm h0 hine v hv
  have key : ∀ f', actK π.ρ (S.e n f') v ≠ 0 → f' = f := by
    intro f' hf'
    have hne : S.e n f' ≠ 0 := fun e => hf' (by rw [e]; simp [actK])
    obtain ⟨hm', -, h0'⟩ := S.label n f' hne
    have e1 := (hP n hn π hπ f' ⟨v, hv, hf'⟩).symm.trans hine
    have e1' : (((Formalism.CyclotomicNorms.rootsBar f').map τ).map fun a => X - C a).prod =
        (((Formalism.CyclotomicNorms.rootsBar f).map τ).map fun a => X - C a).prod := by
      rw [Multiset.map_map, Multiset.map_map]; exact e1
    have e2 := congrArg Polynomial.roots e1'
    rw [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at e2
    exact eq_of_roots_eq hm' hm (map_eq_map hτ (fun x hx => ne_zero_of_mem_roots h0' hx)
      (fun x hx => ne_zero_of_mem_roots h0 hx) e2)
  obtain ⟨T, hT⟩ := S.sum n
  have hv1 : v = ∑ f' ∈ T, actK π.ρ (S.e n f') v := by
    conv_lhs => rw [← actK_one_of_mem π.ρ hv, ← hT, actK_finset_sum]
    simp
  have hv2 : ∑ f' ∈ T, actK π.ρ (S.e n f') v = if f ∈ T then actK π.ρ (S.e n f) v else 0 := by
    split_ifs with hfT
    · rw [Finset.sum_eq_single f]
      · intro f' _ h; by_contra h'; exact h (key f' h')
      · intro h; exact absurd hfT h
    · refine Finset.sum_eq_zero fun f' hf' => ?_
      by_contra h'; exact hfT (key f' h' ▸ hf')
  split_ifs at hv2 with hfT
  · exact (hv1.trans hv2).symm
  · have : v = 0 := hv1.trans hv2
    rw [this, map_zero]

end DiscreteGroups.sglob.DzType.Rt

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MDzLabLP

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace DiscreteGroups.sglob.DzType.Rt
open GlobalTheory.WeilDeligne GlobalTheory.SerSys.LabDepth in
theorem labLP_isLabel_and_actK_fix : Green → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D) (L : ∀ k, LabelDatum (D.host.g k)), _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc → GlobalTheory.HeightCounting.LabTrue D T → GlobalTheory.SerSys.LabTie D L → DiscreteGroups.sglob.DzType.Rt.LabParamLe D.R.nV D L rc → ∀ k v (π : QRep (D.host.g k) D.R.r), IrrSm π → fixK1 π.ρ ≠ ⊥ → IsLabel D k (D.naut.items₂ k (D.naut.plGw k v) (rc k v D.R.r π)) ∧ ∀ y ∈ fixK1 π.ρ, actK π.ρ (D.ntypes.eSer k (D.naut.items₂ k (D.naut.plGw k v) (rc k v D.R.r π))) y = y := by
  intro hG hL D T I rc L hRc hLT hLab hP k v π hπ hfix
  let S : Sys (D.host.g k) := OfLabel.ofLabel (L k) (Bridge.five_le D k) hG
  have hSe : ∀ n f, S.e n f = eSerC (L k) n f := fun _ _ => rfl
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hfix
  obtain ⟨f, hf⟩ : ∃ f, actK π.ρ (S.e D.R.r f) y ≠ 0 := by
    obtain ⟨T', hT'⟩ := S.sum D.R.r
    by_contra hcon
    push Not at hcon
    apply hy0
    rw [← LabLoc.actK_one_of_mem π.ρ hy, ← hT', LabLoc.actK_finset_sum, LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun f _ => hcon f
  have hne : S.e D.R.r f ≠ 0 := fun e => hf (by rw [e]; simp [actK])
  obtain ⟨hm, hd, h0⟩ := S.label _ f hne
  have hine : D.naut.inePol (rc k v D.R.r π) (D.ntypes.tg k v) =
      ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (D.ntypes.teichC k x)).prod := by
    rw [← (hLab k).1]
    exact hP k v D.R.r (DiscreteGroups.sglob.DzType.Rt.r_le_nV D) π hπ f ⟨y, hy, hf⟩
  have hSet : TeichmullerInertiaLabelCondition (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) (D.ntypes.teichC k) (D.ntypes.tg k v) :=
    .of_tameGenAt (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k)
      (D.naut.plGw_over k v)) (D.ntypes.tg_gen k v) (D.ntypes.teichC_inj k)
  have htame : (T.e _ (rc k v D.R.r π)).tame := by
    obtain ⟨σ, hiso, hσ⟩ := exists_pull D I k v π hπ hfix
    rw [hRc k v D.R.r σ π hiso]
    first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))); obtain ⟨a, ha, ε, hl⟩ := hOpn) | obtain ⟨a, ha, ε, -, hl⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))
    refine tame_of_isTameWD ((fun hx => haveI := UpperTheory.One.M.charZero_compl (D.naut.plGw k v); _root_.UpperTheory.One.M.LawsM.depth hl _ (UpperTheory.One.M.good_of_fixed ⟨_, ⟨D.host.g_prime k⟩, I.i k v, I.cont k v⟩ _ hx) hx : _ → _) ?_)
    exact GlobalTheory.LocLanglands.fixed_ne_bot_of_equiv (GlobalTheory.SmGL.IrrRep.nonempty_equiv_rep σ).some.symm hσ
  have hlab : D.naut.items₂ k (D.naut.plGw k v) (rc k v D.R.r π) = f := by
    have e1 : (Formalism.CyclotomicNorms.rootsBar f).map (fun x => X - C (D.ntypes.teichC k x)) =
        ((Formalism.CyclotomicNorms.rootsBar f).map (D.ntypes.teichC k)).map (fun a => X - C a) := by
      rw [Multiset.map_map]; rfl
    rw [hLT k v, WD.lab_eq_iff_of_tame hSet htame, ← T.inePol _ _ _ (D.ntypes.tg_gen k v).1, hine, e1,
      roots_multiset_prod_X_sub_C]
    exact ⟨hm, rfl⟩
  refine ⟨hlab ▸ ⟨hm, hd, h0⟩, fun z hz => ?_⟩
  rw [hlab, (hLab k).2 f, ← hSe]
  refine DiscreteGroups.sglob.DzType.Rt.actK_e_eq_self_le _ S (L k).teich (fun n π => D.naut.inePol (rc k v n π) (D.ntypes.tg k v)) D.R.nV ?_
    (hP k v) D.R.r (DiscreteGroups.sglob.DzType.Rt.r_le_nV D) π hπ f hm h0 ?_ z hz
  · rw [(hLab k).1]
    exact fun x hx y hy e => D.ntypes.teichC_inj k x y hx hy e
  · rw [(hLab k).1]; exact hine
end DiscreteGroups.sglob.DzType.Rt
end
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MClassMapD

section

@[expose] public section



section
section
noncomputable section
namespace GlobalTheory.SerSys
open Polynomial GlobalTheory.GLq GlobalTheory.GLp Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical
variable {g : ℕ} [Fact g.Prime]
end GlobalTheory.SerSys
end
end
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.One.M
theorem exists_isRc_isClassMapD_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
    (I : Ident D), ∃ rc : GlobalTheory.SerSys.Corr D, _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc ∧ ∀ k v, GlobalTheory.SerSys.IsClassMapD D.naut.lpDim (rc k v) := by
  intro hL D T I
  obtain ⟨rc, hrc⟩ := _root_.GlobalTheory.TypeRec.Model.exists_isRc_alt hL T I
  refine ⟨rc, hrc, fun k v n π hπ => ?_⟩
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))); obtain ⟨_, _, _, H⟩ := hOpn) | obtain ⟨_, _, _, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))
  obtain ⟨σ, e⟩ := GlobalTheory.TypeRec.Model.exists_pull I k v π hπ
  refine ⟨?_, fun π' hπ' hg => ?_⟩
  · rw [← T.dim, hrc k v n σ π e]
    exact H.dim _
  · obtain ⟨σ', e', hσ'⟩ := GlobalTheory.SerSys.LabDepth.exists_pull D I k v π' hπ' hg
    have hg' : UpperTheory.Zero.LLC.Good (GlobalTheory.LocLanglands.cls σ') :=
      haveI := charZero_compl (D.naut.plGw k v)
      good_cls_of_fixed ⟨_, ⟨D.host.g_prime k⟩, I.i k v, I.cont k v⟩ σ' hσ'
    constructor
    · intro hr
      have h2 := congrArg (T.e _) hr
      rw [hrc k v n σ π e, hrc k v n σ' π' e'] at h2
      obtain ⟨f⟩ := pull_iso_of_cls_eq I k v σ σ' (_root_.UpperTheory.One.M.LawsM.inj H _ _ hg' h2)
      exact ⟨e.some ≪≫ f ≪≫ e'.some.symm⟩
    · rintro ⟨f⟩
      apply (T.e _).injective
      rw [hrc k v n σ π e, hrc k v n σ π' ⟨f.symm ≪≫ e.some⟩]
end UpperTheory.One.M
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
namespace DiscreteGroups.sglob.DzType.Rt
open GlobalTheory.TypeRec GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem typeLab_of_local_m_alt : Green → GlobalTheory.Published.ZelevinskyPolynomialRing → _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (Rw : GlobalTheory.HeightCounting.RowSide D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (L : ∀ k, LabelDatum (D.host.g k)), GlobalTheory.HeightCounting.LabTrue D T → _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => T.e w (Rw.locR σ w)) Rw.satR → GlobalTheory.HeightCounting.RowDepth D rep → GlobalTheory.SerSys.LabTie D L → (∀ k v, ∃ κ : IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k), TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) κ (D.ntypes.tg k v) (L k).gen) → GlobalTheory.LabPin.TypeLab D rep := by
  intro hG hZ hDZ hL D T Rw rep L hLab hRow hDep hLT hTame
  obtain ⟨I⟩ := GlobalTheory.T.nonempty_typePlaceCompletionIdent D
  obtain ⟨rc, hrc, hcls⟩ := _root_.UpperTheory.One.M.exists_isRc_isClassMapD_alt hL D T I
  obtain ⟨cp, hcomp, hcp⟩ := _root_.GlobalTheory.T.exists_comp_irrSm_locR_eq_rc hL D T I rc hrc Rw rep hRow hDep
  have hP : DiscreteGroups.sglob.DzType.Rt.LabParamLe D.R.nV D L rc := DiscreteGroups.sglob.DzType.Rt.labParamLe_of D L rc hG (_root_.GlobalTheory.T.tame_gen_support_compat_of_is_rc hZ hL D T I rc hrc)
    (fun k => GlobalTheory.T.depthZeroSupercuspidal_cuspidalModule (D.host.g k))
    (fun k v => by
      obtain ⟨κ, hκ⟩ := hTame k v
      exact _root_.DiscreteGroups.sglob.DzType.Rt.tame_param_le_of_tame_coupled hDZ hL D T I rc hrc L k v κ hκ)
  have hfix : ∀ σ k v, fixK1 (cp σ k v).ρ ≠ ⊥ := by
    intro σ k v
    obtain ⟨s, τ, hsw, hloc, hfx⟩ := hDep σ k v
    have hT := hRow.1 σ s τ hloc
    have key : ∀ (w : PlE D.host) (hw : w = D.naut.plGw k v)
        (τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (w.adicCompletion D.host.E))),
        T.e w (Rw.locR σ w) = _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) (GlobalTheory.LocLanglands.cls τ) →
        GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.SplitWeil.KOne (w.adicCompletion D.host.E) (Fin D.R.r)) ≠ ⊥ →
        fixK1 (cp σ k v).ρ ≠ ⊥ := by
      intro w hw τ hT hfx
      subst hw
      have h1 := hrc k v D.R.r τ (pull I k v τ) ⟨CategoryTheory.Iso.refl _⟩
      have h2 : rc k v D.R.r (pull I k v τ) = rc k v D.R.r (cp σ k v) := by
        rw [← (hcp σ k v).2]
        exact (T.e _).injective (h1.trans hT.symm)
      obtain ⟨e⟩ := (((hcls k v) D.R.r (cp σ k v) (hcp σ k v).1).2 (pull I k v τ) (GlobalTheory.TypeRec.Model.irrSm_pull I k v τ)
        (GlobalTheory.LabPin.principalCongruence_fixed_vector_rational_local_field I k v τ hfx)).1 h2.symm
      exact GlobalTheory.LabPin.principalCongruenceFixedVectors_ne_bot_of_iso e (GlobalTheory.LabPin.principalCongruence_fixed_vector_rational_local_field I k v τ hfx)
    exact key s.w hsw τ hT hfx
  intro σ k v
  have hlab : D.nd.lab k σ v = D.naut.items₂ k (D.naut.plGw k v) (rc k v D.R.r (cp σ k v)) := by
    rw [Rw.lab_eq, (hcp σ k v).2]
  obtain ⟨h1, h2⟩ := _root_.DiscreteGroups.sglob.DzType.Rt.labLP_isLabel_and_actK_fix hG hL D T I rc L hrc hLab hLT hP k v (cp σ k v) (hcp σ k v).1 (hfix σ k v)
  show IsLabel D k (D.nd.lab k σ v) ∧ ∀ s : SplitPlace D.host.E, s.w = D.naut.plGw k v → SerFix (rep σ) s (D.ntypes.eSer k (D.nd.lab k σ v))
  rw [hlab]
  exact ⟨h1, fun s hs => GlobalTheory.T.depthZeroIdentity_finiteType_of_typePrimeComponent D I rep cp hcomp σ k v _ h2 s hs⟩
end DiscreteGroups.sglob.DzType.Rt
end
section
namespace GlobalTheory.LabPin
end GlobalTheory.LabPin
namespace GlobalTheory.LabPin
end GlobalTheory.LabPin
end
end
end
end
