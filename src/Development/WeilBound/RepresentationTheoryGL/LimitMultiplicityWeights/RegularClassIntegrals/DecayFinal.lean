module

public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.Variation
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
public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.DDerMemc
public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.DDerVan
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicUnitaryEveryPointHasCuspScale
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelDomainOpenSubgroupBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusConjugateUnipotentBoundedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalCompactFundamentalDomainStatement
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.WeilBound.ThetaLifts.Reductions.SiegelHaar
public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.DSmOfb
public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.DSumSm
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.NcardBiUnionLe
public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.NsumLevel

-- Source module: Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.DBridge

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec

theorem bridge : Bridge := by
  intro D V r X Y hW j
  rw [NA_frameFlag]
  rfl

end MainStatements.WeightKernel.Dec

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.DDecay

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec

namespace DDecay

theorem tsum_eq (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hW : IsWittFrame D.sp.cm.sig V.gram X Y) (j : Fin r)
    (hB : NA (frameFlag (isIsoFrame_firstCols hW j)) = unipRad D.sp.cm.sig V.gram (pre X j))
    (g : GA D V → ℂ) :
    ∑' ν : (frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm, g (rat V ν) =
      ∑' ν : NF D.sp.cm.sig V.gram (pre X j), g ν := by
  have hS : ((NF D.sp.cm.sig V.gram (pre X j) : Subgroup (GA D V)) : Set (GA D V)) =
      rat V '' (((frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm : Subgroup (GF V)) : Set (GF V)) := by
    rw [← Subgroup.coe_map, map_unipRat, hB]; rfl
  calc ∑' ν : (frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm, g (rat V ν)
      = ∑' b : (rat V '' (((frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm : Subgroup (GF V)) :
          Set (GF V))), g b := (tsum_image g (ratEmb_injective _ _).injOn).symm
    _ = ∑' c : ((NF D.sp.cm.sig V.gram (pre X j) : Subgroup (GA D V)) : Set (GA D V)),
          g (Set.equivOfEq hS c) := (Equiv.tsum_eq (Set.equivOfEq hS) (fun b => g b)).symm
    _ = ∑' ν : NF D.sp.cm.sig V.gram (pre X j), g ν := rfl

end DDecay

theorem decay : Core → Bridge → Decay := by
  intro hCore hBridge D V r X Y hW c hc j f hf hU C W hC hW'
  obtain ⟨A, hA⟩ := hCore D V r X Y hW c hc j
  have hB := hBridge D V r X Y hW j
  have hV : Van (unipRad D.sp.cm.sig V.gram (pre X j)) f := by
    have h0 : Van (NA (frameFlag (isIsoFrame_firstCols hW j))) f := fun ν _ x y => (hU ν x y).2
    rw [hB] at h0
    exact h0
  refine ⟨A, fun m => ?_⟩
  obtain ⟨B, hBd⟩ := hA m f hf hV C W hC hW'
  refine ⟨B, fun t ht a ha x hx y hy => ?_⟩
  have h1 := hBd t ht a ha x hx y hy
  have h2 : ∑' ν : (frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm,
      f (x * (a⁻¹ * rat V ν * a) * y) = nsum (NF D.sp.cm.sig V.gram (pre X j)) f (x * a⁻¹) (a * y) := by
    rw [nsum, ← DDecay.tsum_eq D V r X Y hW j hB (fun g => f (x * a⁻¹ * g * (a * y)))]
    congr 1; funext ν; congr 1; group
  rw [h2]
  exact h1

end MainStatements.WeightKernel.Dec
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.DLevel

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec.DLevel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem level_of_mem {f : GAd σ J → ℂ} (hf : f ∈ CcAd σ J) :
    ∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, f (g * k) = f g := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, -, b, hb, rfl⟩ := hx
    obtain ⟨V, hV, hVb⟩ := GlobalTheory.Orb.exists_biinvariant hb
    refine ⟨V.comap (projFin σ J), hV.preimage (continuous_projFin σ J), fun k hk hkf g => ?_⟩
    show a (projInf σ J (g * k)) * b (projFin σ J (g * k)) = a (projInf σ J g) * b (projFin σ J g)
    rw [map_mul, map_mul, mem_finPts.1 hkf, mul_one, (hVb _ hk _).2]
  | zero => exact ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨U, hU, h⟩ := hx
    obtain ⟨V, hV, h'⟩ := hy
    exact ⟨U ⊓ V, hU.inter hV, fun k hk hkf g => by
      simp only [Pi.add_apply, h k hk.1 hkf g, h' k hk.2 hkf g]⟩
  | smul c x _ hx =>
    obtain ⟨U, hU, h⟩ := hx
    exact ⟨U, hU, fun k hk hkf g => by simp only [Pi.smul_apply, h k hk hkf g]⟩

end MainStatements.WeightKernel.Dec.DLevel

theorem MainStatements.WeightKernel.Dec.level : MainStatements.WeightKernel.Dec.Level := by
  intro F E _ _ _ _ _ σ _ n J _ f hf
  exact MainStatements.WeightKernel.Dec.DLevel.level_of_mem hf

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.DNearCusp

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
open PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay.NearCusp
open scoped Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec

theorem nearCusp : NearCusp := by
  intro F E _ _ _ _ _ σ hCM n J hJ r X Y hW Cm c U hCm hc hU s
  have hσ := sigma_sigma hCM
  have hC : GlobalTheory.UAut.IsIsoCols σ J (pre X s) := GlobalTheory.UAut.isIsoCols_of_isWittFrame hW hσ hJ s.2
  let Cf : Set (GFin σ J) := (fun z : GAd σ J => projFin σ J z) '' Cm
  have hCf : IsCompact Cf := hCm.image (continuous_projFin σ J)
  let Uf : Set (GFin σ J) := ofFin σ J ⁻¹' (U : Set (GAd σ J))
  have hUf : Uf ∈ 𝓝 (1 : GFin σ J) :=
    (hU.preimage (continuous_ofFin σ J)).mem_nhds (by simp only [Set.mem_preimage, map_one]; exact U.one_mem)
  let Wn : Set (GFin σ J) := {x | ∀ h ∈ Cf, h⁻¹ * x * h ∈ Uf}
  have hWn : Wn ∈ 𝓝 (1 : GFin σ J) := conj_mem_nhds hCf hUf
  obtain ⟨Q, hQ, hQm⟩ := GlobalTheory.T.unipotent_radical_compact_fundamental_domain F E σ hCM n J hJ _ (pre X s) hC Wn hWn
  obtain ⟨M₁, hM₁, hM₁b⟩ := GlobalTheory.T.torus_conjugate_unipotent_bounded F E σ hCM n J hJ r X Y hW Q c hQ hc s
  obtain ⟨C₀, hC₀, hC₀b⟩ := exists_bound_archMat (σ := σ) (J := J) hCm
  refine ⟨C₀ * M₁, mul_nonneg hC₀ hM₁, ?_⟩
  intro t ht a ha k hk m hm
  obtain ⟨γ, hγ, q, hqQ, hqU, hqW, rfl⟩ := hQm m hm
  have hγU : γ ∈ unipRad σ J (pre X s) := by
    have := mul_mem hm (inv_mem hqU)
    rwa [mul_inv_cancel_right] at this
  have hfa : projFin σ J a = 1 := mem_infPts.1 ha.1
  refine ⟨γ, ⟨hγ, hγU⟩, ofInf σ J (projInf σ J ((a * k)⁻¹ * q * (a * k))),
    ofFin σ J (projFin σ J ((a * k)⁻¹ * q * (a * k))), ⟨mem_infPts.2 (projFin_ofInf σ J _), ?_⟩, ?_,
    mem_finPts.2 (projInf_ofFin σ J _), ?_⟩
  · intro w τ i j
    have hN := hM₁b q hqQ hqU t ht a ha w τ
    have ev : (a * k)⁻¹ * q * (a * k) = k⁻¹ * (a⁻¹ * q * a) * k := by group
    have hB : archMat σ J τ (projArch σ J w k⁻¹) * archMat σ J τ (projArch σ J w k) = 1 := by
      rw [← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
    have key : archMat σ J τ (projArch σ J w (ofInf σ J (projInf σ J ((a * k)⁻¹ * q * (a * k))))) - 1 =
        archMat σ J τ (projArch σ J w k⁻¹) * (archMat σ J τ (projArch σ J w (a⁻¹ * q * a)) - 1) *
          archMat σ J τ (projArch σ J w k) := by
      rw [projArch_ofInf, projInfArch_projInf, ev, map_mul (projArch σ J w) _ k, map_mul (projArch σ J w) k⁻¹,
        map_mul (archMat σ J τ), map_mul (archMat σ J τ), Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hB]
    rw [key]
    refine (GlobalTheory.CuspGeo.norm_mul_mul_apply_le _ _ _ _ hN i j).trans ?_
    rw [mul_div_assoc C₀]
    exact mul_le_mul_of_nonneg_right (hC₀b k hk w τ i j) (div_nonneg hM₁ (ratio_pos ht s).le)
  · have hh : projFin σ J k ∈ Cf := ⟨k, hk, rfl⟩
    have e : projFin σ J ((a * k)⁻¹ * q * (a * k)) =
        (projFin σ J k)⁻¹ * projFin σ J q * projFin σ J k := by
      simp only [map_mul, map_inv, hfa, one_mul]
    have := hqW _ hh
    rw [← e] at this
    exact this
  · rw [mul_assoc (γ * (a * k)), ofInf_projInf_mul_ofFin_projFin]
    group

end MainStatements.WeightKernel.Dec
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.DVariationb

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec

theorem variation : Variation := by
  intro F E _ _ _ _ _ σ hCM n J hJ k C hC f hf hfs hV z g e he
  have := GlobalTheory.UAut.locallyCompact_unipRad hCM hJ hC
  have hc : GlobalTheory.Cusp.Cocompact (ratPts σ J) (unipRad σ J C) := GlobalTheory.UAut.cocompact_unipRad hCM hJ hC
  have hcl : IsClosed (unipRad σ J C : Set (GAd σ J)) :=
    GlobalTheory.UAut.unipFlag_const (σ := σ) (J := J) C 0 ▸ GlobalTheory.UAut.isClosed_unipFlag hJ (sigma_sigma hCM) hC _
  let ν : Measure (unipRad σ J C) := Measure.haar
  have h𝓕 := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)) ν
  have hfin : ν (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C))) ≠ ⊤ := hc.measure_ne_top h𝓕
  have hpos : ν (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C))) ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne ν)
  let h : unipRad σ J C → ℂ := fun m => f (z * m * g)
  have hcont : Continuous h := by fun_prop
  let T := (Homeomorph.mulLeft z).trans (Homeomorph.mulRight g)
  have hK : IsCompact (T ⁻¹' tsupport f) := T.isCompact_preimage.2 hfs
  have hsupp : HasCompactSupport h :=
    HasCompactSupport.intro' (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK)
      ((isClosed_tsupport f).preimage (T.continuous.comp continuous_subtype_val))
      fun x hx => image_eq_zero_of_notMem_tsupport (f := f) (x := z * (x : GAd σ J) * g) hx
  have hint : Integrable h ν := hcont.integrable_of_hasCompactSupport hsupp
  have hV0 : ∫ m, h m ∂ν = 0 := hV ν z g
  let F' : (ratPts σ J).subgroupOf (unipRad σ J C) → unipRad σ J C → ℂ := fun γ x => h (γ • x)
  have hmeas : ∀ γ, AEStronglyMeasurable (F' γ) (ν.restrict (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)))) :=
    fun γ => (hcont.comp (continuous_const_smul γ)).aestronglyMeasurable
  have hlin : ∑' γ, ∫⁻ x in stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)), ‖F' γ x‖ₑ ∂ν ≠ ⊤ := by
    have hl : ∫⁻ x, ‖h x‖ₑ ∂ν = ∑' γ, ∫⁻ x in stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)), ‖F' γ x‖ₑ ∂ν := by
      rw [h𝓕.lintegral_eq_tsum' (fun x => ‖h x‖ₑ), ← (Equiv.inv _).tsum_eq]; simp [F']
    rw [← hl]; exact hint.2.ne
  have e1 : ∫ m, h m ∂ν = ∑' γ, ∫ x in stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)), F' γ x ∂ν := by
    rw [h𝓕.integral_eq_tsum' h hint, ← (Equiv.inv _).tsum_eq]; simp [F']
  have e2 := integral_tsum hmeas hlin
  have hΨ : ∀ x : unipRad σ J C, ∑' γ, F' γ x = nsum (NF σ J C) f z ((x : GAd σ J) * g) := fun x => by
    let eq : (ratPts σ J).subgroupOf (unipRad σ J C) ≃ NF σ J C :=
      { toFun := fun γ => ⟨γ.1.1, γ.2, γ.1.2⟩, invFun := fun ν => ⟨⟨ν.1, ν.2.2⟩, ν.2.1⟩,
        left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    rw [nsum, ← eq.tsum_eq]
    congr 1; funext γ
    show f (z * ((γ • x : unipRad σ J C) : GAd σ J) * g) = _
    rw [Subgroup.smul_def]; simp [eq, mul_assoc]
  have hzero : ∫ x in stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)),
      nsum (NF σ J C) f z ((x : GAd σ J) * g) ∂ν = 0 := by
    simp_rw [← hΨ]; rw [e2]; exact e1.symm.trans hV0
  have hae : ∀ᵐ x ∂(ν.restrict (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)))),
      HasSum (fun γ => F' γ x) (∑' γ, F' γ x) := by
    have h1 : ∫⁻ x in stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)), ∑' γ, ‖F' γ x‖ₑ ∂ν ≠ ⊤ := by
      rw [lintegral_tsum (fun γ => (hmeas γ).enorm)]; exact hlin
    filter_upwards [ae_lt_top' (AEMeasurable.tsum fun γ => (hmeas γ).enorm) h1] with x hx
    have hs : Summable fun γ => ‖F' γ x‖₊ :=
      ENNReal.tsum_coe_ne_top_iff_summable.1 (by simpa [enorm_eq_nnnorm] using hx.ne)
    exact (Summable.of_norm (NNReal.summable_coe.2 hs)).hasSum
  have hΨm : AEStronglyMeasurable (fun x : unipRad σ J C => ∑' γ, F' γ x)
      (ν.restrict (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)))) :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun s => by first
        | exact Finset.aestronglyMeasurable_fun_sum s fun γ _ => hmeas γ
        | exact Finset.aestronglyMeasurable_sum s fun γ _ => hmeas γ) hae
  haveI : IsFiniteMeasure (ν.restrict (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)))) :=
    isFiniteMeasure_restrict.2 hfin
  have hΨi : IntegrableOn (fun x : unipRad σ J C => nsum (NF σ J C) f z ((x : GAd σ J) * g))
      (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C))) ν := by
    refine Integrable.of_bound (C := e + ‖nsum (NF σ J C) f z g‖) ?_ (.of_forall fun x => ?_)
    · simpa only [hΨ] using hΨm
    · have := he x x.2
      calc _ = ‖(nsum (NF σ J C) f z ((x : GAd σ J) * g) - nsum (NF σ J C) f z g) + nsum (NF σ J C) f z g‖ := by
              rw [sub_add_cancel]
        _ ≤ _ := (norm_add_le _ _).trans (by linarith)
  have key : ν.real (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C))) • nsum (NF σ J C) f z g =
      ∫ x in stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)),
        (nsum (NF σ J C) f z g - nsum (NF σ J C) f z ((x : GAd σ J) * g)) ∂ν := by
    rw [integral_sub (integrable_const _) hΨi, hzero, setIntegral_const, sub_zero]
  have hb := norm_setIntegral_le_of_norm_le_const (μ := ν) hfin.lt_top
    (f := fun x : unipRad σ J C => nsum (NF σ J C) f z g - nsum (NF σ J C) f z ((x : GAd σ J) * g)) (C := e)
    (fun x _ => by rw [norm_sub_rev]; exact he x x.2)
  rw [← key, norm_smul, Real.norm_of_nonneg measureReal_nonneg] at hb
  have hp : 0 < ν.real (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C))) := ENNReal.toReal_pos hpos hfin
  nlinarith [norm_nonneg (nsum (NF σ J C) f z g)]

end MainStatements.WeightKernel.Dec
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.DecayFinal

section

@[expose] public section

namespace MainStatements.WeightKernel.Dec

theorem decay_holds : Decay :=
  decay (core derMem (derVan smOf derMem) level (sumSm smOf) variation nearCusp base) bridge

end MainStatements.WeightKernel.Dec
end
end
