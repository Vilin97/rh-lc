module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormBlockEmbLeftInvariant
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockEmbeddingUnipotentMemFlagUnipotentRadicalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactStandardParabolicUnipotentRadicalWittFrStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAlongSubset
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockProjectionFlagUnipotentRadicalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnipotentRadicalEqLeviMulUnipotentStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicUnipotentMono
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.CuspidalConstantTerms.IntegralSectionEqConstTermOn
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockEmbeddingRationalGLMemRationalPoints

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CuspBlockRat

theorem blockEmb_ratGL_mem_ratPts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      ∀ γ : GL (Fin d) E, ι (GlobalTheory.CuspRep.ratGL E d γ) ∈ ratPts σ J := by
  intro F E _ _ _ _ _ _ σ _ n J _ r Xf Yf _ l d h ι hι γ
  obtain ⟨Φ, j, -, -, hj, hΦ, hmat⟩ := hι
  have hΦE : ∀ x : E, Φ (inclR (F := F) (AF F) x) = algebraMap E (AdeleRing (𝓞 E) E) x := fun x => by
    rw [hΦ]
    refine Prod.ext ?_ ?_
    · show j (GlobalTheory.LFun.infTens F E ((1 : AF F) ⊗ₜ[F] x)) = algebraMap E (InfiniteAdeleRing E) x
      rw [← hj x]
      congr 1
    · show GlobalTheory.LFun.finAdEquiv F E (GlobalTheory.LFun.finTens F E ((1 : AF F) ⊗ₜ[F] x)) =
        algebraMap E (FiniteAdeleRing (𝓞 E) E) x
      have e : GlobalTheory.LFun.finTens F E ((1 : AF F) ⊗ₜ[F] x) = (1 : Af F) ⊗ₜ[F] x := by simp [GlobalTheory.LFun.finTens]
      rw [e, show GlobalTheory.LFun.finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = _ from GlobalTheory.LFun.toFinAd_tmul 1 x, map_one, one_mul]
  have hΦs : ∀ x : E, Φ.symm (algebraMap E (AdeleRing (𝓞 E) E) x) = inclR (F := F) (AF F) x := fun x => by
    rw [RingEquiv.symm_apply_eq, hΦE]
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) := by
    intro x y hxy
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    have := congrArg (fun z => (Φ z).1 w) hxy
    simp only [hΦE] at this
    exact (algebraMap E w.Completion).injective this
  have hrat : ∀ δ : GL (Fin d) E, (GlobalTheory.CuspRep.ratGL E d δ).1.map Φ.symm = δ.1.map (inclR (F := F) (AF F)) :=
    fun δ => by
      ext a b
      exact hΦs (δ.1 a b)
  refine GlobalTheory.CuspBlockLeft.mem_ratPts_of _ (1 + GlobalTheory.BlockForms.blkCols h Xf * (γ.1 - 1) *
      (cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Yf) * J) +
    GlobalTheory.BlockForms.blkCols h Yf * (cT (σ : E →+* E) (γ⁻¹).1 - 1) *
      (cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Xf) * J)) ?_ hinj
  rw [hmat, ← map_inv, hrat, hrat, GlobalTheory.CuspBlockLeft.cT_inclR]
  simp [Matrix.map_add (f := _), Matrix.map_sub, Matrix.map_mul, Matrix.map_one]

end GlobalTheory.CuspBlockRat

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockEmbeddingRationalGLMemRationalPointsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.blockEmbedding_rationalGL_mem_rationalPoints : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      ∀ γ : GL (Fin d) E, ι (GlobalTheory.CuspRep.ratGL E d γ) ∈ ratPts σ J := by
  first | exact @GlobalTheory.CuspBlockRat.blockEmb_ratGL_mem_ratPts | exact GlobalTheory.CuspBlockRat.blockEmb_ratGL_mem_ratPts | (intros; apply GlobalTheory.CuspBlockRat.blockEmb_ratGL_mem_ratPts <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryGLBlockEmbeddingPolynomialEntri

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped TensorProduct

namespace GlobalTheory.BlockForms


open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
theorem isBlockEmb_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      Continuous ι := by
  intro F E _ _ _ _ _ _ σ hσ n J _ r Xf Yf _ l d h ι hι
  obtain ⟨Φ, j, _, hΦs, -, -, hform⟩ := hι
  haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ hσ.2.2.1
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hsig : Continuous (sigR (AF F) σ) := by
    have hc := IsModuleTopology.continuous_of_linearMap (R := AF F) (LinearMap.baseChange (AF F) σ.toLinearMap)
    refine hc.congr fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a y => simp [LinearMap.baseChange_tmul, sigR]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have h1 : Continuous fun g : GlobalTheory.CuspRep.GA E d => g.1.map Φ.symm :=
    Units.continuous_val.matrix_map hΦs
  have h2 : Continuous fun g : GlobalTheory.CuspRep.GA E d => (g⁻¹).1.map Φ.symm :=
    Units.continuous_coe_inv.matrix_map hΦs
  have h3 : Continuous fun g : GlobalTheory.CuspRep.GA E d => Matrix.transpose (((g⁻¹).1.map Φ.symm).map (sigR (AF F) σ)) :=
    (h2.matrix_map hsig).matrix_transpose
  have hM : Continuous fun g : GlobalTheory.CuspRep.GA E d => (matHom _ σ J (ι g)).1 := by
    refine Continuous.congr ?_ fun g => (hform g).symm
    exact (continuous_const.add ((continuous_const.matrix_mul (h1.sub continuous_const)).matrix_mul continuous_const)).add
      ((continuous_const.matrix_mul (h3.sub continuous_const)).matrix_mul continuous_const)
  have hMi : Continuous fun g : GlobalTheory.CuspRep.GA E d => ((matHom _ σ J (ι g))⁻¹ : GL (Fin n) (AF F ⊗[F] E)).1 := by
    refine (hM.comp continuous_inv).congr fun g => ?_
    simp only [Function.comp_apply, map_inv]
  exact (isEmbedding_matHom (AF F) σ J).continuous_iff.2 (Units.continuous_iff.2 ⟨hM, hMi⟩)

end GlobalTheory.BlockForms
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryGLBlockEmbeddingPolynomialEntriStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.continuous_unitaryGLBlockEmbedding_polynomial_entries : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      Continuous ι := by
  first | exact @GlobalTheory.BlockForms.isBlockEmb_continuous | exact GlobalTheory.BlockForms.isBlockEmb_continuous | (intros; apply GlobalTheory.BlockForms.isBlockEmb_continuous <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicUnipotentMonoStatement

section

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

theorem _root_.GlobalTheory.T.standardParabolicUnipotent_mono : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (S T : Finset (Fin r)), T ⊆ S → GlobalTheory.StdPar.unip σ J X T ≤ GlobalTheory.StdPar.unip σ J X S := by
  first | exact @GlobalTheory.StdPar.unip_mono_of_subset | exact GlobalTheory.StdPar.unip_mono_of_subset | (intros; apply GlobalTheory.StdPar.unip_mono_of_subset <;> assumption)
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.CuspidalConstantTerms.IsCuspidalCompBlockEmb

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open MeasureTheory

namespace GlobalTheory.BlockForms.CuspConst.Rg

theorem continuous_unip (E : Type) [Field E] [NumberField E] (d r' : ℕ) :
    Continuous fun x : GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E => GlobalTheory.CuspRep.unip x := by
  have hn : Continuous fun x : GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E => (GlobalTheory.CuspRep.nilM x : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Ad E)) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [GlobalTheory.CuspRep.nilM, Matrix.of_apply]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_const.add hn
  · exact continuous_const.sub hn


open GlobalTheory.Cusp GlobalTheory.AutomorphicL2Unitary in
theorem isCuspidal_comp_blockEmb : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (ψ : GAd σ J → ℂ), GlobalTheory.StdPar.IsCuspOn σ J Xf Yf S K ψ → ∀ g₀ : GAd σ J,
        (∀ k : GlobalTheory.CuspRep.Kinf E d, g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀ ∈ K) →
        GlobalTheory.CuspRep.IsCuspidal (fun x => ψ (ι x * g₀)) := by
  intro F E _ _ _ _ _ _ σ hσ n J hJ r X Y hW K _ S l d h ι hι _ hS hk hl ψ hψ g₀ _
  intro r' hr0 hr1 _ _ μ 𝓕 hμ h𝓕 g
  let k : Fin r := ⟨l + r' - 1, by omega⟩
  have hkv : k.val + 1 = l + r' := by simp only [k]; omega
  have hkS : k ∉ S := hS k (by simp only [k]; omega) (by simp only [k]; omega)
  have hSS : S ⊂ insert k S := Finset.ssubset_insert hkS
  set U := GlobalTheory.StdPar.unip σ J X (insert k S) with hU
  set U₀ := GlobalTheory.StdPar.unip σ J X S with hU₀
  have hle : U₀ ≤ U := GlobalTheory.T.standardParabolicUnipotent_mono F E σ hσ n J hJ r X Y hW _ S (Finset.subset_insert _ _)
  haveI : LocallyCompactSpace U₀ := (GlobalTheory.StdPar.isClosed_unip S hσ hJ hW).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace U := (GlobalTheory.StdPar.isClosed_unip _ hσ hJ hW).isClosedEmbedding_subtypeVal.locallyCompactSpace
  have cS := GlobalTheory.T.cocompact_standardParabolicUnipotentRadical_wittFrame F E σ hσ n J hJ r X Y hW S
  have cS' := GlobalTheory.T.cocompact_standardParabolicUnipotentRadical_wittFrame F E σ hσ n J hJ r X Y hW (insert k S)
  have esub : ∀ {N : Subgroup (GAd σ J)}, N ≤ U → (ratPts σ J ⊓ U).subgroupOf N = (ratPts σ J).subgroupOf N := by
    intro N hN
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, hN x.2⟩⟩
  have cinf : ∀ {N : Subgroup (GAd σ J)}, N ≤ U → Cocompact (ratPts σ J) N → Cocompact (ratPts σ J ⊓ U) N := by
    intro N hN hc
    unfold Cocompact
    rw [esub hN]
    exact hc
  have hfΓ : LeftInv (ratPts σ J ⊓ U) ψ := fun γ hγ g => by
    obtain ⟨m, hm, hmL, ν, hν, e⟩ := GlobalTheory.T.rational_unipotentRadical_eq_levi_mul_unipotent F E σ hσ n J hJ r X Y hW S (insert k S) (Finset.subset_insert _ _) γ hγ.1 hγ.2
    rw [e, mul_assoc, hψ.1.leftM m hm hmL, hψ.1.leftN ν hν]
  have hnorm : ∀ p ∈ U, ∀ u ∈ U₀, p * u * p⁻¹ ∈ U₀ := by
    intro p hp u hu
    by_cases hS0 : S = ∅
    · subst hS0
      rw [hU₀, GlobalTheory.StdPar.unip_empty, Subgroup.mem_bot] at hu ⊢
      simp [hu]
    obtain ⟨mS, hmS, hmS'⟩ : ∃ m ∈ S, ∀ k ∈ S, k ≤ m := ⟨S.max' (Finset.nonempty_iff_ne_empty.2 hS0),
      S.max'_mem _, fun k hk => S.le_max' k hk⟩
    have hσσ := sigma_sigma hσ
    have eS := GlobalTheory.ConstTrans.unip_eq_unipFlag F E σ hσ n J hJ r X Y hW S mS hmS hmS'
    have hCS : IsIsoCols σ J (GlobalTheory.StdPar.initCols X mS) := isIsoCols_of_isWittFrame hW hσσ hJ mS.2
    rw [hU₀, eS] at hu ⊢
    exact conj_mem_unipFlag hJ hσσ hCS _ (GlobalTheory.ConstTrans.unip_le_parFlag F E σ hσ n J hJ r X Y hW (insert k S) S mS
      (Finset.subset_insert _ _) hmS hmS' hp) hu
  obtain ⟨π, hπc, hπm, hπs, hπk, hπr⟩ := GlobalTheory.T.exists_blockProjection_flagUnipotentRadical F E σ hσ n J hJ r X Y hW S l d h ι hι hS hk hl r' hr0 hr1 k hkv
  have hrat := GlobalTheory.T.blockEmbedding_rationalGL_mem_rationalPoints F E σ hσ n J hJ r X Y hW l d h ι hι
  have hιc := GlobalTheory.T.continuous_unitaryGLBlockEmbedding_polynomial_entries F E σ hσ n J hJ r X Y hW l d h ι hι
  have hsN := GlobalTheory.T.blockEmbedding_unipotent_mem_flagUnipotentRadical F E σ hσ n J hJ r X Y hW S l d h ι hι hS hk hl r' hr0 hr1 k hkv

  have h0 : constTermOn (ratPts σ J ⊓ U) U ψ (ι g * g₀) = 0 := by
    obtain ⟨μN, 𝓕N, h1, h2, h3⟩ := exists_mass_one cS'
    rw [constTermOn_eq_of_measure_eq_one ((esub le_rfl).symm ▸ h2) h3 hfΓ]
    exact (hψ.2 _ hSS μN 𝓕N h1 h2 h3 (ι g * g₀)).symm
  have key := GlobalTheory.Cusp.Shear.Rg.integral_section_eq_constTermOn (GAd σ J) (ratPts σ J ⊓ U) U U₀ hle hnorm (cinf le_rfl cS') (cinf hle cS)
    (GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E) (GlobalTheory.CuspRep.ratN E d r') (fun x => ι (GlobalTheory.CuspRep.unip x)) π
    (hιc.comp (continuous_unip E d r')) (fun v w => by rw [GlobalTheory.CuspRep.unip_add, map_mul]) hsN hπc hπm hπs hπk
    (fun v hv => by
      obtain ⟨x, rfl⟩ := hv
      refine ⟨?_, hsN _⟩
      have := GlobalTheory.CuspRep.unip_algebraMap (a := d) (r := r') x
      exact this ▸ hrat _)
    (fun a ha => hπr a ha.1) ψ hfΓ hψ.1.cont (fun m hm g => hψ.1.leftN m hm g) μ 𝓕 hμ h𝓕 (ι g * g₀)
  rw [h0, smul_zero] at key
  simpa only [map_mul, mul_assoc] using key

end GlobalTheory.BlockForms.CuspConst.Rg

end
end
end
