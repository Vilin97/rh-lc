module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHeckeOpFullDualLab
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfTwoMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigenSysOfHeckeLin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactLevelOffFinEmpty
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.CommensuratedOfIsOpenIsCompact
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HostPrimeSplitting.FinrankOE
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BoundedAutomorphicRightTranslationUnitarisableBoStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParamTrivialBoundUnitaryGLStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParameterTrivialBoundUnramifiedUnitaStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicSphericalEigenfunctionLocalHeckeAlgebraEig

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinZeta

variable {D : D7}

theorem isUnram_of_not_isSplit {v : HeightOneSpectrum (𝓞 D.host.F)} (hs : ¬ IsSplit (E := D.host.E) v) :
    Formalism.MainNotions.SchurIrreducible.IsUnram (E := D.host.E) v := by
  intro P hP
  have hPv : P.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hP
  have hmem : ∀ Q : HeightOneSpectrum (𝓞 D.host.E),
      Q ∈ Formalism.L2.Host.aboveF (L := D.host.E) D.host.F (P.under (𝓞 D.host.F)) ↔ Q.under (𝓞 D.host.F) = v := by
    intro Q
    rw [hPv]
    simp only [Formalism.L2.Host.aboveF, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have h1 : (Formalism.L2.Host.aboveF (L := D.host.E) D.host.F (P.under (𝓞 D.host.F))).card = 1 := by
    refine Finset.card_eq_one.2 ⟨P, Finset.eq_singleton_iff_unique_mem.2 ⟨(hmem P).2 hPv, fun Q hQ => ?_⟩⟩
    by_contra hne
    exact hs ⟨Q, P, hne, congrArg HeightOneSpectrum.asIdeal ((hmem Q).1 hQ), hP⟩
  exact PI.UnitaryGroupMassFormula.HostPrimeFacts.unram D.R D.host P h1

theorem exists_cartan (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    ∃ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), ∀ g : Gv V v,
      ∃ k₁ ∈ Kv V v, ∃ k₂ ∈ Kv V v, ∃ (g' : Gv V v) (a : GL (Fin V.rank) (w.adicCompletion D.host.E))
        (d : Fin V.rank → ℤ) (u : Fin V.rank → w.adicCompletion D.host.E),
        IsFrameAt w (frameLat V) a ∧ Antitone d ∧ (∀ i, Valued.v (u i) = WithZero.exp (-d i)) ∧
        (a⁻¹ * locMat D.sp.cm.sig V.gram h g' * a).1 = Matrix.diagonal u ∧ g = k₁ * g' * k₂ := by
  have hL := GlobalTheory.HeckeDual.isLattice_frameLat V
  have hH := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V
  have hspan : Submodule.span D.host.E (frameLat V : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have hfull : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra h
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨x, hx, hx₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e x ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
        intro y hy
        have hxy : V.hT (e x) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
        have hyx : V.hT y (e x) = 0 := by
          rw [(V.herm.eq (e x) y).symm, hxy, map_zero]
        simp [hyx]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e x)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (R := 𝓞 D.host.E) (S := D.host.E)
          (FaithfulSMul.algebraMap_injective _ _) (Field.toIsField _))
    have heq : (frameLat V : Set (Fin V.rank → D.host.E)) =
        V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) :=
      (V.frame.equivFun.toEquiv.image_eq_preimage_symm _).symm
    rw [heq, ← Submodule.map_span, hfull, Submodule.map_top, LinearEquiv.range]
  have hd := GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat D V v
  by_cases hsp : IsSplit (E := D.host.E) v
  · obtain ⟨w, -, -, hw, -⟩ := id hsp
    have h : w.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hw
    obtain ⟨e, ⟨⟨a, ha, e1⟩, e2⟩, -⟩ :=
      GlobalTheory.LFun.SplitChart.exists_isSplitChart (isCMExt_host D) hH hL.fg hspan h hsp hd
    refine ⟨w, h, fun g => ?_⟩
    obtain ⟨ϖ, hϖ⟩ := exists_isUnifV w
    obtain ⟨d, hdA, k₁, h₁, k₂, h₂, eg⟩ := Formalism.UG.Final.CartanDecomp D.host.E w V.rank ϖ (mem_Ov_of_isUnifV hϖ) hϖ (e g)
    refine ⟨e.symm k₁, (e2 _).2 (by simpa using h₁), e.symm k₂, (e2 _).2 (by simpa using h₂),
      e.symm (k₁⁻¹ * e g * k₂⁻¹), a, d, fun i => ϖ ^ d i, ha, hdA, fun i => ?_, ?_, ?_⟩
    · rw [map_zpow₀, show Valued.v ϖ = WithZero.exp (-1 : ℤ) from hϖ, ← WithZero.exp_zsmul]
      simp
    · rw [← e1, e.apply_symm_apply, Units.val_mul, Units.val_mul, eg, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      rfl
    · apply e.injective
      simp only [map_mul, e.apply_symm_apply]
      group
  · obtain ⟨w, hw⟩ := ((exists_isInertChart _ (isCMExt_host D) v).1 (isUnram_of_not_isSplit hsp)).resolve_left hsp
    have h : w.under (𝓞 D.host.F) = v := (GlobalTheory.LFun.InertChart.under_eq_iff hw w).2 rfl
    obtain ⟨-, ⟨c, hc, -⟩, -, -, hrest⟩ := (exists_isInertChart _ (isCMExt_host D) v).2 w h hw
    obtain ⟨⟨ϖ, hU⟩, hch⟩ := hrest c hc
    obtain ⟨e, ⟨-, ⟨a, ha, -, e1⟩, e2⟩, -⟩ := hch _ _ _ hH hL.fg hspan hd
    refine ⟨w, h, fun g => ?_⟩
    obtain ⟨d, t, hdA, ht, k₁, h₁, k₂, h₂, eg⟩ := GlobalTheory.LFun.cartanU hU (e g)
    refine ⟨e.symm k₁, (e2 _).2 (by simpa using h₁), e.symm k₂, (e2 _).2 (by simpa using h₂),
      e.symm t, a, d, fun i => ϖ ^ d i, ha, hdA, fun i => ?_, by rw [← e1, e.apply_symm_apply, ht], ?_⟩
    · rw [map_zpow₀, show Valued.v ϖ = WithZero.exp (-1 : ℤ) from hU.2.2.2.1, ← WithZero.exp_zsmul]
      simp
    · apply e.injective
      simp only [map_mul, e.apply_symm_apply, eg]

theorem eigen_heckeAlg : ∀ (D : D7) (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), SphOff J χ Sb → ∀ v ∉ Sb, ∀ f : GA D V → ℂ, (∀ k ∈ J, ∀ g, f (g * k) = χ k * f g) → ∀ c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, (∀ w d R, Hecke₂ V J χ Sb w d R → heckeLin V R f = c w d • f) → f ∈ fixed ((rightReg ℂ (GA D V) ℂ).comp (embV V v)) (Kv V v) ∧ ∀ h ∈ Hecke ℂ (Kv V v), ∃ a : ℂ, heckeVec ((rightReg ℂ (GA D V) ℂ).comp (embV V v)) (Kv V v) h f = a • f := by
  intro D V J χ Sb hJ v hv f hf c hc
  have hfix : f ∈ fixed ((rightReg ℂ (GA D V) ℂ).comp (embV V v)) (Kv V v) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => funext (fixed_of_level hJ hv hf hk)
  refine ⟨hfix, fun x hx => ?_⟩
  obtain ⟨w, h, hcart⟩ := exists_cartan V v
  have hs := isEigenSys_of_heckeLin hJ hv h hfix (hc w)
  have := GlobalTheory.AdelicU.SelfDual.isLattice_frameLat V
  have hK : IsCommensurated (Kv V v) := PI.UnitaryGroupMassFormula.AdIndexEq.commensurated_of_isOpen_isCompact _
    (isOpen_stabLoc D.sp.cm.sig V.gram (frameLat V) v) (isCompact_stabLoc D.sp.cm.sig V.gram (frameLat V) v)
  have hm := Formalism.UG.Final.DosetIndMem (Gv V v) (Kv V v) ℂ
  refine GlobalTheory.LFun.hecke_induction (K := Kv V v)
    (p := fun h => ∃ a : ℂ, heckeVec ((rightReg ℂ (GA D V) ℂ).comp (embV V v)) (Kv V v) h f = a • f)
    ⟨0, by simp [heckeVec]⟩ ?_ ?_ hx
  · rintro g1 hg1 g2 hg2 ⟨a1, e1⟩ ⟨a2, e2⟩
    exact ⟨a1 + a2, by rw [GlobalTheory.LFun.heckeVec_add hK _ hg1 hg2, e1, e2, add_smul]⟩
  · intro r g
    obtain ⟨k₁, hk₁, k₂, hk₂, g', a, d, u, ha, hd, hu, hg, rfl⟩ := hcart g
    refine ⟨r * c w (List.ofFn d), ?_⟩
    rw [GlobalTheory.LFun.dosetInd_mul hk₁ hk₂, GlobalTheory.LFun.heckeVec_smul hK _ r (hm g'), hs a g' d u ha hd hu hg, smul_smul]

end GlobalTheory.FinZeta
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicSphericalEigenfunctionLocalHeckeAlgebraEigStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adelicSphericalEigenfunction_local_heckeAlgebra_eigen : ∀ (D : D7) (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), SphOff J χ Sb → ∀ v ∉ Sb, ∀ f : GA D V → ℂ, (∀ k ∈ J, ∀ g, f (g * k) = χ k * f g) → ∀ c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, (∀ w d R, Hecke₂ V J χ Sb w d R → heckeLin V R f = c w d • f) → f ∈ fixed ((rightReg ℂ (GA D V) ℂ).comp (embV V v)) (Kv V v) ∧ ∀ h ∈ Hecke ℂ (Kv V v), ∃ a : ℂ, heckeVec ((rightReg ℂ (GA D V) ℂ).comp (embV V v)) (Kv V v) h f = a • f := by
  first | exact @GlobalTheory.FinZeta.eigen_heckeAlg | exact GlobalTheory.FinZeta.eigen_heckeAlg | (intros; apply GlobalTheory.FinZeta.eigen_heckeAlg <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParametersBoundedEigenfunction

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinZeta.ParamBound

section General

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem heckeVec_map_of_injective {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W} {K : Subgroup G}
    (f : V →ₗ[ℂ] W) (hf : Function.Injective f) (hρ : ∀ g y, f (ρ g y) = ρ' g (f y)) (h : G → ℂ) (x : V) :
    f (heckeVec ρ K h x) = heckeVec ρ' K h (f x) := by
  unfold heckeVec
  have hs : (Function.support fun c : G ⧸ K => h c.out • ρ' c.out (f x)) =
      Function.support fun c : G ⧸ K => h c.out • ρ c.out x := by
    ext c
    simp only [Function.mem_support, ne_eq, ← hρ, ← map_smul]
    exact not_congr (map_eq_zero_iff f hf)
  by_cases hfin : (Function.support fun c : G ⧸ K => h c.out • ρ c.out x).Finite
  · rw [map_finsum f hfin]
    simp only [map_smul, hρ]
  · rw [finsum_of_infinite_support hfin, finsum_of_infinite_support (hs ▸ hfin), map_zero]

theorem comp_mem_hecke (e : G ≃* H) {K : Subgroup G} {K' : Subgroup H} (hK : ∀ g, g ∈ K ↔ e g ∈ K')
    {h' : H → ℂ} (hh : h' ∈ Hecke ℂ K') : h' ∘ e ∈ Hecke ℂ K := by
  classical
  obtain ⟨h1, S, hS⟩ := hh
  refine ⟨fun a b g => ?_, S.image e.symm, fun g hg => ?_⟩
  · show h' (e (a * g * b)) = h' (e g)
    rw [map_mul, map_mul]
    exact h1 ⟨e a, (hK a).1 a.2⟩ ⟨e b, (hK b).1 b.2⟩ (e g)
  · obtain ⟨s, hs, a, b, hab⟩ := hS (e g) hg
    refine ⟨e.symm s, Finset.mem_image_of_mem _ hs, ⟨e.symm a, (hK _).2 (by simp)⟩,
      ⟨e.symm b, (hK _).2 (by simp)⟩, ?_⟩
    apply e.injective
    simp [hab]

theorem isUnitarisable_comp {ρ : Representation ℂ G V} (hρ : IsUnitarisable ρ) (φ : H →* G) :
    IsUnitarisable (ρ.comp φ) := by
  obtain ⟨B, h1, h2, h3⟩ := hρ
  exact ⟨B, h1, h2, fun g => h3 (φ g)⟩

end General

theorem norm_le_of_mem_bcParam {q n : ℕ} (hq : 2 ≤ q) {α : Fin (n / 2) → ℂˣ}
    (hα : GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q n α) :
    ∀ b ∈ bcParam n α, ‖(b : ℂ)‖ ≤ ((q : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2) := by
  intro b hb
  simp only [bcParam, Multiset.mem_add, Multiset.mem_map, Finset.mem_univ_val, true_and,
    Multiset.mem_replicate] at hb
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq2 : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
  rcases hb with (⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨hn, rfl⟩
  · exact (hα i).2
  · rw [Units.val_inv_eq_inv_val, norm_inv]
    have hpos : 0 < ((q : ℝ) ^ 2) ^ (-(((n : ℝ) - 1) / 2)) := Real.rpow_pos_of_pos hq2 _
    calc ‖(α i : ℂ)‖⁻¹ ≤ (((q : ℝ) ^ 2) ^ (-(((n : ℝ) - 1) / 2)))⁻¹ := inv_anti₀ hpos (hα i).1
      _ = _ := by rw [Real.rpow_neg hq2.le, inv_inv]
  · simp only [Units.val_one, norm_one]
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    exact Real.one_le_rpow (by nlinarith) (by linarith)

theorem exists_param_at (D : D7) (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (hJ : SphOff J χ Sb) (f : GA D V → ℂ) (hfm : f ∈ bddAut V)
    (hf0 : f ≠ 0) (hlev : ∀ k ∈ J, ∀ g, f (g * k) = χ k * f g) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ)
    (hc : ∀ w d R, Hecke₂ V J χ Sb w d R → heckeLin V R f = c w d • f)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : v ∉ Sb) (w : HeightOneSpectrum (𝓞 D.host.E))
    (h : w.under (𝓞 D.host.F) = v) :
    ∃ B : Multiset ℂˣ, IsParamVec D.sp.cm.sig V.gram (frameLat V) h
        ((rightReg ℂ (GA D V) ℂ).comp (embV V v)) f B ∧
      ∀ b ∈ B, ‖(b : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((V.rank : ℝ) - 1) / 2) := by
  obtain ⟨hfix, heig⟩ := GlobalTheory.T.adelicSphericalEigenfunction_local_heckeAlgebra_eigen D V J χ Sb hJ v hv f hlev c hc
  let ρ : Representation ℂ (Gv V v) (bddAut V) := (bddRep V).comp (embV V v)
  let x : bddAut V := ⟨f, hfm⟩
  have hx0 : x ≠ 0 := fun e => hf0 (congrArg Subtype.val e)
  have hint : ∀ g y, (bddAut V).subtype (ρ g y) =
      ((rightReg ℂ (GA D V) ℂ).comp (embV V v)) g ((bddAut V).subtype y) := fun _ _ => rfl
  have hxfix : x ∈ fixed ρ (Kv V v) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext ((GlobalTheory.LGrp.mem_fixed.1 hfix) k hk)
  have hxeig : ∀ hh ∈ Hecke ℂ (Kv V v), ∃ a : ℂ, heckeVec ρ (Kv V v) hh x = a • x := fun hh hm => by
    obtain ⟨a, ha⟩ := heig hh hm
    refine ⟨a, Subtype.val_injective ?_⟩
    have := heckeVec_map_of_injective (K := Kv V v) (bddAut V).subtype Subtype.val_injective hint hh x
    exact this.trans ha
  have hρU : IsUnitarisable ρ := isUnitarisable_comp (GlobalTheory.T.boundedAutomorphicRightTranslation_unitarisable_bounded D V).1 _
  have hH := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V
  have hL := GlobalTheory.HeckeDual.isLattice_frameLat V
  have hspan : Submodule.span D.host.E (frameLat V : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have hfull : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra h
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨x, hx, hx₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e x ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
        intro y hy
        have hxy : V.hT (e x) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
        have hyx : V.hT y (e x) = 0 := by
          rw [(V.herm.eq (e x) y).symm, hxy, map_zero]
        simp [hyx]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e x)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (R := 𝓞 D.host.E) (S := D.host.E)
          (FaithfulSMul.algebraMap_injective _ _) (Field.toIsField _))
    have heq : (frameLat V : Set (Fin V.rank → D.host.E)) =
        V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) :=
      (V.frame.equivFun.toEquiv.image_eq_preimage_symm _).symm
    rw [heq, ← Submodule.map_span, hfull, Submodule.map_top, LinearEquiv.range]
  have hd := GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat D V v
  have hun : Formalism.MainNotions.SchurIrreducible.IsUnram (E := D.host.E) v := fun P _ => by
    haveI := GlobalTheory.BaseChangeExistsCompare.unram_of_cm D D.sp.cm P
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  rcases (exists_isInertChart _ (isCMExt_host D) v).1 hun with hs | ⟨w', hw'⟩
  · obtain ⟨e, he, -, -⟩ := SplitChart.exists_isSplitChart (isCMExt_host D) hH hL.fg hspan h hs hd
    have hfix' := (mem_fixed_comp_symm (ρ := ρ) e he.2).2 hxfix
    obtain ⟨B, hB, hbd⟩ := GlobalTheory.T.exists_satakeParam_trivialBound_unitaryGL D.host.E w V.rank (bddAut V) (ρ.comp e.symm.toMonoidHom)
      (isUnitarisable_comp hρU _) x hx0 hfix' fun h' hh' => by
        rw [heckeVec_comp_symm e he.2 hh'.1 hxfix]
        exact hxeig _ (comp_mem_hecke e he.2 hh')
    exact ⟨B, Or.inl ⟨hs, e, he, hB.map (bddAut V).subtype (fun g y => rfl) hf0⟩, fun b hb => (hbd b hb).1⟩
  · have h' : w'.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext (v.isMaximal.eq_of_le
      (Ideal.comap_ne_top _ w'.isPrime.ne_top) (Ideal.map_le_iff_le_comap.1 (le_of_eq hw'))).symm
    obtain ⟨-, -, huniq, -, -⟩ := (exists_isInertChart _ (isCMExt_host D) v).2 w' h' hw'
    obtain rfl : w = w' := (huniq w).1 h
    obtain ⟨-, ⟨τ, hτ, -⟩, -, hnorm, hconj⟩ := (exists_isInertChart _ (isCMExt_host D) v).2 w h hw'
    obtain ⟨⟨ϖ, hϖ⟩, hch⟩ := hconj τ hτ
    obtain ⟨e, he, -, -⟩ := hch V.rank V.gram (frameLat V) hH hL.fg hspan hd
    have hfix' := (mem_fixed_comp_symm (ρ := ρ) e he.2.2).2 hxfix
    obtain ⟨α, hα, hbd⟩ := GlobalTheory.T.exists_satakeParameter_trivialBound_unramifiedUnitary (w.adicCompletion D.host.E) ϖ τ (qV D.host.F v) V.rank hϖ (bddAut V)
      (ρ.comp e.symm.toMonoidHom) (isUnitarisable_comp hρU _) x hx0 hfix' fun h'' hh'' => by
        rw [heckeVec_comp_symm e he.2.2 hh''.1 hxfix]
        exact hxeig _ (comp_mem_hecke e he.2.2 hh'')
    refine ⟨bcParam V.rank α,
      Or.inr ⟨hw', τ, ϖ, e, α, hϖ, he, hα.map hϖ (bddAut V).subtype (fun g y => rfl) hf0, rfl⟩, ?_⟩
    intro b hb
    rw [hnorm, Nat.cast_pow]
    exact norm_le_of_mem_bcParam hϖ.2.2.2.2.2.1 hbd b hb

end GlobalTheory.FinZeta.ParamBound

namespace GlobalTheory.FinZeta.ParamBound

theorem exists_param_bounded : ∀ (D : D7) (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), SphOff J χ Sb → ∀ f ∈ bddAut V, f ≠ 0 → (∀ k ∈ J, ∀ g, f (g * k) = χ k * f g) → ∀ c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, (∀ w d R, Hecke₂ V J χ Sb w d R → heckeLin V R f = c w d • f) → ∃ B : Fam D.host.E, IsParamFunV V Sb f B ∧ Bounded (above D.host.E (Sb : Set (HeightOneSpectrum (𝓞 D.host.F)))) B V.rank (((V.rank : ℝ) - 1) / 2) := by
  intro D V J χ Sb hJ f hfm hf0 hlev c hc
  classical
  have key := fun (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : v ∉ Sb) (w : HeightOneSpectrum (𝓞 D.host.E))
      (h : w.under (𝓞 D.host.F) = v) => exists_param_at D V J χ Sb hJ f hfm hf0 hlev c hc v hv w h
  let B : Fam D.host.E := fun w =>
    if hw : w.under (𝓞 D.host.F) ∉ Sb then (key _ hw w rfl).choose else 0
  have hB : ∀ w (hw : w.under (𝓞 D.host.F) ∉ Sb), B w = (key _ hw w rfl).choose := fun w hw => dif_pos hw
  refine ⟨B, ?_, ?_⟩
  · intro v hv w h
    subst h
    have hv' : w.under (𝓞 D.host.F) ∉ Sb := hv
    rw [hB w hv']
    exact (key _ hv' w rfl).choose_spec.1
  · intro w hw
    have hw' : w.under (𝓞 D.host.F) ∉ Sb := hw
    rw [hB w hw']
    exact ⟨(IsParamVec.card (key _ hw' w rfl).choose_spec.1).le, (key _ hw' w rfl).choose_spec.2⟩

end GlobalTheory.FinZeta.ParamBound

end
end
end
