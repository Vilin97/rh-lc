module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubledLagrangianTermDependsOnlyOnIsotropicMeans
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankOrth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConjWeilDatumExchangedPairStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWittDecompositionIsotropicSplitUnipotent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacterStatement
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CompatibleThetaRestrictions
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittTowerRestrictionUnipotentRadicalInvariant
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubledLagrangianTermDependsOnlyOnIsotropicMeansStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.doubledLagrangian_term_depends_only_on_isotropic_means : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → ∀ (Y : Lag W) (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), IsLagFrame W Y C → ∀ (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I → Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) → ∀ (ν : Measure (Mx D s V.rank)) (𝓨 : Set (Mx D s V.rank)), IsCovolOne (GlobalTheory.MixModel.ratMx D s V.rank) ν 𝓨 → ∀ f₁ f₁' f₂ : WO V W → ℂ, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₁' → IsThetaFunO ψ V W f₂ → (∀ x : WO V W, HMul.hMul ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) I * W.gram).map (incA D)) x = (0 : Mx D s V.rank) → ∫ y in 𝓨, f₁ (HMul.hMul (I.map (incA D)) y + x) ∂ν = ∫ y in 𝓨, f₁' (HMul.hMul (I.map (incA D)) y + x) ∂ν) → lagTerm μ 𝓕 C f₁ f₂ = lagTerm μ 𝓕 C f₁' f₂ := by
  first | exact @GlobalTheory.LagMeans.lagTerm_eq_of_means | exact GlobalTheory.LagMeans.lagTerm_eq_of_means | (intros; apply GlobalTheory.LagMeans.lagTerm_eq_of_means <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilConstantTermSourceTargetConjAdjointCorr

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistSwap

open GlobalTheory.MixModel

variable {D : D7}

theorem covolOne_map {a b c d : ℕ} (f : Mx D a b ≃+ Mx D c d) (hf : Continuous f) (hfs : Continuous f.symm)
    (hΓ : ∀ x, f x ∈ ratMx D c d ↔ x ∈ ratMx D a b) {μ : Measure (Mx D a b)} {𝓖 : Set (Mx D a b)}
    (h : IsCovolOne (ratMx D a b) μ 𝓖) :
    IsCovolOne (ratMx D c d) (μ.map f) (f.symm ⁻¹' 𝓖) ∧
      ∀ g : Mx D c d → ℂ, ∫ x in f.symm ⁻¹' 𝓖, g x ∂(μ.map f) = ∫ y in 𝓖, g (f y) ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D a b
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := lattice_Mx D c d
  haveI : BorelSpace (Mx D a b) := ⟨rfl⟩
  haveI : BorelSpace (Mx D c d) := ⟨rfl⟩
  let m : Mx D a b ≃ᵐ Mx D c d :=
    { toEquiv := f.toEquiv
      measurable_toFun := hf.measurable
      measurable_invFun := hfs.measurable }
  have hm : (m : Mx D a b → Mx D c d) = f := rfl
  have hmp : MeasurePreserving m μ (μ.map f) := ⟨m.measurable, rfl⟩
  have hmp' : MeasurePreserving f.symm (μ.map f) μ := hmp.symm
  have hpre : f ⁻¹' (f.symm ⁻¹' 𝓖) = 𝓖 := by
    ext y; simp
  obtain ⟨hμ, hF, h1⟩ := h
  refine ⟨⟨f.isAddHaarMeasure_map μ hf hfs, ?_, ?_⟩, fun g => ?_⟩
  · let e : ratMx D a b → ratMx D c d := fun y => ⟨f y, (hΓ _).2 y.2⟩
    have he : Function.Bijective e := by
      constructor
      · intro x y hxy
        exact Subtype.ext (f.injective (congrArg Subtype.val hxy))
      · intro x
        refine ⟨⟨f.symm x, (hΓ _).1 (by simpa using x.2)⟩, Subtype.ext ?_⟩
        simp [e]
    refine hF.preimage_of_equiv hmp'.quasiMeasurePreserving he ?_
    intro y x
    simp [e, AddSubgroup.vadd_def]
  · rw [← hm, MeasurableEquiv.map_apply, hm, hpre, h1]
  · rw [← hm, m.measurableEmbedding.setIntegral_map, hm, hpre]

def swapE (S : HSp D) (t : ℕ) : Mx D S.rank t ≃+ Mx D t S.rank where
  toFun y := adj y ⬝ gA S
  invFun x := giA S ⬝ adj x
  left_inv y := by
    simp only [adj_mul, adj_gA, adj_adj, giA_gA_cancel]
  right_inv x := by
    simp only [adj_mul, adj_giA, adj_adj, Matrix.mul_assoc, giA_mul_gA, Matrix.mul_one]
  map_add' x y := by
    simp only [adj_add, Matrix.add_mul]

theorem swapE_apply (S : HSp D) (t : ℕ) (y : Mx D S.rank t) : swapE S t y = adj y ⬝ gA S := rfl

theorem swapE_symm_apply (S : HSp D) (t : ℕ) (x : Mx D t S.rank) : (swapE S t).symm x = giA S ⬝ adj x := rfl

theorem continuous_swapE (S : HSp D) (t : ℕ) : Continuous (swapE S t) :=
  continuous_adj.matrix_mul continuous_const

theorem continuous_swapE_symm (S : HSp D) (t : ℕ) : Continuous (swapE S t).symm :=
  continuous_const.matrix_mul continuous_adj

theorem swapE_mem_iff (S : HSp D) (t : ℕ) (y : Mx D S.rank t) :
    swapE S t y ∈ ratMx D t S.rank ↔ y ∈ ratMx D S.rank t := by
  constructor
  · intro hy
    have e : y = (swapE S t).symm (swapE S t y) := ((swapE S t).symm_apply_apply y).symm
    rw [e, swapE_symm_apply]
    exact ratMx_mul (rat_mem _) (ratMx_adj hy)
  · intro hy
    exact ratMx_mul (ratMx_adj hy) (rat_mem _)

theorem swapE_symm_mem_iff (S : HSp D) (t : ℕ) (x : Mx D t S.rank) :
    (swapE S t).symm x ∈ ratMx D S.rank t ↔ x ∈ ratMx D t S.rank := by
  rw [← swapE_mem_iff, AddEquiv.apply_symm_apply]

end GlobalTheory.TwistSwap

namespace GlobalTheory.TwistSwap

open GlobalTheory.MixModel

variable {D : D7}

theorem adjO_split (S T T' : HSp D) {t : ℕ} (ι : T'.V →ₗ[D.host.E] T.V) (C : Matrix (Fin T.rank) (Fin t) D.host.E)
    (y : Mx D S.rank t) (w' : WO T' S) :
    GlobalTheory.PairLift.adjO S T ((y : Matrix (Fin S.rank) (Fin t) (AE D)) *
                 GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.adel (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ct C * T.gram) +
      (w' : Matrix (Fin S.rank) (Fin T'.rank) (AE D)) *
        GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.adel (T'.gram⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ct (frameMat T T' ι) * T.gram)) =
    GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.adel C * (swapE S t y : Matrix (Fin t) (Fin S.rank) (AE D)) +
      GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.adel (frameMat T T' ι) * GlobalTheory.PairLift.adjO S T' w' := by
  have e1 : ∀ {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.adel x = rat x := fun _ => rfl
  have e2 : ∀ {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ct x = xᴴ := fun _ => rfl
  have e3 : ∀ (A B : HSp D) (z : WO B A), GlobalTheory.PairLift.adjO A B z = giA B ⬝ adj z ⬝ gA A := fun _ _ _ => rfl
  have g1 : ∀ A : HSp D, rat A.gram = gA A := fun _ => rfl
  have g2 : ∀ A : HSp D, rat A.gram⁻¹ = giA A := fun _ => rfl
  rw [e3, e3, e1, e1, e1, e2, e2, swapE_apply]
  simp only [e1, rat_mul, rat_conjTranspose, g1, g2, adj_add, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_assoc, giA_gA_cancel]

theorem res_dag_swap : ∀ (D : D7) (S T T' : HSp D) (t : ℕ) (ι : T'.V →ₗ[D.host.E] T.V) (C : Matrix (Fin T.rank) (Fin t) D.host.E), (∀ μ 𝓖, IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ratMx D t S.rank) μ 𝓖 → ∃ μ' 𝓖', IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ratMx D S.rank t) μ' 𝓖' ∧ ∀ φ : WO S T → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resS T T' S ι C μ' 𝓖' (GlobalTheory.PairLift.dag S T φ) = GlobalTheory.PairLift.dag S T' (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT S T T' ι C μ 𝓖 φ)) ∧ ∀ μ' 𝓖', IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ratMx D S.rank t) μ' 𝓖' → ∃ μ 𝓖, IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ratMx D t S.rank) μ 𝓖 ∧ ∀ φ : WO S T → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resS T T' S ι C μ' 𝓖' (GlobalTheory.PairLift.dag S T φ) = GlobalTheory.PairLift.dag S T' (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT S T T' ι C μ 𝓖 φ) := by
  intro D S T T' t ι C
  have key : ∀ (μ : Measure (Mx D t S.rank)) (𝓖 : Set (Mx D t S.rank)) (μ' : Measure (Mx D S.rank t))
      (𝓖' : Set (Mx D S.rank t)),
      (∀ G : Mx D t S.rank → ℂ, ∫ y in 𝓖', G (swapE S t y) ∂μ' = ∫ x in 𝓖, G x ∂μ) →
      ∀ φ : WO S T → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resS T T' S ι C μ' 𝓖' (GlobalTheory.PairLift.dag S T φ) =
        GlobalTheory.PairLift.dag S T' (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT S T T' ι C μ 𝓖 φ) := by
    intro μ 𝓖 μ' 𝓖' hI φ
    funext w'
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resS, GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT, GlobalTheory.PairLift.dag, adjO_split]
    rw [integral_conj, hI (fun x => φ (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.adel C * (x : Matrix (Fin t) (Fin S.rank) (AE D)) +
      GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.adel (frameMat T T' ι) * GlobalTheory.PairLift.adjO S T' w'))]
  refine ⟨fun μ 𝓖 h => ?_, fun μ' 𝓖' h => ?_⟩
  · obtain ⟨h1, h2⟩ := covolOne_map (swapE S t).symm (continuous_swapE_symm S t) (continuous_swapE S t)
      (swapE_symm_mem_iff S t) h
    refine ⟨_, _, h1, key μ 𝓖 _ _ fun G => ?_⟩
    exact (h2 fun y => G (swapE S t y)).trans (by simp)
  · obtain ⟨h1, h2⟩ := covolOne_map (swapE S t) (continuous_swapE S t) (continuous_swapE_symm S t) (swapE_mem_iff S t) h
    exact ⟨_, _, h1, key _ _ μ' 𝓖' fun G => (h2 G).symm⟩

end GlobalTheory.TwistSwap
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilConstantTermSourceTargetConjAdjointCorrStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weilConstantTerm_source_target_conjAdjoint_corr : ∀ (D : D7) (S T T' : HSp D) (t : ℕ) (ι : T'.V →ₗ[D.host.E] T.V) (C : Matrix (Fin T.rank) (Fin t) D.host.E), (∀ μ 𝓖, IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ratMx D t S.rank) μ 𝓖 → ∃ μ' 𝓖', IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ratMx D S.rank t) μ' 𝓖' ∧ ∀ φ : WO S T → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resS T T' S ι C μ' 𝓖' (GlobalTheory.PairLift.dag S T φ) = GlobalTheory.PairLift.dag S T' (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT S T T' ι C μ 𝓖 φ)) ∧ ∀ μ' 𝓖', IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ratMx D S.rank t) μ' 𝓖' → ∃ μ 𝓖, IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ratMx D t S.rank) μ 𝓖 ∧ ∀ φ : WO S T → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resS T T' S ι C μ' 𝓖' (GlobalTheory.PairLift.dag S T φ) = GlobalTheory.PairLift.dag S T' (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT S T T' ι C μ 𝓖 φ) := by
  first | exact @GlobalTheory.TwistSwap.res_dag_swap | exact GlobalTheory.TwistSwap.res_dag_swap | (intros; apply GlobalTheory.TwistSwap.res_dag_swap <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunIsotropicMeanUnipotentInvariant

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.TargetUnipMean

open GlobalTheory.MixModel (rat)
open scoped GlobalTheory.MixModel

variable {D : D7}

theorem exists_split (W : HSp D) {s : ℕ} (I : Matrix (Fin W.rank) (Fin s) D.host.E) (hI : IsIsoFrame W I) :
    ∃ (W' : HSp D) (ι : W'.V →ₗ[D.host.E] W.V), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit W W' I (frameMat W W' ι) := by
  obtain ⟨e, rfl⟩ := GlobalTheory.BesselCompare.eMat_surj W I
  have he : LinearIndependent D.host.E e :=
    LinearIndependent.of_comp W.frame.equivFun.toLinearMap hI.2.1
  have hiso : ∀ a b, W.hT (e a) (e b) = 0 := fun a b => by
    rw [← GlobalTheory.BesselCompare.cT_mul, hI.2.2]; rfl
  obtain ⟨W', ι, h1, h2, h3⟩ := GlobalTheory.WittLow.exists_lower Examples₂.star_isIntegral W e he hiso
  refine ⟨W', ι, ⟨hI, ?_, ?_, by omega⟩⟩
  · refine Matrix.ext fun a b => ?_
    unfold GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj
    rw [GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.cT_mul]
    exact h2 _ _
  · refine Matrix.ext fun a b => ?_
    unfold GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj
    rw [GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.cT_mul, ← W.herm.eq, h3]
    simp

theorem decomp {W W' : HSp D} {s k : ℕ} {I : Matrix (Fin W.rank) (Fin s) D.host.E}
    {B : Matrix (Fin W.rank) (Fin W'.rank) D.host.E} (hsp : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit W W' I B) (x : Mx D W.rank k)
    (hx : rat (Iᴴ * W.gram) ⬝ x = 0) : ∃ (z : Mx D s k) (w : Mx D W'.rank k), x = rat I ⬝ z + rat B ⬝ w := by
  obtain ⟨d, hde, hdi, -⟩ := GlobalTheory.WittSect.exists_hypDec_mem_NI D W W' s I B hsp
  have h := d.sum_eq_one_rat
  simp only [GlobalTheory.MixModel.HypDec.qX, GlobalTheory.MixModel.HypDec.qY, GlobalTheory.MixModel.HypDec.q0, hde, hdi] at h
  have h1 : rat (1 : Matrix (Fin W.rank) (Fin W.rank) D.host.E) ⬝ x = x := by
    rw [GlobalTheory.MixModel.rat_one, Matrix.one_mul]
  rw [← h, GlobalTheory.MixModel.rat_add, GlobalTheory.MixModel.rat_add, Matrix.add_mul, Matrix.add_mul] at h1
  have h2 : rat (d.e' * (Iᴴ * W.gram)) ⬝ x = 0 := by
    rw [GlobalTheory.MixModel.rat_mul, Matrix.mul_assoc, hx, Matrix.mul_zero]
  rw [h2, add_zero] at h1
  rw [GlobalTheory.MixModel.rat_mul I, GlobalTheory.MixModel.rat_mul B, Matrix.mul_assoc (rat I), Matrix.mul_assoc (rat B)] at h1
  exact ⟨_, _, h1.symm⟩

theorem periodic {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {g : WO V W → ℂ} (hg : IsThetaFunO ψ V W g) {s : ℕ}
    (I : Matrix (Fin W.rank) (Fin s) D.host.E) (p : WO V W) (hp : rat (Iᴴ * W.gram) ⬝ p = 0)
    (γ : Matrix (Fin s) (Fin V.rank) D.host.E) : g (rat I ⬝ rat γ + p) = g p := by
  have e1 : rat I ⬝ rat γ = ratW W V (I * γ) := by rw [GlobalTheory.MixModel.ratW_eq, GlobalTheory.MixModel.rat_mul]
  have e2 : GlobalTheory.MixModel.adj p ⬝ rat (W.gram * I) = 0 := by
    have := congrArg GlobalTheory.MixModel.adj hp
    rwa [GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_zero, ← GlobalTheory.MixModel.rat_conjTranspose, conjTranspose_mul,
      GlobalTheory.MixModel.gram_conjTranspose, conjTranspose_conjTranspose] at this
  have e3 : GlobalTheory.MixModel.adj p ⬝ (GlobalTheory.MixModel.gA W ⬝ ratW W V (I * γ)) = 0 := by
    have e2' : GlobalTheory.MixModel.adj p ⬝ (rat W.gram ⬝ rat I) = 0 := by rw [← GlobalTheory.MixModel.rat_mul]; exact e2
    rw [GlobalTheory.MixModel.ratW_eq, GlobalTheory.MixModel.gA, GlobalTheory.MixModel.rat_mul I γ, ← Matrix.mul_assoc (rat W.gram) (rat I) (rat γ),
      ← Matrix.mul_assoc, e2', Matrix.zero_mul]
  rw [e1, hg.quasi, GlobalTheory.MixModel.symplOH_eq, GlobalTheory.MixModel.hO_eq_trace, e3, Matrix.mul_zero, Matrix.trace_zero,
    map_zero, neg_zero, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.TargetUnipMean

namespace GlobalTheory.TargetUnipMean

open GlobalTheory.MixModel (rat)
open scoped GlobalTheory.MixModel

theorem mean_unip : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χV χW om → ∀ (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I → ∀ (ν : Measure (Mx D s V.rank)) (𝓨 : Set (Mx D s V.rank)), IsCovolOne (GlobalTheory.MixModel.ratMx D s V.rank) ν 𝓨 → ∀ n ∈ NI W I, ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f → ∀ x : WO V W, HMul.hMul ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) I * W.gram).map (incA D)) x = (0 : Mx D s V.rank) → ∫ y in 𝓨, om (1, n) f (HMul.hMul (I.map (incA D)) y + x) ∂ν = ∫ y in 𝓨, f (HMul.hMul (I.map (incA D)) y + x) ∂ν := by
  intro D ψ V W χV χW om hom s I hI ν 𝓨 hν n hn f hf x hx
  obtain ⟨W', ι, hsp⟩ := exists_split W I hI
  obtain ⟨omt, hmt, hsw⟩ := GlobalTheory.T.exists_conj_weilDatum_exchangedPair D ψ V W χV χW om hom
  obtain ⟨μ', 𝓖', hμ', he⟩ := (GlobalTheory.T.weilConstantTerm_source_target_conjAdjoint_corr D V W W' s ι I).1 ν 𝓨 hν
  have hlaw := GlobalTheory.T.hermitianAdjoint_laws_standardCharacter D ψ hom.std V W'
  have hlawW := GlobalTheory.T.hermitianAdjoint_laws_standardCharacter D ψ hom.std V W
  have hr : GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT V W W' ι I ν 𝓨 (om (1, n) f) = GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT V W W' ι I ν 𝓨 f := by
    have h1 := GlobalTheory.UnipRes.res_unip D W W' V s I (frameMat W W' ι) hsp ψ χW χV omt hmt μ' 𝓖' hμ' ⟨n, hn⟩
      (GlobalTheory.PairLift.dag V W f) (hlawW.theta f hf)
    have h2 : GlobalTheory.PairLift.dag V W' (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT V W W' ι I ν 𝓨 (om (1, n) f)) =
        GlobalTheory.PairLift.dag V W' (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT V W W' ι I ν 𝓨 f) := by
      rw [← he, ← he, ← hsw]
      exact h1
    funext w
    have h3 := congrFun h2 (GlobalTheory.PairLift.adjO W' V w)
    simp only [GlobalTheory.PairLift.dag, hlaw.invol] at h3
    exact (starRingEnd ℂ).injective h3
  have hII : Iᴴ * W.gram * I = 0 := hI.2.2
  have hIB : Iᴴ * W.gram * frameMat W W' ι = 0 := hsp.orth
  obtain ⟨z, w, hz⟩ := decomp hsp x hx
  have hred : ∀ g, IsThetaFunO ψ V W g → ∫ y in 𝓨, g (HMul.hMul (I.map (incA D)) y + x) ∂ν =
      GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT V W W' ι I ν 𝓨 g w := by
    intro g hg
    have hper : ∀ γ ∈ GlobalTheory.MixModel.ratMx D s V.rank, ∀ a : Mx D s V.rank,
        g (rat I ⬝ (γ + a) + rat (frameMat W W' ι) ⬝ w) = g (rat I ⬝ a + rat (frameMat W W' ι) ⬝ w) := by
      intro γ hγ a
      obtain ⟨γ0, rfl⟩ := GlobalTheory.MixModel.mem_ratMx.1 hγ
      rw [Matrix.mul_add, add_assoc]
      refine periodic hg I _ ?_ γ0
      rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← GlobalTheory.MixModel.rat_mul, ← GlobalTheory.MixModel.rat_mul, hII,
        hIB, GlobalTheory.MixModel.rat_zero, GlobalTheory.MixModel.rat_zero, Matrix.zero_mul, Matrix.zero_mul, add_zero]
    have := GlobalTheory.MixModel.covolOne_integral_add hν (fun a => g (rat I ⬝ a + rat (frameMat W W' ι) ⬝ w)) hper z
    rw [hz]
    calc ∫ y in 𝓨, g (HMul.hMul (I.map (incA D)) y + (rat I ⬝ z + rat (frameMat W W' ι) ⬝ w)) ∂ν
        = ∫ y in 𝓨, g (rat I ⬝ (y + z) + rat (frameMat W W' ι) ⬝ w) ∂ν := by
          congr 1
          funext y
          show g (rat I ⬝ y + _) = _
          rw [Matrix.mul_add, add_assoc]
      _ = _ := this
  rw [hred (om (1, n) f) (hom.om_pres (1, n) f hf), hred f hf, hr]

end GlobalTheory.TargetUnipMean
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunIsotropicMeanUnipotentInvariantStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.thetaFun_isotropic_mean_unipotent_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χV χW om → ∀ (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I → ∀ (ν : Measure (Mx D s V.rank)) (𝓨 : Set (Mx D s V.rank)), IsCovolOne (GlobalTheory.MixModel.ratMx D s V.rank) ν 𝓨 → ∀ n ∈ NI W I, ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f → ∀ x : WO V W, HMul.hMul ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) I * W.gram).map (incA D)) x = (0 : Mx D s V.rank) → ∫ y in 𝓨, om (1, n) f (HMul.hMul (I.map (incA D)) y + x) ∂ν = ∫ y in 𝓨, f (HMul.hMul (I.map (incA D)) y + x) ∂ν := by
  first | exact @GlobalTheory.TargetUnipMean.mean_unip | exact GlobalTheory.TargetUnipMean.mean_unip | (intros; apply GlobalTheory.TargetUnipMean.mean_unip <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TermInv

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.TermInvProof

theorem termInv : ∀ D : D7, TermInv D := by
  intro D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS Y s I hI hY n hn f₁ f₂ hf₁ hf₂
  obtain ⟨ν, 𝓨, hν⟩ := GlobalTheory.MixModel.exists_isCovolOne (D := D) (m := s) (n := V.rank)
  exact GlobalTheory.T.doubledLagrangian_term_depends_only_on_isotropic_means D ψ hS.weil.std V W μ 𝓕 hS.covol Y (fr Y) (hS.frame Y) s I hI hY ν 𝓨 hν _ _ f₂
    (hS.weil.om_pres _ f₁ hf₁) hf₁ hf₂
    (fun x hx => GlobalTheory.T.thetaFun_isotropic_mean_unipotent_invariant D ψ V W χV χW om hS.weil s I hI ν 𝓨 hν n hn f₁ hf₁ x hx)

end GlobalTheory.TermInvProof

end
end
end
