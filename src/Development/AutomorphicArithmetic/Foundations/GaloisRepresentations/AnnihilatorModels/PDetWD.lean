module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.CommonModel
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericScale
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericMulOfProd
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisRepConjInvariant
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPotentiallySemistableCoefficientFieldEnlarge
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPstAtOfIsSstAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSstAtOfIsCrysAt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetCore
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetMem
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetSpan
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetWdLift
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetWeil
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PWdModel
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetBasis

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.detBasis_of :
    BasisIn := by
  intro C W X _ _ _ _ a mk hspan hfin
  obtain ⟨t, hts, hst, hli⟩ := exists_linearIndependent C (Set.range mk)
  have htop : ⊤ ≤ Submodule.span C (Set.range ((↑) : t → W)) := by
    rw [Subtype.range_coe, hst, hspan]
  let b₀ : Basis t C W := Basis.mk hli htop
  haveI : Finite t := Module.Finite.finite_basis b₀
  haveI : Fintype t := Fintype.ofFinite t
  have hcard : Fintype.card t = a := by
    rw [← hfin, Module.finrank_eq_card_basis b₀]
  let e : t ≃ Fin a := Fintype.equivFinOfCardEq hcard
  have hx : ∀ k : Fin a, ∃ x : X, mk x = ((e.symm k : t) : W) := fun k => hts (e.symm k).2
  choose x hx using hx
  refine ⟨x, b₀.reindex e, fun k => ?_⟩
  rw [Basis.reindex_apply, Basis.mk_apply, hx k]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetCo

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.detCo_of :
    CoFacts := by
  intro F L B _ _ _ _ _ a
  refine ⟨fun x y => ?_, ?_, ?_, ?_, ?_⟩
  · funext i
    simp [co, map_add (f := _)]
  · intro c x
    funext i
    show AlgebraTensorModule.map (LinearMap.proj i) LinearMap.id (c • x) =
      (c ⊗ₜ[F] (1 : B)) * AlgebraTensorModule.map (LinearMap.proj i) LinearMap.id x
    rw [map_smul, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
  · intro b x
    funext i
    induction x using TensorProduct.induction_on with
    | zero => simp [co]
    | tmul m n => simp [co, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp_all [co, mul_add]
  · intro T A hT s x
    funext i
    induction x using TensorProduct.induction_on with
    | zero => simp [co, Matrix.mulVec, dotProduct]
    | tmul m n =>
      simp [co, onR, hT, Matrix.mulVec, dotProduct, TensorProduct.sum_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy =>
      simp only [map_add (f := _), Pi.add_apply] at hx hy ⊢
      simp_all [co, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
  · convert (AlgebraTensorModule.congr (LinearEquiv.funUnique (Fin 1) L L)
      (LinearEquiv.refl F B)).bijective using 1
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp [co]
    | tmul m n => simp [co]
    | add x y hx hy => simp_all [co]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetCoLift

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison


theorem UpperTheory.Gal.crystallineComparison.detCoLift_of :
    CoFacts → WdLift → CoLift := by
  intro hco hwd l _ P ι K LL a ρ S _ _ π h1 h2
  obtain ⟨f1, f2, f3, -, -⟩ := hco ℚ_[l] ↥LL.1 (Bst P) a
  refine Exists.elim (hwd l P ι K LL (Fin a → ↥LL.1) ρ (Fin a → S)
    (fun x i => π (co (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P) i)) ?_ ?_ ?_)
    fun j hj => ⟨j, fun x i => by rw [hj]⟩
  · intro x y
    funext i
    rw [Submodule.coe_add, f1, Pi.add_apply, Pi.add_apply, map_add (f := _)]
  · intro c x
    funext i
    change π (co (c • (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P)) i) = _
    rw [f2, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, h1,
      Algebra.smul_def]
  · intro c x
    funext i
    have e : co (mulV P ↥LL.1 (Fin a → ↥LL.1) c (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P)) = _ :=
      f3 (algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c) (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P)
    show π (co (mulV P ↥LL.1 (Fin a → ↥LL.1) c (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P)) i) =
      ι (c : Om l) • π (co (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P) i)
    rw [e, Pi.smul_apply, smul_eq_mul, RingHom.map_mul π, h2, Algebra.smul_def]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetCommon

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.detCommon_of :
    CommonModel := by
  intro l _ P AI hT E Ω _ _ _ Gw O _ _ _ Bw a r c hr hc
  obtain ⟨T⟩ := hT
  obtain ⟨L₁, r₁, hm₁, hc₁⟩ := hr
  obtain ⟨L₂, c₂, hm₂, hp₂⟩ := hc
  have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  haveI := L₁.2
  haveI := (supExt L₁ L₂).2
  have hs₁ : IsSst P (Bw.repE L₁ r₁) := GlobalTheory.CrysSst.isSst_of_isCrys P AI T (Bw.repE L₁ r₁) hc₁
  have hs := GlobalTheory.AboveL.RepConj.isSst_enlarge P Bw l₁ r₁ hs₁
  refine ⟨supExt L₁ L₂, mapRep (IntermediateField.inclusion l₁).toRingHom r₁,
    mapRep (IntermediateField.inclusion l₂).toRingHom c₂, hm₁.enlarge l₁, hm₂.enlarge l₂, hs, ?_,
    GlobalTheory.PstExt.isPst_enlarge P Bw l₂ c₂ hp₂⟩
  haveI : FiniteDimensional ℚ_[l] (Fin a → ↥(supExt L₁ L₂).1) := Module.Finite.trans ↥(supExt L₁ L₂).1 _
  exact GlobalTheory.GalCut.IwaTwist.isPst_of_isSst P AI T _ hs
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetRingS

section

@[expose] public section

noncomputable section

open TensorProduct

namespace UpperTheory.Gal.crystallineComparison

theorem detRingS_of :
    RingS := by
  intro F L U B C _ _ _ _ _ _ _ _ _ _ _ τL τU h
  letI : Algebra U C := τU.toAlgebra
  let S := TensorProduct U C B
  have hS : Nontrivial S :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_right U C B τU.injective
  let ψ : B →+* S := (Algebra.TensorProduct.includeRight : B →ₐ[U] S).toRingHom
  have key : ∀ c : U, algebraMap C S (τU c) = (1 : C) ⊗ₜ[U] algebraMap U B c := by
    intro c
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    have e : τU c = c • (1 : C) := by
      rw [Algebra.smul_def, mul_one]
      rfl
    rw [e, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  letI : Algebra F S := (ψ.comp (algebraMap F B)).toAlgebra
  let φ : L →ₐ[F] S :=
    { (algebraMap C S).comp τL with
      commutes' := by
        intro z
        change algebraMap C S (τL (algebraMap F L z)) = ψ (algebraMap F B z)
        rw [h z, key, IsScalarTower.algebraMap_apply F U B z]
        rfl }
  let ψ' : B →ₐ[F] S := { ψ with commutes' := fun _ => rfl }
  let π : L ⊗[F] B →+* S :=
    (Algebra.TensorProduct.lift φ ψ' (fun _ _ => Commute.all _ _)).toRingHom
  refine ⟨S, inferInstance, inferInstance, π, hS, ?_, ?_⟩
  · intro x
    change φ x * ψ' 1 = _
    rw [map_one, mul_one]
    rfl
  · intro c
    change φ 1 * ψ' (algebraMap U B c) = _
    rw [map_one, one_mul, key]
    rfl

end UpperTheory.Gal.crystallineComparison
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetUnit

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.detUnit_of :
    UnitOfSpan := by
  intro S _ a v hv
  have hmem : ∀ i : Fin a, ∃ c : Fin a → S, ∑ k, c k • v k = Pi.single i 1 := fun i => by
    have h : (Pi.single i 1 : Fin a → S) ∈ Submodule.span S (Set.range v) := by
      rw [hv]; trivial
    exact (Submodule.mem_span_range_iff_exists_fun S).1 h
  choose c hc using hmem
  have hQN : (Matrix.of fun i k => v k i) * (Matrix.of fun k i => c i k) =
      (1 : Matrix (Fin a) (Fin a) S) := by
    ext i j
    have h := congrFun (hc j) i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply]
    simp only [mul_comm (v _ i)]
    rw [h, Pi.single_apply]
  exact Matrix.isUnit_det_of_right_inverse hQN
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetWD

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

namespace UpperTheory.Gal.crystallineComparison

private theorem roots_prod {W : Type} [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] (M : End ℂ W) :
    M.charpoly.roots.prod = LinearMap.det M := by
  classical
  let b := Module.finBasis ℂ W
  rw [← LinearMap.charpoly_toMatrix M b, ← LinearMap.det_toMatrix b M, Matrix.det_eq_prod_roots_charpoly]


theorem detWD_of (hW : WdModel) (hC : CommonModel) (hE : DetE) : DetWD := by
  intro l _ P AI hT ι E Ω _ _ _ _ _ A w h O _ _ _ Bw hj a r c hdet hr hc g hg
  obtain ⟨LL, r', c', m₁, m₂, hs, p₁, p₂⟩ := hC l P AI hT E Ω _ O Bw a r c hr hc
  have hd : ∀ x, Matrix.GeneralLinearGroup.det (c' x) = Matrix.GeneralLinearGroup.det (r' x) := by
    intro x
    have e := congrArg Units.val (hdet x)
    rw [← m₁.2, ← m₂.2] at e
    refine Units.ext ((algebraMap ↥LL.1 (Om l)).injective ?_)
    simp only [Matrix.GeneralLinearGroup.val_det_apply] at e ⊢
    rw [RingHom.map_det, RingHom.map_det]
    exact e
  have k := hE l P AI hT ι E Ω A w h O Bw hj a LL r' c' hd hs p₁ p₂ g hg
  have e₁ := (hW l P ι E Ω A w h O Bw hj a r LL r' m₁ p₁ g).1
  have e₂ := (hW l P ι E Ω A w h O Bw hj 1 c LL c' m₂ p₂ g).1
  haveI := p₁.finite
  haveI := p₂.finite
  exact ((congrArg (fun p : Polynomial ℂ => p.roots.prod) e₁).trans ((roots_prod _).trans (k.trans (roots_prod _).symm))).trans
    (congrArg (fun p : Polynomial ℂ => p.roots.prod) e₂).symm

theorem detWD_holds : DetWD :=
  detWD_of wdModel_of detCommon_of
    (detOne_of detCo_of detRingS_of (detCore_of detUnit_of detBasis_of) (detMem_of detCo_of) detWeil_of (detSpan_of detCo_of)
      (detCoLift_of detCo_of detWdLift_of))

end UpperTheory.Gal.crystallineComparison
end
end
