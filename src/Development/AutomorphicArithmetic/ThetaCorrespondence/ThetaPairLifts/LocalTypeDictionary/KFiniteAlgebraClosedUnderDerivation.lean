module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeights
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFinitePiTensorSumOfFactorOperators
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLinesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectorsStatement
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialSpaceEqFockImageOfArchLawsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchrodingerMapExistsOfArchHeisenbergDerivaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieFirstOfLieSecond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFockVacuumLineUniqueOfHeisenbergDerivatiStatement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfMapPderivEqAndMapOneNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LieSecondOrderOfRealLift
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WeilLieAlgebraScalarAction
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgebraicModelInvariantSub

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.SquareAgree.KFinAlg

def tensDeg (F : Type) [Field F] [NumberField F] (P Q R S D : ℕ) : Submodule ℂ (GlobalTheory.RealLift.Tens F P Q R S) :=
  LinearMap.range (PiTensorProduct.map fun _ : InfinitePlace F =>
    (MvPolynomial.restrictTotalDegree (Formalism.BasicNotions.TH.Ix P Q × Formalism.BasicNotions.TH.Ix R S) ℂ D).subtype)

theorem tensDeg_mono {F : Type} [Field F] [NumberField F] {P Q R S D D' : ℕ} (h : D ≤ D') :
    tensDeg F P Q R S D ≤ tensDeg F P Q R S D' := by
  have hi : MvPolynomial.restrictTotalDegree (Formalism.BasicNotions.TH.Ix P Q × Formalism.BasicNotions.TH.Ix R S) ℂ D ≤
      MvPolynomial.restrictTotalDegree _ ℂ D' := fun x hx => by
    rw [MvPolynomial.mem_restrictTotalDegree] at hx ⊢; omega
  rintro _ ⟨t, rfl⟩
  refine ⟨PiTensorProduct.map (fun _ => Submodule.inclusion hi) t, ?_⟩
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  rfl

theorem exists_tensDeg {F : Type} [Field F] [NumberField F] {P Q R S : ℕ} (T : GlobalTheory.RealLift.Tens F P Q R S) :
    ∃ D, T ∈ tensDeg F P Q R S D := by
  classical
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    refine ⟨Finset.univ.sup fun w => (m w).totalDegree, r • PiTensorProduct.tprod ℂ (fun w =>
      (⟨m w, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 (Finset.le_sup (f := fun w => (m w).totalDegree)
        (Finset.mem_univ w))⟩ : MvPolynomial.restrictTotalDegree _ ℂ _)), ?_⟩
    simp [PiTensorProduct.map_tprod]
  | add x y hx hy =>
    obtain ⟨D₁, h₁⟩ := hx
    obtain ⟨D₂, h₂⟩ := hy
    exact ⟨max D₁ D₂, Submodule.add_mem _ (tensDeg_mono (le_max_left _ _) h₁) (tensDeg_mono (le_max_right _ _) h₂)⟩

theorem exp_stable {V : Type} [AddCommGroup V] [Module ℂ V] {L U : Module.End ℂ V} (hU : GlobalTheory.RealLift.IsExp L U)
    (N : Submodule ℂ V) (hN : ∀ y ∈ N, L y ∈ N) : ∀ y ∈ N, U y ∈ N := by
  intro y hy
  by_contra hne
  obtain ⟨l, hl1, hl2⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hne inferInstance
  have hpow : ∀ m : ℕ, (L ^ m) y ∈ N := by
    intro m
    induction m with
    | zero => simpa using hy
    | succ m ih => rw [pow_succ', Module.End.mul_apply]; exact hN _ ih
  have hz : ∀ m : ℕ, ((m.factorial : ℂ))⁻¹ * l ((L ^ m) y) = 0 := fun m => by
    have hm : l ((L ^ m) y) ∈ N.map l := Submodule.mem_map_of_mem (hpow m)
    rw [hl2, Submodule.mem_bot] at hm
    rw [hm, mul_zero]
  have h1 := hU y l
  simp only [hz] at h1
  exact hl1 (h1.unique hasSum_zero)

def pureL {κ : Type} [Fintype κ] {F : Type} [Field F] [NumberField F]
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun f := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ
  map_add' f g := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
  map_smul' c f := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

end GlobalTheory.SquareAgree.KFinAlg
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanMatricesTriple

section

@[expose] public section

noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.RealLift.FockFirst

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_map_piInf {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j

  change infEmb τ (compInf F E w ((1 : AF F) ⊗ₜ[F] J i j)) = τ.1 (J i j)
  simp [compInf, infEmb_tmul]

theorem hasExp_div (τ : ∀ w : InfinitePlace F, EmbOver E w) {χ χ' : Chr F E} {m m' : InfinitePlace F → ℤ}
    (h : HasExp τ χ m) (h' : HasExp τ χ' m') : HasExp τ (χ / χ') (fun w => m w - m' w) := by
  intro z hz
  rw [MonoidHom.div_apply, Circle.coe_div, h z hz, h' z hz, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_

  have h0 : piInf (τ w) (z : AE F E) ≠ 0 := (z.isUnit.map (piInf (τ w))).ne_zero
  have hne : piInf (τ w) (z : AE F E) / (‖piInf (τ w) (z : AE F E)‖ : ℂ) ≠ 0 :=
    div_ne_zero h0 (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h0))
  rw [zpow_sub₀ hne]

end SlopeTestRemainingChoices

end GlobalTheory.RealLift.FockFirst

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsFockMapFirstOrderOfRealLift

section

@[expose] public section

section
noncomputable section
open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
namespace GlobalTheory.RealLift.FockFirst
section SlopeTestRemainingChoices
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end SlopeTestRemainingChoices
theorem exists_fockMap_first_order_of_real_lift (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W)
    (om' : Rep σ G.V' G.W) (h : IsTriple B G X om om') :
    ∃ (A : InfinitePlace F → Matrix (Fin a) (Ix (a - G.p) G.p) ℂ)
      (Φ : Tens F (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')))
      (c : InfinitePlace F → ℂ),
      (∀ w, IsFrame ((1 : ℂ) • (incM F G.V.J).map (piInf (B.emb w))) (A w)) ∧
      (∀ w, G.V.θ w * A w = A w * Jm (a - G.p) G.p) ∧
      LinearMap.range Φ = G.M.Pol B.ψ B.emb ∧
      ActsBy B.emb A (om.comp (MonoidHom.inl _ _)) Φ
        (fockAct1 (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q)) c := by
  obtain ⟨hb, hg, hc, hw, -⟩ := h
  choose A hA hAθ using fun w => GlobalTheory.RealLift.frameEx_holds _ _ _ _ _ (hg.hV.sig w) (hg.hV.cartan w)
  choose C hC hCθ using fun w => GlobalTheory.RealLift.frameEx_holds _ _ _ _ _ (hg.hW.sig w) (hg.hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F G.W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_piInf]; exact hC w
  have fr : Framed B.emb (incM F G.V.J) (incM F G.W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  have hder : DerEx := GlobalTheory.T.archHeisenbergDerivatives_exist
  have hvl : VacLine := GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hder
  have hfe : FockEx := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hder
  have hsec : LieSecond := _root_.GlobalTheory.T.real_lift_lie_second_order hP hder hfe hvl (_root_.GlobalTheory.T.weil_lie_algebra_scalar_action hP hder hvl)
  have hfst : LieFirst := GlobalTheory.RealLift.LieFirstPf.lieFirst_of_lieSecond hsec
  have hpr : PolRange := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws GlobalTheory.RealLift.actsLaws hder hvl
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := hpr F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hw
  obtain ⟨d, hd, hB1⟩ := hwp.2.1
  have hW1 := hfst F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co d 1 Complex.I A C Φ _ _ _ hb.cm hb.std fr hΦ hd hB1
    (hasExp_div B.emb hc.expβ hc.expα)
  exact ⟨A, Φ, _, hA1, hAθ, hr, hW1⟩
end GlobalTheory.RealLift.FockFirst
end
end

section

theorem _root_.GlobalTheory.T.real_lift_exists_fock_map : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∃ (A : NumberField.InfinitePlace F → Matrix (Fin a) (Formalism.BasicNotions.TH.Ix (a - Γ.p) Γ.p) ℂ)
      (Φ : GlobalTheory.RealLift.Tens F (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q) →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))
      (c : NumberField.InfinitePlace F → ℂ),
      (∀ w, GlobalTheory.RealLift.IsFrame ((1 : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.V.J).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w))) (A w)) ∧
      (∀ w, Γ.V.θ w * A w = A w * Formalism.BasicNotions.TH.Jm (a - Γ.p) Γ.p) ∧
      LinearMap.range Φ = Γ.M.Pol Bs.ψ Bs.emb ∧
      GlobalTheory.RealLift.ActsBy Bs.emb A (om.comp (MonoidHom.inl _ _)) Φ
        (Formalism.BasicNotions.TH.fockAct1 (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q)) c := by
  first | exact @_root_.GlobalTheory.RealLift.FockFirst.exists_fockMap_first_order_of_real_lift | exact _root_.GlobalTheory.RealLift.FockFirst.exists_fockMap_first_order_of_real_lift | (intros; apply _root_.GlobalTheory.RealLift.FockFirst.exists_fockMap_first_order_of_real_lift <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KFiniteAlgebraClosedUnderDerivation

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.SquareAgree.KFinAlg
theorem polynomial_vector_kFinite (fockFirst : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∃ (A : InfinitePlace F → Matrix (Fin a) (Formalism.BasicNotions.TH.Ix (a - Γ.p) Γ.p) ℂ)
      (Φ : GlobalTheory.RealLift.Tens F (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q) →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))
      (c : InfinitePlace F → ℂ),
      (∀ w, GlobalTheory.RealLift.IsFrame ((1 : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.V.J).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w))) (A w)) ∧
      (∀ w, Γ.V.θ w * A w = A w * Formalism.BasicNotions.TH.Jm (a - Γ.p) Γ.p) ∧
      LinearMap.range Φ = Γ.M.Pol Bs.ψ Bs.emb ∧
      GlobalTheory.RealLift.ActsBy Bs.emb A (om.comp (MonoidHom.inl _ _)) Φ
        (Formalism.BasicNotions.TH.fockAct1 (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q)) c) : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' → ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb,
    ∃ P : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))), FiniteDimensional ℂ P ∧ P ≤ Γ.M.Pol Bs.ψ Bs.emb ∧
      f ∈ P ∧ ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ Γ.V Bs.emb, ∀ g ∈ P, ∃ g₁ ∈ P,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (k, 1)) (⇑g) (⇑g₁) := by
  intro hPr F E _ _ _ _ _ σ Bs a a' Γ Xc om om' hT f hf
  classical
  obtain ⟨A, Φ, c, hA, hAθ, hr, hact⟩ := fockFirst hPr F E σ Bs a a' Γ Xc om om' hT
  have hb := hT.base
  have hwp : GlobalTheory.WeilM.IsUWeilPair (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.WeilM.adeleClass F) Bs.ψ (-1)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.V.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.W.J) Γ.M.co Xc.β (Xc.β / Xc.α) om := hT.weil
  have hadm := fun g => (hwp.isUSplitting).adm g
  rw [← hr] at hf
  obtain ⟨T, rfl⟩ := hf
  obtain ⟨D, hD⟩ := exists_tensDeg T
  haveI : FiniteDimensional ℂ (tensDeg F (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q) D) :=
    LinearMap.finiteDimensional_range _
  refine ⟨(tensDeg F _ _ _ _ D).map Φ, inferInstance, hr ▸ LinearMap.map_le_range, ⟨T, hD, rfl⟩, ?_⟩
  rintro k hk _ ⟨T', hT', rfl⟩
  obtain ⟨γ, hγ, Yg, hgen, hKC, hγ1⟩ := GlobalTheory.RealLift.kLine_of_lineEx GlobalTheory.T.unitaryLieElements_generate_oneParamLines F E σ (Fin a) _ _ Bs.emb
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.V.J) 1 A Γ.V.θ hb.cm hA hAθ k hk.1 hk.2
  let L := GlobalTheory.RealLift.sumPl (fun w => Formalism.BasicNotions.TH.fockAct1 (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q) (Yg w) +
    (c w * (Yg w).trace) • (1 : Module.End ℂ _))
  have hloc : GlobalTheory.RealLift.LocFin L := GlobalTheory.RealLift.locFin_sumPl _ _ _ fun w v => by
    obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights _ _ _ _).1 v
    exact ⟨W, hW, hv, fun y hy => W.add_mem (hs (Yg w) (hKC w) y hy) (W.smul_mem _ hy)⟩
  obtain ⟨U, hexp, hSA⟩ := GlobalTheory.T.weakExponential_action_on_fockVectors F (Fin a × Fin (a + a')) _ Φ L ((om.comp (MonoidHom.inl _ _)).comp γ) hloc
    (fun t l hl => hadm _ l hl) (fun T => hact γ hγ Yg hgen T)
  let Lw : ∀ w : InfinitePlace F, Module.End ℂ (Formalism.BasicNotions.TH.Pol (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q)) :=
    fun w => Formalism.BasicNotions.TH.fockAct1 (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q) (Yg w) +
      (c w * (Yg w).trace) • (1 : Module.End ℂ _)
  let Nw : ∀ w : InfinitePlace F, Submodule ℂ (Formalism.BasicNotions.TH.Pol (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q)) :=
    fun _ => MvPolynomial.restrictTotalDegree _ ℂ D
  have hN : ∀ i, ∀ z ∈ Nw i, Lw i z ∈ Nw i := by
    intro i z hz
    simp only [Lw, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact Submodule.add_mem _ (GlobalTheory.FockPolGK.kStable1 _ _ _ _ D (Yg i) (hKC i) z hz) (Submodule.smul_mem _ _ hz)
  have hLst : ∀ y ∈ tensDeg F _ _ _ _ D, L y ∈ tensDeg F _ _ _ _ D := by
    intro y hy
    change GlobalTheory.RealLift.sumPl Lw y ∈ _
    rw [GlobalTheory.RealLift.sumPl, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun w _ => GlobalTheory.RealLift.atPl_mem_range_map Lw Nw hN w y hy
  refine ⟨Φ (U T'), ⟨U T', exp_stable hexp _ hLst T' hT', rfl⟩, ?_⟩
  have h1 := hSA T'
  change GlobalTheory.RealLift.SA (om (γ (Multiplicative.ofAdd 1), 1)) (Φ T') (Φ (U T')) at h1
  rw [hγ1] at h1
  exact (GlobalTheory.RealLift.actsLaws F _ (Φ T') (Φ (U T')) (Φ (U T'))).2.1 _ (map_zero _) h1
theorem derivation_algebra_kFinite : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' → ∀ ΦD ∈ GlobalTheory.SquareAgree.algD Γ.M Bs.ψ Bs.emb,
    ∃ U : Submodule ℂ ((Fin a × Fin (a + a') → AF F) → ℂ), FiniteDimensional ℂ U ∧
      U ≤ GlobalTheory.SquareAgree.algD Γ.M Bs.ψ Bs.emb ∧ ΦD ∈ U ∧
      ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ Γ.V Bs.emb, ∀ x ∈ U, om (k, 1) x ∈ U := by
  intro hPr F E _ _ _ _ _ σ Bs a a' Γ Xc om om' hT ΦD hΦ
  have hPair := GlobalTheory.ThK.RealUniq.isPair_V hT
  have hstdM := hPair.good.std
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hf, hSB, hcof, rfl⟩ := hx
    obtain ⟨P, hPfin, hPle, hfP, hPst⟩ := _root_.GlobalTheory.SquareAgree.KFinAlg.polynomial_vector_kFinite _root_.GlobalTheory.T.real_lift_exists_fock_map hPr F E σ Bs a a' Γ Xc om om' hT f hf
    have hstd : ∀ᶠ v in Filter.cofinite,
        φ v = Set.indicator {x : Fin a × Fin (a + a') → Fv F v |
          ∀ j, x j ∈ v.adicCompletionIntegers F} 1 := by
      filter_upwards [hcof, hstdM] with v h1 h2
      rw [h1, h2]
    refine ⟨P.map (pureL φ), inferInstance, ?_, ⟨f, hfP, rfl⟩, ?_⟩
    · rintro _ ⟨g, hg, rfl⟩
      exact Submodule.subset_span ⟨g, φ, hPle hg, hSB, hcof, rfl⟩
    · rintro k hk _ ⟨g, hg, rfl⟩
      obtain ⟨g₁, hg₁, hA⟩ := hPst k hk g hg
      have key : om (k, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ :=
        hA _ (GlobalTheory.ThK.EvUniqInf.rest_pure _ _ hSB hstd)
      exact ⟨g₁, hg₁, key.symm⟩
  | zero =>
    exact ⟨⊥, inferInstance, bot_le, Submodule.zero_mem _, fun k _ x hx => by
      rw [Submodule.mem_bot] at hx; subst hx; rw [map_zero]; exact Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨U₁, h1, l1, m1, s1⟩ := hx
    obtain ⟨U₂, h2, l2, m2, s2⟩ := hy
    refine ⟨U₁ ⊔ U₂, inferInstance, sup_le l1 l2, Submodule.add_mem_sup m1 m2, fun k hk z hz => ?_⟩
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hz
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (s1 k hk y₁ hy₁) (s2 k hk y₂ hy₂)
  | smul c x _ hx =>
    obtain ⟨U, h, l, m, s⟩ := hx
    exact ⟨U, h, l, U.smul_mem c m, s⟩
end GlobalTheory.SquareAgree.KFinAlg
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.kFinite_algebra_closed_under_derivation : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' → ∀ ΦD ∈ GlobalTheory.SquareAgree.algD Γ.M Bs.ψ Bs.emb,
    ∃ U : Submodule ℂ ((Fin a × Fin (a + a') → AF F) → ℂ), FiniteDimensional ℂ U ∧
      U ≤ GlobalTheory.SquareAgree.algD Γ.M Bs.ψ Bs.emb ∧ ΦD ∈ U ∧
      ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ Γ.V Bs.emb, ∀ x ∈ U, om (k, 1) x ∈ U := by
  first | exact @_root_.GlobalTheory.SquareAgree.KFinAlg.derivation_algebra_kFinite | exact _root_.GlobalTheory.SquareAgree.KFinAlg.derivation_algebra_kFinite | (intros; apply _root_.GlobalTheory.SquareAgree.KFinAlg.derivation_algebra_kFinite <;> assumption)
end
end
end
