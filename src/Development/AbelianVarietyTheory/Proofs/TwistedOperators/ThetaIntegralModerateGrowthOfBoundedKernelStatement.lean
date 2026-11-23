module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinprodFiniteHeightTransposeGramUnitaryLeStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsModGrowthExpLeNormInfPow
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
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfiniteHeightTransposeGramUnitaryLe

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

namespace GlobalTheory.HtInfKapX

open GlobalTheory.AdelicU (htInf htOf normInf opNorm compInf)

theorem opNorm_reindex_le {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m)
    (y : Matrix n n ℂ) : opNorm (reindex e e y) ≤ opNorm y := by
  unfold GlobalTheory.AdelicU.opNorm
  refine ContinuousLinearMap.opNNNorm_le_bound _ _ fun x => ?_
  let c : EuclideanSpace ℂ m → EuclideanSpace ℂ n := fun z => WithLp.toLp 2 fun i => z (e i)
  let c' : EuclideanSpace ℂ n → EuclideanSpace ℂ m := fun z => WithLp.toLp 2 fun j => z (e.symm j)
  have hc : ∀ z, ‖c z‖₊ = ‖z‖₊ := fun z => by
    simp only [EuclideanSpace.nnnorm_eq, c]
    congr 1
    exact Equiv.sum_comp e (fun j => ‖z j‖₊ ^ 2)
  have hc' : ∀ z, ‖c' z‖₊ = ‖z‖₊ := fun z => by
    simp only [EuclideanSpace.nnnorm_eq, c']
    congr 1
    exact Equiv.sum_comp e.symm (fun j => ‖z j‖₊ ^ 2)
  have h : Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) (reindex e e y) x =
      c' (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) y (c x)) := by
    ext j
    change ∑ k, y (e.symm j) (e.symm k) * x k = ∑ i, y (e.symm j) i * x (e i)
    rw [← Equiv.sum_comp e]
    simp
  rw [h, hc', ← hc x]
  exact ContinuousLinearMap.le_opNNNorm _ _

theorem opNorm_reindex {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m)
    (y : Matrix n n ℂ) : opNorm (reindex e e y) = opNorm y := by
  refine le_antisymm (opNorm_reindex_le e y) ?_
  have h : reindex e.symm e.symm (reindex e e y) = y := by ext; simp
  calc opNorm y = opNorm (reindex e.symm e.symm (reindex e e y)) := by rw [h]
    _ ≤ opNorm (reindex e e y) := opNorm_reindex_le e.symm _

variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  (w : NumberField.InfinitePlace F)

theorem normInf_reindex {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m)
    (y : Matrix n n (w.Completion ⊗[F] E)) : normInf F w (reindex e e y) = normInf F w y := by
  unfold GlobalTheory.AdelicU.normInf
  congr 1
  funext τ
  rw [reindex_apply, ← Matrix.submatrix_map, ← reindex_apply, opNorm_reindex]

theorem htInf_reindex {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m)
    (g : (Matrix n n (w.Completion ⊗[F] E))ˣ) :
    htInf F w (Units.map (Matrix.reindexAlgEquiv (w.Completion ⊗[F] E) (w.Completion ⊗[F] E) e).toMonoidHom g) =
      htInf F w g := by
  have key : ∀ y, normInf F w ((Matrix.reindexAlgEquiv (w.Completion ⊗[F] E) (w.Completion ⊗[F] E) e) y) =
      normInf F w y := fun y => by rw [Matrix.reindexAlgEquiv_apply, normInf_reindex]
  show GlobalTheory.AdelicU.htOf (normInf F w) _ = GlobalTheory.AdelicU.htOf (normInf F w) _
  rw [GlobalTheory.AdelicU.htOf, GlobalTheory.AdelicU.htOf, ← map_inv, Units.coe_map, Units.coe_map]
  exact congrArg₂ _ rfl (congrArg₂ _ (key _) (key _))

theorem bc_reindex {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {n m : Type} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (e : n ≃ m) (g : (Matrix n n A)ˣ) :
    Formalism.UG.bc φ (Units.map (Matrix.reindexAlgEquiv A A e).toMonoidHom g) =
      Units.map (Matrix.reindexAlgEquiv B B e).toMonoidHom (Formalism.UG.bc φ g) := by
  ext i j
  rfl

theorem htInf_kapX_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E} (hJ : J = D.host.xi0 • reindex e e X.gramᵀ), ∃ C : NNReal, ∀ h : GA D X, ∏ w, GlobalTheory.AdelicU.htInf D.host.F w (Formalism.UG.bc (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) (kapX X e hJ h).1) ≤ C * ∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infHt θ X τ h := by
  intro D θ hθ X d e J hJ
  refine ⟨1, fun h => ?_⟩
  rw [one_mul]
  refine le_of_eq ?_
  have key : ∀ w, GlobalTheory.AdelicU.htInf D.host.F w
      (Formalism.UG.bc (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) (kapX X e hJ h).1) =
      GlobalTheory.AdelicU.htInf D.host.F w (Formalism.UG.bc (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) (Formalism.L2.Theta.matHom X h)) :=
    fun w => by
      show GlobalTheory.AdelicU.htInf D.host.F w (Formalism.UG.bc _
        (Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e).toMonoidHom (Formalism.L2.Theta.matHom X h))) = _
      rw [bc_reindex, htInf_reindex]
  simp only [key]
  exact (Function.Bijective.prod_comp (GlobalTheory.CMTypePlaces.places_bijective D) _).symm.trans
    (Finset.prod_congr rfl fun τ _ => GlobalTheory.Grow.htInf_eq_infHt X hθ τ h)

end GlobalTheory.HtInfKapX
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfiniteHeightTransposeGramUnitaryLeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.infiniteHeight_transposeGramUnitary_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E} (hJ : J = D.host.xi0 • reindex e e X.gramᵀ), ∃ C : NNReal, ∀ h : GA D X, ∏ w, GlobalTheory.AdelicU.htInf D.host.F w (Formalism.UG.bc (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) (kapX X e hJ h).1) ≤ C * ∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infHt θ X τ h := by
  first | exact @GlobalTheory.HtInfKapX.htInf_kapX_le | exact GlobalTheory.HtInfKapX.htInf_kapX_le | (intros; apply GlobalTheory.HtInfKapX.htInf_kapX_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralModerateGrowthOfBoundedKernel

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

namespace GlobalTheory.ModGrowth

variable {D : D7}


open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation in
def conjInv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (h : J = (-1 : D.host.E) • V.gram) (u : UB J) :
    GA D V :=
  ⟨Matrix.GeneralLinearGroup.map (Formalism.L2.Theta.cA D) u.1, by
    have hu : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat u)ᵀ * incM J * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat u).map (Formalism.L2.Theta.cA D) = incM J := u.2
    have hJ : incM J = -incM V.gram := by
      subst h; ext i j; simp [incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
    rw [hJ, Matrix.mul_neg, Matrix.neg_mul, neg_inj] at hu
    show (((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat u).map (Formalism.L2.Theta.cA D)).map (Formalism.L2.Theta.cA D))ᵀ *
      incM V.gram * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat u).map (Formalism.L2.Theta.cA D) = incM V.gram
    have e : ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat u).map (Formalism.L2.Theta.cA D)).map (Formalism.L2.Theta.cA D) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat u :=
      Matrix.ext fun _ _ => Formalism.L2.Theta.cA_cA _
    rw [e]; exact hu⟩

theorem conjInv_conjU (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (h : J = (-1 : D.host.E) • V.gram)
    (g : GA D V) : conjInv V h (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V (-1) h g) = g :=
  Subtype.ext (Units.ext (Matrix.ext fun _ _ => Formalism.L2.Theta.cA_cA _))

theorem conjU_conjInv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (h : J = (-1 : D.host.E) • V.gram)
    (u : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V (-1) h (conjInv V h u) = u :=
  Subtype.ext (Units.ext (Matrix.ext fun _ _ => Formalism.L2.Theta.cA_cA _))

theorem continuous_conjInv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (h : J = (-1 : D.host.E) • V.gram) :
    Continuous (conjInv V h) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact (Units.continuous_val.comp continuous_subtype_val).matrix_map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D)
  · exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D)

def conjHomeo (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (h : J = (-1 : D.host.E) • V.gram) :
    GA D V ≃ₜ GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J where
  toFun := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V (-1) h
  invFun := conjInv V h
  left_inv := conjInv_conjU V h
  right_inv := conjU_conjInv V h
  continuous_toFun := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conjU V (-1) h
  continuous_invFun := continuous_conjInv V h

theorem measurableEmbedding_conjU (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E}
    (h : J = (-1 : D.host.E) • V.gram) : MeasurableEmbedding (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V (-1) h) := by
  haveI : BorelSpace (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) := ⟨rfl⟩
  exact (conjHomeo V h).measurableEmbedding

end GlobalTheory.ModGrowth

namespace GlobalTheory.ModGrowth

variable {D : D7}

theorem ht_kapX_le (θ : InfFam D) (hθ : IsInfFam θ) (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    {J : Matrix (Fin d) (Fin d) D.host.E} (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) :
    ∃ C : NNReal, ∀ h : GA D X, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (kapX X e hJ h) ≤ C * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h := by
  obtain ⟨C₁, h₁⟩ := GlobalTheory.T.infiniteHeight_transposeGramUnitary_le D θ hθ X e hJ
  obtain ⟨C₂, h₂⟩ := GlobalTheory.T.finprod_finiteHeight_transposeGramUnitary_le D X e hJ
  refine ⟨C₁ * C₂, fun h => ?_⟩
  show (∏ w, GlobalTheory.AdelicU.htInf D.host.F w (Formalism.UG.bc (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) (kapX X e hJ h).1)) *
      ∏ᶠ v, GlobalTheory.AdelicU.htFin D.host.F v (Formalism.UG.bc (GlobalTheory.AdelicU.compFin D.host.F D.host.E v) (kapX X e hJ h).1) ≤
    C₁ * C₂ * ((∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infHt θ X τ h) * ∏ᶠ v, GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt X v h)
  calc _ ≤ (C₁ * ∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infHt θ X τ h) * (C₂ * ∏ᶠ v, GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt X v h) :=
        mul_le_mul' (h₁ h) (h₂ h)
    _ = _ := by ring

end GlobalTheory.ModGrowth

namespace GlobalTheory.ModGrowth


open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in
theorem modInt_of_bound : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB → IsHaarFD W₁ ν₁ 𝓕₁ →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Φ₀ Φ₀D, IsDatum Γ.M' ψ cB Φ₀D Φ₀ → Γ.M'.Conv om' Φ₀D →
    (∃ (C : ℝ) (k : ℕ), ∀ g h, ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ₀D g h‖ ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht h : ℝ) ^ k) →
    ModInt θ ωB ν₁ 𝓕₁ Φ₀ := by
  intro D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hO hH _ Φ₀ Φ₀D hD hC hB
  obtain ⟨C, k, hCk⟩ := hB
  obtain ⟨C', hC'⟩ := ht_kapX_le θ hθ X e hO.JX
  have hcm := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm
  have hvol : ν₁ 𝓕₁ < ⊤ :=
    GlobalTheory.Mem.VolFin.finVol _ _ D.sp.cm.sig hcm.1 W₁.rank W₁.gram (hcm.2 W₁) ν₁ hH.1 𝓕₁ hH.2
  have hemb := measurableEmbedding_conjU W₁ hO.JW₁
  have key : ∀ g h, thetaKO ωB g h Φ₀ =
      theta om' Φ₀D (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ g) (kapX X e hO.JX h) := fun g h =>
    (hO.theta_eq_B hD g h).symm
  refine ⟨k, max C 0 * (C' : ℝ) ^ k * ν₁.real 𝓕₁, fun h => ⟨?_, ?_⟩⟩
  · have hi := hC (kapX X e hO.JX h)
    rw [hO.measW₁, hO.domW₁, hemb.integrableOn_map_iff, Set.preimage_image_eq _ hemb.injective] at hi
    have hf : (fun g => thetaKO ωB g h Φ₀) =
        (fun u => theta om' Φ₀D u (kapX X e hO.JX h)) ∘ GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ :=
      funext fun g => key g h
    rw [hf]; exact hi
  · have hht : (ht (kapX X e hO.JX h) : ℝ) ≤ (C' : ℝ) * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) := by
      exact_mod_cast hC' h
    have hb : ∀ g ∈ 𝓕₁, ‖‖thetaKO ωB g h Φ₀‖‖ ≤
        max C 0 * ((C' : ℝ) * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ)) ^ k := by
      intro g _
      rw [norm_norm, key]
      calc _ ≤ C * (ht (kapX X e hO.JX h) : ℝ) ^ k := hCk _ _
        _ ≤ max C 0 * (ht (kapX X e hO.JX h) : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (NNReal.coe_nonneg _) _)
        _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) hht k) (le_max_right _ _)
    have hI := norm_setIntegral_le_of_norm_le_const hvol hb
    calc _ ≤ ‖∫ g in 𝓕₁, ‖thetaKO ωB g h Φ₀‖ ∂ν₁‖ := Real.le_norm_self _
      _ ≤ _ := hI
      _ = _ := by rw [mul_pow]; ring

end GlobalTheory.ModGrowth
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralModerateGrowthOfBoundedKernelStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.theta_integral_moderate_growth_of_bounded_kernel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB → IsHaarFD W₁ ν₁ 𝓕₁ →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Φ₀ Φ₀D, IsDatum Γ.M' ψ cB Φ₀D Φ₀ → Γ.M'.Conv om' Φ₀D →
    (∃ (C : ℝ) (k : ℕ), ∀ g h, ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ₀D g h‖ ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht h : ℝ) ^ k) →
    ModInt θ ωB ν₁ 𝓕₁ Φ₀ := by
  first | exact @GlobalTheory.ModGrowth.modInt_of_bound | exact GlobalTheory.ModGrowth.modInt_of_bound | (intros; apply GlobalTheory.ModGrowth.modInt_of_bound <;> assumption)
end
end
