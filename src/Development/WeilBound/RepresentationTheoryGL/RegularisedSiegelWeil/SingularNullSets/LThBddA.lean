module

public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalAdelicMatricesSelfAnnihilatorStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatAdelicMatrixContinuousLeMajorantStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondOnCommonRangeOfSecond
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryUnnSubgroupEqTopOfLeviUnipotentWeyl
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLeftMulUnitaryMatrixAddHaar
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Mathlib.Algebra.Order.Archimedean.Real.Hom
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
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalGroupLeOfGeneratorsMemStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSumInvariantUnipotentTranslate
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSumInvariantWeylInvolution
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.GramMatrixAdjoint
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstMemAndComm

section

@[expose] public section

noncomputable section

open scoped TensorProduct ENNReal Matrix Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilSchComm

def lmul {R : Type} [CommRing R] {m : ℕ} (n : ℕ) (A : Matrix (Fin m) (Fin m) R) (z : Fin m → Fin n → R) :
    Fin m → Fin n → R := fun i j => ∑ c, A i c * z c j

theorem lmul_lmul {R : Type} [CommRing R] {m n : ℕ} {A B : Matrix (Fin m) (Fin m) R} (h : A * B = 1)
    (z : Fin m → Fin n → R) : lmul n A (lmul n B z) = z := by
  change (A * (B * Matrix.of z) : Matrix (Fin m) (Fin n) R) = Matrix.of z
  rw [← Matrix.mul_assoc, h, Matrix.one_mul]

theorem continuous_lmul {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {m : ℕ} (n : ℕ)
    (A : Matrix (Fin m) (Fin m) R) : Continuous (lmul n A) := by
  unfold lmul
  fun_prop

def lmulHomeo {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {m : ℕ} (n : ℕ)
    {A B : Matrix (Fin m) (Fin m) R} (h : A * B = 1) : (Fin m → Fin n → R) ≃ₜ (Fin m → Fin n → R) where
  toFun := lmul n A
  invFun := lmul n B
  left_inv := lmul_lmul (mul_eq_one_comm.1 h)
  right_inv := lmul_lmul h
  continuous_toFun := continuous_lmul n A
  continuous_invFun := continuous_lmul n B

def lmulFam {T : Type} {m : ℕ} (n : ℕ) {A B : T → Matrix (Fin m) (Fin m) ℂ} (h : ∀ τ, A τ * B τ = 1) :
    (T → Fin m → Fin n → ℂ) ≃ₗ[ℝ] (T → Fin m → Fin n → ℂ) where
  toFun z τ := lmul n (A τ) (z τ)
  invFun z τ := lmul n (B τ) (z τ)
  map_add' z z' := by
    funext τ i j
    simp [lmul, mul_add, Finset.sum_add_distrib]
  map_smul' c z := by
    funext τ i j
    simp [lmul, Finset.mul_sum, mul_left_comm]
  left_inv z := funext fun τ => lmul_lmul (mul_eq_one_comm.1 (h τ)) (z τ)
  right_inv z := funext fun τ => lmul_lmul (h τ) (z τ)

theorem map_mul_entry {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {m n : ℕ} (M : Matrix (Fin m) (Fin m) R)
    (x : Matrix (Fin m) (Fin n) R) : (fun i j => φ ((M * x) i j)) = lmul n (M.map φ) fun i j => φ (x i j) := by
  funext i j

  simp only [lmul, Matrix.mul_apply, map_sum, map_mul, Matrix.map_apply]

variable {D : D7} {n : ℕ}

theorem map_cancel {R : Type} [CommRing R] (φ : AE D →+* R) (V : HSp D) (g : GA D V) :
    (mt V g).map φ * (mt V g⁻¹).map φ = 1 := by
  have h : mt V g * mt V g⁻¹ = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [map_inv]
    exact Units.mul_inv _
  rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero φ) (map_one φ)]

theorem comp_mem (θ : InfFam D) (V : HSp D) (h : GA D V) {Φ : Mx D V.rank n → ℂ} (hΦ : Φ ∈ schwartzA θ V.rank n) :
    (fun x : Mx D V.rank n => Φ (mt V h ⬝ x)) ∈ schwartzA θ V.rank n := by
  induction hΦ using Submodule.span_induction with
  | zero => exact Submodule.zero_mem _
  | add Φ Ψ _ _ h1 h2 => exact Submodule.add_mem _ h1 h2
  | smul c Φ _ h1 => exact Submodule.smul_mem _ c h1
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
    haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
    refine Submodule.subset_span ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
      (lmulFam n fun τ => map_cancel ((θ τ).comp (infPart D)) V h).toContinuousLinearEquiv f,
      g ∘ lmulHomeo n (map_cancel (finPart D) V h), ⟨hg.1.comp_continuous (lmulHomeo n _).continuous, hg.2.comp_homeomorph _⟩, funext fun x => ?_⟩
    have e1 := fun τ => map_mul_entry ((θ τ).comp (infPart D)) (mt V h) x
    have e2 := map_mul_entry (finPart D) (mt V h) x
    exact congrArg₂ (· * ·) (congrArg f (funext e1)) (congrArg g e2)

theorem inner_mul (V : HSp D) (h : GA D V) (x y : Mx D V.rank n) :
    StdUnn.inner V (mt V h ⬝ x) (mt V h ⬝ y) = StdUnn.inner V x y := by
  unfold StdUnn.inner
  rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA V), ← Matrix.mul_assoc (adj (mt V h)), mt_unitary]

def subst (θ : InfFam D) (V : HSp D) (n : ℕ) (h : GA D V) : Module.End ℂ (schwartzA θ V.rank n) where
  toFun Φ := ⟨fun x => Φ.1 (mt V h ⬝ x), comp_mem θ V h Φ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem subst_mem_and_comm : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D), IsInfFam θ → ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 → ∀ ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n), StdUnn.IsWeilSch ψ χ θ V μ ω → ∀ h : GA D V, (∀ Φ ∈ schwartzA θ V.rank n, (fun x : Mx D V.rank n => Φ (mt V h ⬝ x)) ∈ schwartzA θ V.rank n) ∧ ∀ (g : StdUnn.G D n) (Φ Ψ : schwartzA θ V.rank n), (∀ x, Ψ.1 x = Φ.1 (mt V h ⬝ x)) → ∀ x, (ω g Ψ).1 x = (ω g Φ).1 (mt V h ⬝ x) := by
  intro D n V ψ χ θ _ μ 𝓕 hμ ω hω h
  refine ⟨fun Φ hΦ => comp_mem θ V h hΦ, fun g Φ Ψ hΨ x => ?_⟩
  let S : Subgroup (StdUnn.G D n) :=
    { carrier := {g | Commute (ω g) (subst θ V n h)}
      one_mem' := by
        change Commute (ω 1) _
        rw [map_one]
        exact Commute.one_left _
      mul_mem' := fun {a b} ha hb => by
        change Commute (ω (a * b)) _
        rw [map_mul]
        exact Commute.mul_left ha hb
      inv_mem' := fun {a} ha => Commute.units_inv_left (u := ω.toHomUnits a) ha }
  have hS : S = ⊤ := by
    refine StdUnn.eq_top_of_levi_unip_weyl D n S (fun g a hg => ?_) (fun g b hg => ?_) (fun g hg => ?_) <;>
      refine LinearMap.ext fun Φ => Subtype.ext (funext fun x => ?_) <;>
      change (ω g (subst θ V n h Φ)).1 x = (ω g Φ).1 (mt V h ⬝ x)
    · rw [hω.levi g a hg, hω.levi g a hg, Matrix.mul_assoc]
      rfl
    · rw [hω.unip g b hg, hω.unip g b hg, inner_mul]
      rfl
    · rw [hω.weyl g hg, hω.weyl g hg, ← GlobalTheory.Twist.LeftHaar.integral_left_unitary D V n h μ hμ.1
        (fun y => Φ.1 y * ψ (StdUnn.trA (Matrix.trace (StdUnn.inner V (mt V h ⬝ x) y))))]
      refine congrArg (integral μ) (funext fun y => ?_)
      exact congrArg (fun t => Φ.1 (mt V h ⬝ y) * ψ (StdUnn.trA (Matrix.trace t))) (inner_mul V h x y).symm
  have hg : g ∈ S := hS ▸ Subgroup.mem_top g
  obtain rfl : Ψ = subst θ V n h Φ := Subtype.ext (funext hΨ)
  exact congrFun (congrArg Subtype.val (LinearMap.congr_fun (show Commute (ω g) (subst θ V n h) from hg).eq Φ)) x

end GlobalTheory.WeilSchComm

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThBddA

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.L.LThBdd

variable {D : D7} {n : ℕ}

theorem theta_levi {V : HSp D} {ψ χ θ μ} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hχ : IsHeckeChar D χ) (hω : IsWeilSch ψ χ θ V μ ω)
    (g : G D n) (a : GL (Fin n) D.host.E) (hg : mat g = blk4 (a.1.map (incA D)) 0 0 (adj ((a⁻¹).1.map (incA D))))
    (Φ : schwartzA θ V.rank n) :
    ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  let a' : GL (Fin n) (AE D) := Matrix.GeneralLinearGroup.map (incA D) a
  have hdet : Matrix.GeneralLinearGroup.det a' =
      Units.map (incA D).toMonoidHom (Matrix.GeneralLinearGroup.det a) := by
    apply Units.ext
    simp [a', Matrix.GeneralLinearGroup.map]
    exact (RingHom.map_det _ _).symm
  have h1 : absA D (Matrix.GeneralLinearGroup.det a') = 1 := by
    rw [hdet]; exact absE_inclR _
  have h2 : χ (Matrix.GeneralLinearGroup.det a') = 1 := by
    rw [hdet]; exact hχ.2 _
  have hinv : (a'⁻¹).1 = (a⁻¹).1.map (incA D) := by
    show ((Matrix.GeneralLinearGroup.map (incA D) a)⁻¹).1 = _
    rw [← map_inv]; rfl
  have hg' : mat g = blk4 a'.1 0 0 (adj (a'⁻¹).1) := by
    rw [hinv]; exact hg
  have hm : ∀ ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
      (ω g Φ).1 (ξ.map (incA D)) = Φ.1 ((ξ * a.1).map (incA D)) := by
    intro ξ
    rw [hω.levi g a' hg' Φ, h1, h2]
    have e : (HMul.hMul (ξ.map (incA D)) a'.1 : Mx D V.rank n) = (ξ * a.1).map (incA D) := by
      rw [Matrix.map_mul]; rfl
    rw [e]
    simp [npow]
  let e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    { toFun := fun ξ => ξ * a.1
      invFun := fun ξ => ξ * (a⁻¹).1
      left_inv := fun ξ => by
        show ξ * a.1 * (a⁻¹).1 = ξ
        rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      right_inv := fun ξ => by
        show ξ * (a⁻¹).1 * a.1 = ξ
        rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one] }
  simp_rw [hm]
  exact e.tsum_eq (fun ξ => Φ.1 (ξ.map (incA D)))

theorem theta_unip {V : HSp D} {ψ χ θ μ} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hψ : IsCharAF D.host.F ψ) (hω : IsWeilSch ψ χ θ V μ ω)
    (g : G D n) (b : Matrix (Fin n) (Fin n) D.host.E) (hg : mat g = blk4 1 (b.map (incA D)) 0 1)
    (Φ : schwartzA θ V.rank n) :
    ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  refine tsum_congr fun ξ => ?_
  rw [hω.unip g (b.map (incA D)) hg Φ (ξ.map (incA D)), GlobalTheory.CompanionTheory.ThetaInv.psi_unip_rat hψ, one_mul]

open GlobalTheory.CompanionTheory.ThetaPoisson in
theorem theta_weyl {V : HSp D} {ψ χ θ μ} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hψ : IsCharAF D.host.F ψ) (hθ : IsInfFam θ) {𝓕 : Set (Mx D V.rank n)} (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕)
    (hω : IsWeilSch ψ χ θ V μ ω) (g : G D n) (hg : mat g = blk4 0 1 (-1) 0) (Φ : schwartzA θ V.rank n) :
    ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_Mx D V.rank n
  haveI : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  have hT := isHermND_gram V
  obtain ⟨h1, h2⟩ := GlobalTheory.T.rationalAdelicMatrices_self_annihilator D V.rank n V.gram hT ψ hψ
  have hs := pairing_symm (n := n) hT ψ
  have hval : ∀ x, (ω g Φ).1 x = ∫ y, Φ.1 y * GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing V.gram ψ y x ∂μ := fun x => by
    rw [hω.weyl g hg Φ x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [hs y x]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing, GlobalTheory.SiegelWeilLitCompare.gramQ_eq]
    rfl
  haveI := hμ.1
  have key := poisson_translates (ratMx D V.rank n) K hK hKc (GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing (n := n) V.gram ψ)
    (fun y => ?_) hs (fun x x' y => ?_) (fun x y => hψ.2.1 _) h1 h2 μ 𝓕 hμ.2.1 hμ.2.2 (f := Φ.1) ?_
    (translates_bound hθ Φ) ?_
  · simp only [← hval] at key
    rw [tsum_ratMx, tsum_ratMx (fun x => (ω g Φ).1 x)] at key
    exact key.symm
  · simp only [hs _ y]
    haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
    haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    have ht : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA (D := D)) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
    exact hψ.1.comp (ht.comp (continuous_const.matrix_mul continuous_id).matrix_trace)
  · simp only [hs _ y]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.gramQ GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.mmul
    rw [Matrix.mul_add, Matrix.trace_add, map_add (f := _), AddChar.map_add_eq_mul]
  · exact (GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ _ n Φ.1
      (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ _ n Φ.1 Φ.2)).1
  · simp only [← hval]
    exact (ratEquiv D V.rank n).summable_iff.1 (GlobalTheory.SiegelWeilLitCompare.summable_rat hθ (ω g Φ))

theorem thetaInv' {V : HSp D} {ψ χ θ μ} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hψ : IsCharAF D.host.F ψ) (hχ : IsHeckeChar D χ) (hθ : IsInfFam θ) {𝓕 : Set (Mx D V.rank n)}
    (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕) (hω : IsWeilSch ψ χ θ V μ ω) (Φ : schwartzA θ V.rank n) {γ : G D n}
    (hγ : γ ∈ GF D n) :
    ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω γ Φ).1 (ξ.map (incA D)) =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  let S : Subgroup (G D n) :=
    { carrier := {γ | ∀ Φ : schwartzA θ V.rank n,
        ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω γ Φ).1 (ξ.map (incA D)) =
          ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D))}
      one_mem' := fun Φ => by simp
      mul_mem' := fun {g h} hg hh Φ => by
        rw [map_mul, Module.End.mul_apply]
        exact (hg _).trans (hh Φ)
      inv_mem' := fun {g} hg Φ => by
        have := hg (ω g⁻¹ Φ)
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
        exact this.symm }
  have hle : GF D n ≤ S := GlobalTheory.T.rational_group_le_of_generators_mem D n S (fun g a hg Φ => theta_levi hχ hω g a hg Φ)
    (fun g b hg Φ => theta_unip hψ hω g b hg Φ)
    (fun g hg Φ => theta_weyl hψ hθ hμ hω g hg Φ)
  exact hle hγ Φ

theorem theta_rat {V : HSp D} {ψ χ θ μ} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hψ : IsCharAF D.host.F ψ) (hχ : IsHeckeChar D χ) (hθ : IsInfFam θ) {𝓕 : Set (Mx D V.rank n)}
    (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕) (hω : IsWeilSch ψ χ θ V μ ω) (Φ : schwartzA θ V.rank n) {γ : G D n}
    (hγ : γ ∈ GF D n) (g : G D n) (h : GA D V) : theta ω Φ (γ * g) h = theta ω Φ g h := by
  have hc := (GlobalTheory.WeilSchComm.subst_mem_and_comm D n V ψ χ θ hθ μ 𝓕 hμ ω hω h⁻¹).2 γ (ω g Φ)
    (GlobalTheory.WeilSchComm.subst θ V n h⁻¹ (ω g Φ)) (fun _ => rfl)
  have ht := thetaInv' hψ hχ hθ hμ hω (GlobalTheory.WeilSchComm.subst θ V n h⁻¹ (ω g Φ)) hγ
  simp only [hc] at ht
  unfold theta
  rw [map_mul, Module.End.mul_apply]
  exact ht

end PositivityTheory.Rg.Rsw.L.LThBdd

end
end
end
