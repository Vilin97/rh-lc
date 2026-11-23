module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlacesStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WordDerivatives
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffOfContinuousOneParameter
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArchimedeanMatrixUnitaryContinuousMultiplicative
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParamUnitaryMatrixEqExpLieAlgebra

section

@[expose] public section

open Matrix

namespace GlobalTheory.OneParamUnitary

open scoped ContDiff

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem oneParam_eq_exp_lieU {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (u : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (hc : Continuous u) (h0 : u 0 = 1) (hadd : ∀ s t, u (s + t) = u s * u t)
    (hU : ∀ t, u t ∈ Formalism.QuantumDeterminants.UH G) :
    ∃ Y ∈ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU G, ∀ t : ℝ, u t = NormedSpace.exp (t • Y) := by
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have hsm : ContDiff ℝ ∞ u :=
    GlobalTheory.contDiff_of_continuous_oneParameter (Matrix (Fin n) (Fin n) ℂ) u hc h0 hadd
  have hdiff : Differentiable ℝ u := hsm.differentiable (by simp)
  set Y := deriv u 0 with hY
  have hY0 : HasDerivAt u Y 0 := (hdiff 0).hasDerivAt
  have hder : ∀ t, HasDerivAt u (u t * Y) t := by
    intro t
    have h1 : HasDerivAt (fun s => u (s - t)) Y t :=
      (show HasDerivAt u Y (t - t) by simpa using hY0).comp_sub_const t t
    have h2 := h1.const_mul (u t)
    have h3 : (fun s => u t * u (s - t)) = u := by
      funext s
      rw [← hadd]; congr 1; ring
    rwa [h3] at h2

  have hexp : ∀ t : ℝ, u t = NormedSpace.exp (t • Y) := by
    set v : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t => u t * NormedSpace.exp (t • (-Y)) with hv
    have hvd : ∀ t, HasDerivAt v 0 t := by
      intro t
      have hE := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-Y) t
      have := (hder t).mul hE
      rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, add_neg_cancel] at this
      exact this
    have hvc : ∀ t, v t = v 0 := fun t =>
      is_const_of_deriv_eq_zero (fun s => (hvd s).differentiableAt) (fun s => (hvd s).deriv) t 0
    have hv0 : v 0 = 1 := by simp [hv, h0]
    intro t
    have hcomm : Commute (t • (-Y)) (t • Y) :=
      ((Commute.refl Y).neg_left.smul_left t).smul_right t
    have hinv : NormedSpace.exp (t • (-Y)) * NormedSpace.exp (t • Y) = 1 := by
      rw [← Matrix.exp_add_of_commute _ _ hcomm, smul_neg, neg_add_cancel, NormedSpace.exp_zero]
    calc u t = u t * (NormedSpace.exp (t • (-Y)) * NormedSpace.exp (t • Y)) := by rw [hinv, Matrix.mul_one]
      _ = v t * NormedSpace.exp (t • Y) := by rw [hv, Matrix.mul_assoc]
      _ = NormedSpace.exp (t • Y) := by rw [hvc t, hv0, Matrix.one_mul]
  refine ⟨Y, ?_, hexp⟩

  show Yᴴ * G + G * Y = 0
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun A => star A
      map_add' := fun A B => star_add A B
      map_smul' := fun c A => by simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul] }
  have hst : HasDerivAt (fun t => star (u t)) (star Y) 0 :=
    (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt 0 hY0
  have hw := (hst.mul_const G).mul hY0
  have hconst : ((fun t => star (u t) * G) * u) = fun _ => G := by
    funext t; exact hU t
  rw [hconst] at hw
  have := (hasDerivAt_const (0 : ℝ) G).unique hw
  rw [h0, star_one, Matrix.one_mul, Matrix.mul_one, ← Matrix.star_eq_conjTranspose] at *
  exact this.symm

end GlobalTheory.OneParamUnitary
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParamUnitaryMatrixEqExpLieAlgebraStatement

section

@[expose] public section

open Matrix


theorem _root_.GlobalTheory.T.oneParamUnitaryMatrix_eq_exp_lieAlgebra : ∀ {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (u : ℝ → Matrix (Fin n) (Fin n) ℂ), Continuous u → u 0 = 1 → (∀ s t, u (s + t) = u s * u t) → (∀ t, u t ∈ Formalism.QuantumDeterminants.UH G) → ∃ Y ∈ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU G, ∀ t : ℝ, u t = NormedSpace.exp (t • Y) := by
  first | exact @GlobalTheory.OneParamUnitary.oneParam_eq_exp_lieU | exact GlobalTheory.OneParamUnitary.oneParam_eq_exp_lieU | (intros; apply GlobalTheory.OneParamUnitary.oneParam_eq_exp_lieU <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchLineTransposeGramUnitaryEqExp

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.LineDecomp

theorem toUX_surj (D : D7) (X : HSp D) {J : Matrix (Fin X.rank) (Fin X.rank) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl (Fin X.rank)) (Equiv.refl (Fin X.rank)))
    (u : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig J) : ∃ g : GA D X, GlobalTheory.TripleRead.toUX X (Equiv.refl _) hJ g = u := by
  have h : (u.1.1)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F J * (u.1.1).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F J := u.2
  generalize hm : u.1.1 = m at h
  have e0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F J = Formalism.L2.Theta.incA D D.host.xi0 • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ := by
    rw [hJ]
    simp only [Equiv.coe_refl, Matrix.submatrix_id_id]
    exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _
  rw [e0, Matrix.mul_smul, Matrix.smul_mul] at h
  have hu : IsUnit (Formalism.L2.Theta.incA D D.host.xi0) := (isUnit_iff_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)).map _
  have h2 := hu.smul_left_cancel.1 h
  have h3 := congrArg Matrix.transpose h2
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc] at h3
  have e : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ)ᵀ = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram := rfl
  rw [e, ← hm] at h3
  refine ⟨⟨u.1, h3⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  exact GlobalTheory.TripleRead.toUX_val X (Equiv.refl _) hJ _



theorem mem_GinfC_of_at (D : D7) (X : HSp D) (g : GA D X)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Formalism.L2.Theta.mt X g - 1)) : g ∈ GinfC X := by
  let a : AF D.host.F := ((0 : Ainf D.host.F), (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F))
  have ha : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F a = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F)
  have h1 := h a ha
  let φ := Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
  have key : ∀ x : AF D.host.F ⊗[D.host.F] D.host.E, φ (a • x) = φ x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [smul_zero]
    | tmul b c =>
      rw [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, smul_eq_mul, map_mul]
      congr 1
      exact one_mul _
    | add x y hx hy =>
      have e1 : a • (x + y) = a • x + a • y := smul_add a x y
      rw [e1, map_add φ (a • x) (a • y), map_add φ x y, hx, hy]
  show finHom X g = 1
  apply Units.ext
  show (Formalism.L2.Theta.mt X g).map φ = 1
  ext i j
  have h2 := congrArg φ (congrFun (congrFun h1 i) j)
  rw [Matrix.smul_apply, key, Matrix.zero_apply, map_zero, Matrix.sub_apply, map_sub, sub_eq_zero] at h2
  rw [Matrix.map_apply, h2, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem line_eq_expInf : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (X : HSp D) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (hJ : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl (Fin X.rank)) (Equiv.refl (Fin X.rank))),
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Ws, ∃ L : GlobalTheory.SmoothForms.LieN X, ∀ t : ℝ,
      γ (Multiplicative.ofAdd t) = GlobalTheory.TripleRead.toUX X (Equiv.refl (Fin X.rank)) hJ (GlobalTheory.SmoothForms.expInf θ X (t • L)) := by
  intro D θ hθ X Ws hJ γ hγ
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ X
  choose g hg using fun t : ℝ => toUX_surj D X hJ (γ (Multiplicative.ofAdd t))
  have hmat : ∀ t, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t)) = Formalism.L2.Theta.mt X (g t) := fun t => by
    rw [← hg t]
    show (GlobalTheory.TripleRead.toUX X _ hJ (g t)).1.1 = _
    rw [GlobalTheory.TripleRead.toUX_val]
    rfl
  have inj : ∀ a b : GA D X, Formalism.L2.Theta.mt X a = Formalism.L2.Theta.mt X b → a = b := fun a b h =>
    Subtype.ext (Units.ext h)
  have mtmul : ∀ a b : GA D X, Formalism.L2.Theta.mt X (a * b) = Formalism.L2.Theta.mt X a * Formalism.L2.Theta.mt X b := fun a b => by
    simp [Formalism.L2.Theta.mt, map_mul]
  have hmul : ∀ s t, g (s + t) = g s * g t := fun s t => inj _ _ (by
    rw [mtmul, ← hmat, ← hmat, ← hmat, ofAdd_add, map_mul]
    rfl)
  have g0 : g 0 = 1 := inj _ _ (by
    rw [← hmat, ofAdd_zero, map_one]
    rfl)
  have hinf : ∀ t, g t ∈ GinfC X := fun t => mem_GinfC_of_at D X (g t) (by rw [← hmat]; exact hγ.2 _)
  have hcont : Continuous fun t : ℝ => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t)) :=
    Units.continuous_val.comp (continuous_subtype_val.comp (hγ.1.comp continuous_ofAdd))
  have hu : ∀ τ, Continuous fun t : ℝ => infMat D.sp.cm.sig X.gram (θ τ) (g t) := fun τ => by
    refine ((hcont.matrix_map (GlobalTheory.Member.Arch.continuous_inf _ _)).matrix_map
      (GlobalTheory.Mem.VolExists.infEmb_continuous (hθ τ))).congr fun t => ?_
    rw [hmat]
    rfl
  choose Y hY hYe using fun τ => GlobalTheory.T.oneParamUnitaryMatrix_eq_exp_lieAlgebra (gramAt D X τ) (fun t => infMat D.sp.cm.sig X.gram (θ τ) (g t)) (hu τ)
    (by rw [g0]; simp [infMat, HA.mat]; exact Matrix.map_one _ (by simp) (by simp))
    (fun s t => by rw [hmul]; exact R.2.2.2.1 _ _ _)
    (fun t => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ X (g t) τ)
  let L : GlobalTheory.SmoothForms.LieN X := fun τ => ⟨Y τ, hY τ⟩
  refine ⟨L, fun t => ?_⟩
  have hE := GlobalTheory.SmoothForms.isExpFam_expInf R (t • L)
  have e : GlobalTheory.SmoothForms.expInf θ X (t • L) = g t := R.2.2.1 _ hE.1 _ (hinf t) fun τ => by
    rw [hE.2 τ, hYe τ t]
    rfl
  rw [e]
  exact (hg t).symm

end GlobalTheory.LineDecomp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchLineTransposeGramUnitaryEqExpStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun


theorem _root_.GlobalTheory.T.archLine_transposeGramUnitary_eq_exp : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (X : HSp D) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (hJ : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl (Fin X.rank)) (Equiv.refl (Fin X.rank))),
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Ws, ∃ L : GlobalTheory.SmoothForms.LieN X, ∀ t : ℝ,
      γ (Multiplicative.ofAdd t) = GlobalTheory.TripleRead.toUX X (Equiv.refl (Fin X.rank)) hJ (GlobalTheory.SmoothForms.expInf θ X (t • L)) := by
  first | exact @GlobalTheory.LineDecomp.line_eq_expInf | exact GlobalTheory.LineDecomp.line_eq_expInf | (intros; apply GlobalTheory.LineDecomp.line_eq_expInf <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SkewSpaceLineOneParamFockDerivative

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.LieLines

theorem line_deriv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X)
    (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ), IsInfFam θ →
    IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
    ∀ (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
      (hJ : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl (Fin X.rank)) (Equiv.refl (Fin X.rank))),
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Ws,
      ∃ (h : ℝ → GA D X) (Y : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ τ, Y τ ∈ lieAt X τ) ∧
        (∀ t : ℝ, γ (Multiplicative.ofAdd t) = GlobalTheory.TripleRead.toUX X (Equiv.refl (Fin X.rank)) hJ (h t)) ∧
        ∀ f₀ : WO (sgn ε M) X → ℂ, IsVacF ψ θ (frSgn ε A) B f₀ → ∀ (P : PolF D X.rank M.rank) (z : WO (sgn ε M) X),
          HasDerivAt (fun t : ℝ => ω (1, h t) (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ P) z)
            (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ (∑ τ, GlobalTheory.RealQuot.actT ε A B eS τ (Y τ) P) z) 0 := by
  classical
  intro D ψ θ ε M X A B χS χT ω eS eT hθ hω hexp Ws hJ γ hγ
  obtain ⟨L, hL⟩ : ∃ L : GlobalTheory.SmoothForms.LieN X, ∀ t : ℝ, γ (Multiplicative.ofAdd t) =
      GlobalTheory.TripleRead.toUX X (Equiv.refl (Fin X.rank)) hJ (GlobalTheory.SmoothForms.expInf θ X (t • L)) :=
    GlobalTheory.T.archLine_transposeGramUnitary_eq_exp D θ hθ X Ws hJ γ hγ
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ X
  refine ⟨fun t => GlobalTheory.SmoothForms.expInf θ X (t • L), fun τ => (L τ).1, fun τ => (L τ).2, hL, ?_⟩
  intro f₀ hf P z
  have hω' : IsWeilDatumO ψ (sgn ε M) X χS χT (WRep.toSgn ε ω) := hω
  have hψ := hω'.std
  have h1g : ∀ (g : GA D X), WRep.toSgn ε ω (1, g) = ω (1, g) := fun g => by
    simp [WRep.toSgn]
  have hlin : ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ (∑ τ, GlobalTheory.RealQuot.actT ε A B eS τ (L τ).1 P) =
      ∑ τ, ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ (GlobalTheory.RealQuot.actT ε A B eS τ (L τ).1 P) := map_sum _ _ _
  rcases isEmpty_or_nonempty D.what₂.Tau with hT | ⟨⟨τ₀⟩⟩
  · have e : ∀ t : ℝ, t • L = L := fun t => funext fun τ => (IsEmpty.false τ).elim
    simp only [e, hlin, Finset.univ_eq_empty, Finset.sum_empty, Pi.zero_apply]
    exact hasDerivAt_const _ _
  have hth : ∀ Q, IsThetaFunO ψ (sgn ε M) X (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ Q) :=
    (GlobalTheory.LieScalar.ptF_laws hθ hψ (frSgn ε A) B hf).1 τ₀
  let 𝒮 : Set (GA D X → ℂ) :=
    {φ | ∃ f z, IsThetaFunO ψ (sgn ε M) X f ∧ φ = fun g => WRep.toSgn ε ω (1, g) f z}
  have hc : ∀ φ ∈ 𝒮, Continuous φ := by
    rintro _ ⟨f, z, hf, rfl⟩
    exact (hω'.om_cont f hf z).comp (continuous_const.prodMk continuous_id)
  have hd : ∀ φ ∈ 𝒮, ∀ τ', ∀ Z ∈ lieAt X τ', ∃ φ' ∈ 𝒮, ∀ g,
      HasDerivAt (fun t : ℝ => φ (g * oneP θ X τ' Z t)) (φ' g) 0 := by
    rintro _ ⟨f, z, hf, rfl⟩ τ' Z hZ
    obtain ⟨G, hG', h⟩ := GlobalTheory.LieScalar.genT hθ hω' τ' Z hZ f hf
    refine ⟨_, ⟨G, z, hG', rfl⟩, fun g => ?_⟩
    have := h (MonoidHom.inr (GA D (sgn ε M)) (GA D X) g) z
    simpa only [MonoidHom.inr_apply, Prod.mk_mul_mk, mul_one] using this
  let φ : GA D X → ℂ := fun g => WRep.toSgn ε ω (1, g) (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ P) z
  have hφ : φ ∈ 𝒮 := ⟨_, z, hth P, rfl⟩
  have h1 := GlobalTheory.Mem.DerClosed.mem_smFun_of_closed D θ hθ X 𝒮 hc hd φ hφ
  have h2 : GlobalTheory.SmoothForms.Sm (GlobalTheory.SmoothForms.expInf θ X) φ :=
    (GlobalTheory.SmoothForms.isSmoothInf_iff φ).1 ((GlobalTheory.SmoothForms.smooth_iff R φ).1 h1)
  have h3 := ((h2 1).differentiable (by simp) 0).hasFDerivAt
  have hline : ∀ V : GlobalTheory.SmoothForms.LieN X, HasDerivAt (fun t : ℝ => φ (GlobalTheory.SmoothForms.expInf θ X (t • V)))
      (fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0 V) 0 := by
    intro V
    have h4 : HasDerivAt (fun t : ℝ => t • V) V 0 := by
      have h := (hasDerivAt_id (0 : ℝ)).smul_const V
      rwa [one_smul] at h
    have h3' : HasFDerivAt (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y))
        (fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0) ((0 : ℝ) • V) := by
      rw [zero_smul]
      exact h3
    have h5 := HasFDerivAt.comp_hasDerivAt (0 : ℝ) h3' h4
    simpa only [Function.comp_def, one_mul] using h5
  have hτ : ∀ τ, fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0
      (Pi.single τ (L τ) : GlobalTheory.SmoothForms.LieN X) =
      ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ (GlobalTheory.RealQuot.actT ε A B eS τ (L τ).1 P) z := by
    intro τ
    have hl := (GlobalTheory.LieScalar.lieFockAll D (sgn ε M) X (frSgn ε A) B θ ψ χS χT (WRep.toSgn ε ω) f₀ τ (eS τ) (eT τ)
      hθ hω' (hexp τ).1 (hexp τ).2 hf).2 (L τ).1 (L τ).2 P z
    have e := (hline (Pi.single τ (L τ) : GlobalTheory.SmoothForms.LieN X)).unique
      (hl.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
        show φ _ = _
        simp only [φ]
        rw [GlobalTheory.SmoothForms.oneP_eq R τ (L τ) t]
        rfl))
    rw [e]
    rfl
  have hsum : ∑ τ, (Pi.single τ (L τ) : GlobalTheory.SmoothForms.LieN X) = L := Finset.univ_sum_single L
  have e1 : (fun t : ℝ => ω (1, GlobalTheory.SmoothForms.expInf θ X (t • L)) (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ P) z) =
      fun t => φ (GlobalTheory.SmoothForms.expInf θ X (t • L)) := funext fun t => by simp only [φ, h1g]
  rw [e1, hlin, Finset.sum_apply]
  have e2 : fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0 L =
      ∑ τ, ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ (GlobalTheory.RealQuot.actT ε A B eS τ (L τ).1 P) z := by
    have h7 := map_sum (fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0)
      (fun τ => (Pi.single τ (L τ) : GlobalTheory.SmoothForms.LieN X)) Finset.univ
    have h8 : fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0 L =
        fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0
          (∑ τ, (Pi.single τ (L τ) : GlobalTheory.SmoothForms.LieN X)) := by
      congr 1
      exact hsum.symm
    have h9 : fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0 L =
        ∑ τ, fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0
          (Pi.single τ (L τ) : GlobalTheory.SmoothForms.LieN X) := by
      exact h8.trans h7
    rw [h9]
    exact Finset.sum_congr rfl fun τ _ => hτ τ
  have h6 := hline L
  rwa [e2] at h6

end GlobalTheory.LieLines

end
end
end
