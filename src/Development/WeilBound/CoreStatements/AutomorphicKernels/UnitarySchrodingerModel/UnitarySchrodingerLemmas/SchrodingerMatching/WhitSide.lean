module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitKA
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.PsiPlaces
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.WhitNDgOfLocalOfSteps
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitKA
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.IntegrableWhitOfUnfold
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMulRight
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfDualSiegelWeilMeasures
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.ConjHConjHInv

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwMatch

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.SiegelND

variable {D : D7} {n : ℕ}

theorem conjH_conjH_inv' (a : GL (Fin n) (AE D)) (b : hermA D n) : conjH a (conjH a⁻¹ b) = b := by
  apply Subtype.ext
  change a.1 * ((a⁻¹).1 * b.1 * adj (a⁻¹).1) * adj a.1 = b.1
  have h1 : a.1 * (a⁻¹).1 = 1 := Units.mul_inv a
  have h2 : adj (a⁻¹).1 * adj a.1 = 1 := by
    rw [← adj_mul, h1]
    unfold adj
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  calc a.1 * ((a⁻¹).1 * b.1 * adj (a⁻¹).1) * adj a.1
      = (a.1 * (a⁻¹).1) * b.1 * (adj (a⁻¹).1 * adj a.1) := by simp only [mul_assoc]
    _ = b.1 := by rw [h1, h2, one_mul, mul_one]

theorem inv_cpow_neg' (x : ℝ≥0) {w : ℂ} (hw : w ≠ 0) : (((x : ℝ)⁻¹ : ℝ) : ℂ) ^ (-w) = npow x w := by
  unfold npow
  rcases eq_or_ne x 0 with rfl | hx
  · simp [Complex.zero_cpow hw, Complex.zero_cpow (neg_ne_zero.2 hw)]
  · have hpos : (0 : ℝ) ≤ (x : ℝ) := x.2
    have harg : ((x : ℝ) : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hpos]
      exact Real.pi_ne_zero.symm
    rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg, Complex.cpow_neg, inv_inv]


theorem nu_conj {θ : InfFam D} (hRc : RealConj) (hθ : IsInfFam θ) (a : GL (Fin n) (AE D))
    (lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E))
    (L L₁ L₂ : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      AddSubgroup (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E))
    (hnu2 : ∀ v (b : hermA D n),
      PositivityTheory.SiegelWeilFormula.Gen.nu2 (lam v) (L₁ v) (L₂ v) (PositivityTheory.SiegelWeilFormula.Gen.matV v (conjH a b).1) =
        PositivityTheory.SiegelWeilFormula.Gen.nu2 (lam v) (L v) (L v) (PositivityTheory.SiegelWeilFormula.Gen.matV v b.1)) (c : hermA D n) :
    PositivityTheory.SiegelWeilFormula.Gen.nuA θ (aTau θ a) lam L₁ L₂ (conjH a c).1 = PositivityTheory.SiegelWeilFormula.Gen.nuA θ (fun _ => 1) lam L L c.1 := by
  exact congrArg₂ (· * ·) (hRc D θ hθ n a c) (finprod_congr fun v => hnu2 v c)

end PositivityTheory.PfSWUS.SwMatch

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.TrPairEqHalfTr

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwMatch

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.SiegelND

variable {D : D7} {n : ℕ}

theorem trPair_eq_halfTr (S T : Mx D n n) :
    PositivityTheory.PfSWUS.Loc.trPair (AF D.host.F) S T = halfTr (Matrix.trace (HMul.hMul S T : Mx D n n)) := rfl

theorem gramR_tupInv (V : HSp D) (y : Mx D V.rank n) :
    HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF D.host.F) D.sp.cm.sig (HSpace.gram V) (tupInv y) = GlobalTheory.StdUnn.inner V y y := by
  ext a c
  exact hR_tup V y y a c

theorem inner_mul_right (V : HSp D) (y : Mx D V.rank n) (a : Mx D n n) :
    GlobalTheory.StdUnn.inner V (HMul.hMul y a : Mx D V.rank n) (HMul.hMul y a : Mx D V.rank n) =
      adj a * GlobalTheory.StdUnn.inner V y y * a := by
  unfold GlobalTheory.StdUnn.inner
  rw [adj_mul]
  simp only [Matrix.mul_assoc]




theorem jt_conj (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n))
    (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕) (a : GL (Fin n) (AE D)) (φ : Mx D V.rank n → ℂ) (c : hermA D n) :
    PositivityTheory.PfSWUS.Loc.jtR (AF D.host.F) D.sp.cm.sig (HSpace.gram V) ψ (μ.map tupInv)
        (fun X => φ (HMul.hMul (tupOf X) a.1)) (hermTo (conjH a c)) =
      npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(V.rank : ℂ)) * Jt ψ V μ φ c := by
  obtain ⟨k1, -, -, -, -, -⟩ := lattice_Mx D V.rank n
  have : IsTopologicalAddGroup (Mx D V.rank n) := k1
  have : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  have : BorelSpace (Fin n → Fin V.rank → AE D) := borel_tup
  unfold Jt
  rw [← GlobalTheory.RightMulJac.integral_mul_right D V.rank n μ 𝓕 hμ a]
  refine (integral_map_of tupInv tupOf tupOf_tupInv tupInv_tupOf tupInv_add continuous_tupInv continuous_tupOf μ
    (fun Y => φ (HMul.hMul (tupOf Y) a.1) * ψ (PositivityTheory.PfSWUS.Loc.trPair (AF D.host.F) (conjH a c).1
      (HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF D.host.F) D.sp.cm.sig (HSpace.gram V) Y)))).trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change φ (HMul.hMul y a.1) * ψ (PositivityTheory.PfSWUS.Loc.trPair (AF D.host.F) (conjH a c).1
      (HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF D.host.F) D.sp.cm.sig (HSpace.gram V) (tupInv y))) =
    φ (HMul.hMul y a.1) * ψ (halfTr (Matrix.trace (HMul.hMul c.1
      (GlobalTheory.StdUnn.inner V (HMul.hMul y a.1 : Mx D V.rank n) (HMul.hMul y a.1 : Mx D V.rank n)) : Mx D n n)))
  rw [gramR_tupInv, trPair_eq_halfTr, inner_mul_right]
  have e : Matrix.trace (a.1 * c.1 * adj a.1 * GlobalTheory.StdUnn.inner V y y) =
      Matrix.trace (c.1 * (adj a.1 * GlobalTheory.StdUnn.inner V y y * a.1)) := by
    rw [← Matrix.mul_assoc c.1, Matrix.trace_mul_comm _ a.1]
    simp only [Matrix.mul_assoc]
  exact congrArg (fun z => φ (HMul.hMul y a.1) * ψ (halfTr z)) e

theorem char_conj (ψ : AddChar (AF D.host.F) ℂ) (β : HermE D n) (a : GL (Fin n) (AE D)) (c : hermA D n) :
    ψ (-PositivityTheory.PfSWUS.Loc.trPair (AF D.host.F) (β.1.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF D.host.F))) (hermTo (conjH a c)).1) =
      ψ (-halfTr (Matrix.trace (HMul.hMul (adj a.1 * β.1.map (incA D) * a.1) c.1 : Mx D n n))) := by
  have e : Matrix.trace (β.1.map (incA D) * (a.1 * c.1 * adj a.1)) =
      Matrix.trace (adj a.1 * β.1.map (incA D) * a.1 * c.1) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm _ (adj a.1)]
    simp only [Matrix.mul_assoc]
  exact congrArg (fun z => ψ (-z))
    ((trPair_eq_halfTr (D := D) (β.1.map (incA D)) (a.1 * c.1 * adj a.1)).trans (congrArg halfTr e))

end PositivityTheory.PfSWUS.SwMatch

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.Transport

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwMatch

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.SiegelND

section Transport

variable {D : D7} {n : ℕ}

def hermToME : hermA D n ≃ᵐ HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF D.host.F) D.sp.cm.sig n where
  toFun := hermTo
  invFun := hermFrom
  left_inv := hermFrom_hermTo
  right_inv := hermTo_hermFrom
  measurable_toFun := by
    haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
    haveI : BorelSpace (hermA D n) := Subtype.borelSpace _
    haveI : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF D.host.F) D.sp.cm.sig n) := ⟨rfl⟩
    exact continuous_hermTo.measurable
  measurable_invFun := by
    haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
    haveI : BorelSpace (hermA D n) := Subtype.borelSpace _
    haveI : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF D.host.F) D.sp.cm.sig n) := ⟨rfl⟩
    exact continuous_hermFrom.measurable

theorem integral_map_hermTo (lam : Measure (hermA D n))
    (W : HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF D.host.F) D.sp.cm.sig n → ℂ) :
    ∫ b, W b ∂(lam.map hermTo) = ∫ b, W (hermTo b) ∂lam :=
  (hermToME (D := D) (n := n)).measurableEmbedding.integral_map W

theorem integrable_map_hermTo (lam : Measure (hermA D n))
    (W : HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF D.host.F) D.sp.cm.sig n → ℂ) (h : Integrable (fun b => W (hermTo b)) lam) :
    Integrable W (lam.map hermTo) :=
  ((hermToME (D := D) (n := n)).measurableEmbedding.integrable_map_iff).2 h

end Transport

end PositivityTheory.PfSWUS.SwMatch

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.WhitSide

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwMatch

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.SiegelND




theorem whit_side (hRc : RealConj) (hM : ConjMod) (hU : Unfold) (hK : HeightKInv)
    {D : D7} {n : ℕ} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
    {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
    {Φ : schwartzA θ V.rank n} (hstd : Std D n V ψ χ θ μ ω H l s ν Φ) (hrange : InRange V n)
    {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} {nb : hermA D n → G D n} (hcd : CoefData nb lam 𝓖)
    {w : G D n} (hw : mat w = blk4 0 1 (-1) 0) {β : HermE D n} (hβ : β.1.det ≠ 0) (a : GL (Fin n) (AE D))
    {k : G D n} (hk : k ∈ K D n) {φ : Mx D V.rank n → ℂ} (hsch : φ ∈ schwartzA θ V.rank n) (hfock : φ ∈ fockA θ V n l s)
    (lamS : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E))
    (hlamS : ∀ v, (lamS v).IsAddHaarMeasure)
    (L L₁ L₂ : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      AddSubgroup (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E))
    (hLnu : ∀ lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
        Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E),
      (∀ v, (lam v).IsAddHaarMeasure) →
      ∀ b : hermA D n, ((H (w * nb b) : ℝ))⁻¹ = PositivityTheory.SiegelWeilFormula.Gen.nuA θ (fun _ => 1) lam L L b.1)
    (hnu2 : ∀ v (b : hermA D n),
      PositivityTheory.SiegelWeilFormula.Gen.nu2 (lamS v) (L₁ v) (L₂ v) (PositivityTheory.SiegelWeilFormula.Gen.matV v (conjH a b).1) =
        PositivityTheory.SiegelWeilFormula.Gen.nu2 (lamS v) (L v) (L v) (PositivityTheory.SiegelWeilFormula.Gen.matV v b.1))
    (𝓕μ : Set (Mx D V.rank n)) (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕μ) :
    ∃ t : ℝ, ∀ z : ℂ, t < z.re →
      Integrable (PositivityTheory.SiegelWeilFormula.Gen.whI (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F) D.sp.cm.sig (HSpace.gram V) ψ (μ.map tupInv)
        (fun X => φ (HMul.hMul (tupOf X) a.1))
        (PositivityTheory.SiegelWeilFormula.Gen.nuA θ (aTau θ a) lamS L₁ L₂) (β.1.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F))) z)
        (lam.map hermTo) ∧
      whitT ψ V μ lam nb w H φ (adj a.1 * β.1.map (incA D) * a.1) k z =
        npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) - n) *
          ∫ b, PositivityTheory.SiegelWeilFormula.Gen.whI (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F) D.sp.cm.sig (HSpace.gram V) ψ (μ.map tupInv)
            (fun X => φ (HMul.hMul (tupOf X) a.1))
            (PositivityTheory.SiegelWeilFormula.Gen.nuA θ (aTau θ a) lamS L₁ L₂)
            (β.1.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F))) z b ∂(lam.map hermTo) := by
  classical
  refine ⟨(n : ℝ) / 2, fun z hz => ?_⟩
  set r : ℝ≥0 := absA D (Matrix.GeneralLinearGroup.det a) with hr
  have hr0 : r ≠ 0 := ((Group.isUnit (Matrix.GeneralLinearGroup.det a)).map (absA D)).ne_zero
  set T : Mx D n n := adj a.1 * β.1.map (incA D) * a.1 with hT

  set I : hermA D n → ℂ := fun c => npow (H (w * nb c * k)) (z - s0 V n) * Jt ψ V μ φ c *
    ψ (-halfTr (Matrix.trace (HMul.hMul T c.1 : Mx D n n))) with hI
  set W := PositivityTheory.SiegelWeilFormula.Gen.whI (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F) D.sp.cm.sig (HSpace.gram V) ψ (μ.map tupInv)
        (fun X => φ (HMul.hMul (tupOf X) a.1))
        (PositivityTheory.SiegelWeilFormula.Gen.nuA θ (aTau θ a) lamS L₁ L₂) (β.1.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F))) z
    with hW
  have hzs : z - s0 V n ≠ 0 := by
    intro h0
    have hre := congrArg Complex.re h0
    simp only [s0, Complex.sub_re, Complex.div_re, Complex.natCast_re, Complex.natCast_im, Complex.zero_re] at hre
    have h2 : (V.rank : ℝ) ≤ 2 * n := by exact_mod_cast hrange.2.1
    norm_num at hre
    linarith
  have hpt : ∀ c : hermA D n, W (hermTo (conjH a c)) = npow r (-(V.rank : ℂ)) * I c := by
    intro c
    have h1 := nu_conj hRc hstd.hθ a lamS L L₁ L₂ hnu2 c
    rw [← hLnu lamS hlamS c] at h1
    have h2 := jt_conj V ψ μ 𝓕μ hμ a φ c
    have h3 := char_conj ψ β a c
    have h4 : H (w * nb c * k) = H (w * nb c) := hK D n H hstd.hH (w * nb c) k hk
    have h5 : ((V.rank : ℂ) - n) / 2 = s0 V n := by unfold s0; ring
    simp only [hW, hI, PositivityTheory.SiegelWeilFormula.Gen.whI]
    change (((PositivityTheory.SiegelWeilFormula.Gen.nuA θ (aTau θ a) lamS L₁ L₂ (conjH a c).1 : ℝ)) : ℂ) ^ (-(z - ((V.rank : ℂ) - n) / 2)) *
        PositivityTheory.PfSWUS.Loc.jtR (AF D.host.F) D.sp.cm.sig (HSpace.gram V) ψ (μ.map tupInv)
          (fun X => φ (HMul.hMul (tupOf X) a.1)) (hermTo (conjH a c)) *
        ψ (-PositivityTheory.PfSWUS.Loc.trPair (AF D.host.F) (β.1.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF D.host.F))) (hermTo (conjH a c)).1) = _
    rw [h1, h2, h3, h4, h5, inv_cpow_neg' _ hzs]
    ring
  have hHaar : lam.IsAddHaarMeasure := hcd.2.1
  have hIint : Integrable I lam := by
    have h := integrable_whit_of_unfold hU D n V ψ χ θ μ ω H l s ν Φ hstd hrange lam 𝓖 nb hcd w hw β hβ φ hsch hfock
      T z hz
    refine h.congr (Filter.Eventually.of_forall fun c => ?_)
    simp only [hI, hK D n H hstd.hH (w * nb c) k hk]
  have hWcomp : (fun b => W (hermTo b)) = fun b => npow r (-(V.rank : ℂ)) * I (conjH a⁻¹ b) := by
    funext b
    conv_lhs => rw [← conjH_conjH_inv' a b]
    exact hpt _
  have hrC : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr0
  have key : npow r ((V.rank : ℂ) - n) * (((r : ℝ) : ℂ) ^ n * npow r (-(V.rank : ℂ))) = 1 := by
    unfold npow
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hrC, ← Complex.cpow_add _ _ hrC]
    have : ((V.rank : ℂ) - n) + ((n : ℂ) + -(V.rank : ℂ)) = 0 := by ring
    rw [this, Complex.cpow_zero]
  have hwI : whitT ψ V μ lam nb w H φ T k z = ∫ c, I c ∂lam := rfl
  refine ⟨?_, ?_⟩
  · refine integrable_map_hermTo lam W ?_
    rw [hWcomp]
    exact (integrable_comp_conjH lam hHaar a⁻¹ hIint).const_mul _
  · rw [integral_map_hermTo lam W]
    have hc := hM D n lam hHaar a (fun B => if h : B ∈ hermA D n then W (hermTo ⟨B, h⟩) else 0)
    have e1 : ∫ b, (fun B => if h : B ∈ hermA D n then W (hermTo ⟨B, h⟩) else 0) b.1 ∂lam = ∫ b, W (hermTo b) ∂lam :=
      integral_congr_ae (Filter.Eventually.of_forall fun b => by
        show (if h : b.1 ∈ hermA D n then W (hermTo ⟨b.1, h⟩) else 0) = W (hermTo b)
        rw [dite_eq_left b.2])
    have e2 : ∫ c, (fun B => if h : B ∈ hermA D n then W (hermTo ⟨B, h⟩) else 0) (a.1 * c.1 * adj a.1) ∂lam =
        ∫ c, W (hermTo (conjH a c)) ∂lam :=
      integral_congr_ae (Filter.Eventually.of_forall fun c => by
        show (if h : a.1 * c.1 * adj a.1 ∈ hermA D n then W (hermTo ⟨_, h⟩) else 0) = W (hermTo (conjH a c))
        rw [dite_eq_left (show a.1 * c.1 * adj a.1 ∈ hermA D n from (conjH a c).2)]
        rfl)
    rw [← e1, hc, e2]
    simp only [hpt]
    rw [integral_const_mul, hwI]
    calc ∫ c, I c ∂lam = (npow r ((V.rank : ℂ) - n) * (((r : ℝ) : ℂ) ^ n * npow r (-(V.rank : ℂ)))) * ∫ c, I c ∂lam := by
          rw [key, one_mul]
      _ = _ := by ring

end PositivityTheory.PfSWUS.SwMatch

end
end
end
