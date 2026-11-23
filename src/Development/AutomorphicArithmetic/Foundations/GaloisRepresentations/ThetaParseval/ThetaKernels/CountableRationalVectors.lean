module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SecondOrbitBijection
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContinuousCA
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.MeasurableSh
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinSecondTerm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BlockDiagonalPreservesFormIff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.UnipotentNilpotentMulEqZero
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.CountableRationalPointsDoubled
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContinuousPhzK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinTermLeftInvariant
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.UnipotentFirstMatrix
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContinuousABK

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
def cMF_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (δ : E) (c : (Fin L.n → AE F E) × AF F) :
    Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ c.2) 0 ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-c.1))ᵀ.map (cA σ))
def cMF'_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (δ : E) (c : (Fin L.n → AE F E) × AF F) :
    Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-c.1)) (-(_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-c.1) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ c.2 * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1)ᵀ.map (cA σ))) 0 ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1)ᵀ.map (cA σ))
theorem cMF_mul_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (δ : E) (c : (Fin L.n → AE F E) × AF F) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cMF_k (σ := σ) L δ c * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cMF'_k L δ c = 1 := by
  have e1 := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_mul_neg_k L c.1
  have e2 : (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-c.1))ᵀ.map (cA σ) * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1)ᵀ.map (cA σ) = 1 := by
    rw [← kunf.map_cA_mul, ← Matrix.transpose_mul, e1, Matrix.transpose_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have e3 : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1 * -(_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-c.1) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ c.2 * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1)ᵀ.map (cA σ)) +
      _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ c.2 * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1)ᵀ.map (cA σ) = 0 := by
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.one_mul, neg_add_cancel]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.cMF_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cMF'_k, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [e1, e2, e3, Matrix.fromBlocks_one]
theorem continuous_aB_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (δ : E) :
    Continuous fun c : (Fin L.n → AE F E) × AF F => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k (σ := σ) L δ c.2 := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, Matrix.single_apply]
  split_ifs
  · exact Continuous.smul (continuous_snd (X := Fin L.n → AE F E) (Y := AF F))
      (continuous_const (y := inclR (F := F) (E := E) (AF F) δ))
  · exact continuous_const
theorem continuous_cM_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) : Continuous cM := by
  have hF : ∀ c, inFrame d.b (cM c) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cMF_k L δ c := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_cM_k h
  have hN := _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.continuous_unipotent_nilpotent L
  have hU : Continuous fun c : (Fin L.n → AE F E) × AF F => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1 :=
    continuous_const.add (hN.comp continuous_fst)
  have hUn : Continuous fun c : (Fin L.n → AE F E) × AF F => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-c.1) :=
    continuous_const.add (hN.comp continuous_fst.neg)
  have hcA : Continuous fun M : Matrix (Fin d.n) (Fin d.n) (AE F E) => M.map (cA σ) :=
    continuous_id.matrix_map (GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ)
  have hA := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.continuous_aB_k (σ := σ) L δ
  have hc : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.cMF_k (σ := σ) L δ) :=
    Continuous.matrix_fromBlocks hU hA continuous_const (hcA.comp hUn.matrix_transpose)
  have hc' : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.cMF'_k (σ := σ) L δ) :=
    Continuous.matrix_fromBlocks hUn ((hUn.matrix_mul hA).matrix_mul (hcA.comp hU.matrix_transpose)).neg
      continuous_const (hcA.comp hU.matrix_transpose)
  have h1 : Continuous fun c => incM F d.b.1 * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cMF_k L δ c * incM F (d.b⁻¹).1 :=
    (continuous_const.matrix_mul hc).matrix_mul continuous_const
  have h2 : Continuous fun c => incM F d.b.1 * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cMF'_k L δ c * incM F (d.b⁻¹).1 :=
    (continuous_const.matrix_mul hc').matrix_mul continuous_const
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · refine h1.congr fun c => ?_
    show _ = mat2 (cM c)
    rw [kunf.matrix_eq_inFrame_conj d.b, hF c]
  · refine h2.congr fun c => ?_
    show _ = mat2 (cM c)⁻¹
    rw [kunf.matrix_eq_inFrame_conj d.b, GlobalTheory.EisBL.DoubledParabolic.inFrame_inv, hF c, Matrix.inv_eq_right_inv (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.cMF_mul_k L δ c)]
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.CountableRationalVectors

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
set_option linter.style.haveILetI false
def rationalCosetEquiv (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L ≃ L.ratV × fA F where
  toFun c := (⟨c.1.1, c.2.1⟩, ⟨c.1.2, c.2.2⟩)
  invFun c := ⟨((c.1 : Fin L.n → AE F E), (c.2 : AF F)), c.1.2, c.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
theorem countable_rational_vectors (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) : Countable L.ratV := by
  have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  refine Function.Surjective.countable (f := fun v : Fin L.n → E =>
    (⟨GlobalTheory.ThK.incV F v, AddSubgroup.subset_closure ⟨v, rfl⟩⟩ : L.ratV)) fun u => ?_
  obtain ⟨v, hv⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.ratV_inc_k u.2
  exact ⟨v, Subtype.ext hv.symm⟩
theorem coset_point_decomposition (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) {γ' : G2 σ L.Y}
    {Λ : ((Fin L.n → AE F E) × (Fin L.n → AE F E)) ≃ₜ+ ((Fin L.n → AE F E) × (Fin L.n → AE F E))}
    {Q : (Fin L.n → AE F E) × (Fin L.n → AE F E) → AF F}
    (hΛ : ∀ b u a, L.j γ' * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (u, a)) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (Λ (b, u)).1 * cM ((Λ (b, u)).2, a + Q (b, u)) * L.j γ')
    {Z : (Fin L.n → AE F E) → (Fin L.n → AE F E) → AF F}
    (hZ : ∀ u₀ a₀ b u a, cM (u₀, a₀) * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (u, a)) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (u₀ + u, a₀ + a + Z u₀ b))
    (Y : d.G) (c₀ : (Fin L.n → AE F E) × AF F) (p : (Fin L.n → AE F E) × ((Fin L.n → AE F E) × AF F)) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c₀ * (L.j γ' * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.1 * (cM (p.1, p.2.2) * Y))))) =
      _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM (UnfoldingIntegralSum.sh Λ Q Z c₀ p) * (L.j γ' * Y))) := by
  obtain ⟨u₀, a₀⟩ := c₀
  obtain ⟨u, b, a⟩ := p
  have e1 : L.j γ' * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * (cM (u, a) * Y)) = (L.j γ' * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (u, a))) * Y := by simp only [mul_assoc]
  have e2 : ∀ c', cM (u₀, a₀) * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (Λ (b, u)).1 * cM c' * L.j γ' * Y) =
      (cM (u₀, a₀) * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (Λ (b, u)).1 * cM c')) * (L.j γ' * Y) := by intro c'; simp only [mul_assoc]
  rw [e1, hΛ, e2, hZ, mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.section_unipotent_invariant h hf z]
  simp only [UnfoldingIntegralSum.sh, add_assoc]
theorem unfqE_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ)
    {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤)
    {𝓐 : Set (AF F)} (h𝓐 : IsAddFundamentalDomain (fA F) 𝓐 (lamA F)) {γ' : G2 σ L.Y} (hγ : γ' ∈ rat2 σ L.Y) (Y : d.G) :
    ∫⁻ p, ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c₀.1 * (L.j γ' * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.1 * (cM (p.1, p.2.2) * Y)))))‖ₑ
        ∂((ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod ((lamA F).restrict 𝓐))) =
      ∫⁻ c, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c * (L.j γ' * Y)))‖ₑ ∂(ν.prod (lamA F)) := by
  obtain ⟨-, hν, hU0, hU1⟩ := hU
  haveI := hν
  haveI := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.countable_rational_vectors L
  obtain ⟨Λ, Q, hQ, hΛeq, hΛrat⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.j_conj_k (R := R) h γ'
  obtain ⟨Z, hZ, -, hheis⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.heis_k (R := R) h
  have hg : Continuous fun c => _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c * (L.j γ' * Y))) :=
    (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.continuous_phz_k d hf.cont s₁ z).comp (continuous_const.mul ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.continuous_cM_k h).mul continuous_const))
  rw [← UnfoldingIntegralSum.unf_lint hU0 hU1 (fd_prod hU0 hU0) h𝓐 Λ (hΛrat hγ) hQ.measurable hZ.measurable hg.measurable.enorm]
  refine lintegral_congr fun p => ?_
  rw [← (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.rationalCosetEquiv L).symm.tsum_eq]
  exact tsum_congr fun c => by rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.coset_point_decomposition h hf z hΛeq hheis]; rfl
theorem unfqC_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ)
    {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤)
    {𝓐 : Set (AF F)} (h𝓐 : IsAddFundamentalDomain (fA F) 𝓐 (lamA F)) {γ' : G2 σ L.Y} (hγ : γ' ∈ rat2 σ L.Y) (Y : d.G)
    (hfin : ∫⁻ c, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c * (L.j γ' * Y)))‖ₑ ∂(ν.prod (lamA F)) < ⊤) :
    ∫ p, ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c₀.1 * (L.j γ' * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.1 * (cM (p.1, p.2.2) * Y)))))
        ∂((ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod ((lamA F).restrict 𝓐))) =
      ∫ c, _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c * (L.j γ' * Y))) ∂(ν.prod (lamA F)) := by
  obtain ⟨-, hν, hU0, hU1⟩ := hU
  haveI := hν
  haveI := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.countable_rational_vectors L
  obtain ⟨Λ, Q, hQ, hΛeq, hΛrat⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.j_conj_k (R := R) h γ'
  obtain ⟨Z, hZ, -, hheis⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.heis_k (R := R) h
  have hg : Continuous fun c => _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c * (L.j γ' * Y))) :=
    (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.continuous_phz_k d hf.cont s₁ z).comp (continuous_const.mul ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.continuous_cM_k h).mul continuous_const))
  rw [← UnfoldingIntegralSum.unf_int hU0 hU1 (fd_prod hU0 hU0) h𝓐 Λ (hΛrat hγ) hQ.measurable hZ.measurable hg.measurable hfin]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  beta_reduce
  rw [← (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.rationalCosetEquiv L).symm.tsum_eq]
  exact tsum_congr fun c => by rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.coset_point_decomposition h hf z hΛeq hheis]; rfl
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
end
end
