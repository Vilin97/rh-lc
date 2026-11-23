module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotLv3MvFixH
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StarCoeffOfEqReverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootsReverseProd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RootsMinpolyPhi
public import Mathlib.RepresentationTheory.Coinduced
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemChainVecsDet
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColsTiedSym
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDiscreteSeriesFormalDegreeProduct
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpectralObjectsOverReplacedStagesStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueScaleIsScale

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.LabelEqOfMemSuppSpan

section

@[expose] public section

noncomputable section

namespace GlobalTheory.SeriesSupport

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp Formalism.MainNotions.ArithmeticCylinders Formalism.BasicNotions Formalism.CyclotomicNorms
open scoped Classical

section Dual

variable {g : ℕ} [Fact g.Prime]

theorem phi_conj (L : LabelDatum g) (x : Fbar g) : GalSer.phi L (starRingAut : ℂ ≃+* ℂ) x = x⁻¹ := by
  by_cases hx : x = 0
  · rw [hx, GalSer.phi_zero, inv_zero]
  apply GalSer.teich_injective L
  rw [GalSer.teich_phi]
  have h1 : ‖L.teich x‖ = 1 := (L.teich.isOfFinOrder (GalSer.finOrder hx)).norm_eq_one
  have h2 : L.teich x⁻¹ = (L.teich x)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel₀ hx, map_one])
  rw [h2, Complex.inv_eq_conj h1]
  rfl

theorem roots_reverse {K : Type} [Field K] (s : Multiset K) (hs : (0 : K) ∉ s) :
    ((s.map fun x => X - C x).prod.reverse).roots = s.map (·⁻¹) := by
  apply GlobalTheory.DualLabel.roots_reverse_prod <;> assumption

theorem rel_dual (L : LabelDatum g) {f : (ZMod g)[X]} (hm : f.Monic) (h0 : f.coeff 0 ≠ 0) :
    GalSer.Rel L (starRingAut : ℂ ≃+* ℂ) f (C (f.coeff 0)⁻¹ * f.reverse) := by
  refine ⟨?_, ?_⟩
  · rw [Monic, leadingCoeff_mul, leadingCoeff_C, reverse_leadingCoeff, trailingCoeff_eq_coeff_zero h0,
      inv_mul_cancel₀ h0]
  · have hz : (0 : Fbar g) ∉ rootsBar f := fun h => by
      rw [GalSer.mem_rootsBar hm.ne_zero, ← coeff_zero_eq_aeval_zero'] at h
      exact h0 ((map_eq_zero _).1 h)
    have e : f.reverse.map (algebraMap (ZMod g) (Fbar g)) = (f.map (algebraMap (ZMod g) (Fbar g))).reverse := by
      rw [reverse, reverse, reflect_map, natDegree_map]
    have hf := (IsAlgClosed.splits (f.map (algebraMap (ZMod g) (Fbar g)))).eq_prod_roots_of_monic (hm.map _)
    rw [rootsBar, Polynomial.map_mul, map_C, roots_C_mul _ (by simpa using h0), e, hf]
    simp only [phi_conj]
    exact roots_reverse _ hz

end Dual

local instance factTypePrime (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

abbrev LocRep (D : D7) (k : Fin 2) (n : ℕ) : Type 1 := Rep.{0} ℂ (GL (Fin n) ℚ_[D.host.g k])

variable (D : D7)
  (σ : D.ntypes.Par → ∀ k, D.nd.PlG k → LocRep D k D.R.r)
  (ΩV : D.what₂.Tup → ℕ → ∀ k, D.nd.PlG k → LocRep D k D.R.nV)
  (ιV : ∀ μ j k v, D.what₂.Mt μ j →ₗ[ℂ] ΩV μ j k v)
  (ΩX : D.what₂.Tup → ∀ k, D.nd.PlG k → LocRep D k D.R.rankX')
  (ιX : ∀ μ k v, D.what₂.Amb μ →ₛₗ[starRingEnd ℂ] ΩX μ k v)

end GlobalTheory.SeriesSupport
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDiscreteSeriesFormalDegreeProductStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_discreteSeries_formalDegree_product : DiscreteSeriesExist → FormalDegreeFormula₂ → ∀ (cd : CDHaar) (R : Ranks) (P : HCParam R), (∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin (2 * R.rS + R.k + 1)) (Fin (2 * R.rS + R.k + 1)) ℂ → (H →L[ℂ] H)), IsDS (epsSH R) (lamSH R P) σ ∧ IsFdeg ((trueScale cd _ (epsSH R) : ENNReal) • Formalism.REAL.muG (epsSH R)) σ (trueDsig R P)) ∧ ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin (2 * R.rS + R.k + 1)) (Fin (2 * R.rS + R.k + 1)) ℂ → (H →L[ℂ] H)) (d : ℝ), IsDS (epsSH R) (lamSH R P) σ → IsFdeg ((trueScale cd _ (epsSH R) : ENNReal) • Formalism.REAL.muG (epsSH R)) σ d → d = trueDsig R P := by
  first | exact @GlobalTheory.Mem.Vol.exists_isDS_isFdeg_trueDsig | exact GlobalTheory.Mem.Vol.exists_isDS_isFdeg_trueDsig | (intros; apply GlobalTheory.Mem.Vol.exists_isDS_isFdeg_trueDsig <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RangeEEAndNorm

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.RowsLvl

section Scale

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem isMultiplicityInner_smul_measure (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' : MMap M) {c : ℝ}
    (hc : 0 < c) {k : ℂ} (h : IsMultIP M μ 𝓕 T T' k) :
    IsMultIP M (ENNReal.ofReal c • μ) 𝓕 T T' ((c : ℂ) * k) := by
  intro v v'
  obtain ⟨hi, he⟩ := h v v'
  refine ⟨?_, ?_⟩
  · unfold IntegrableOn at hi ⊢
    rw [Measure.restrict_smul]
    exact hi.smul_measure ENNReal.ofReal_ne_top
  · rw [Measure.restrict_smul, integral_smul_measure, he, ENNReal.toReal_ofReal hc.le, Complex.real_smul, mul_assoc]

theorem ipM_smul (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' : MMap M) {c : ℝ}
    (hc : 0 < c) (hv : ∃ v : M.Vec, ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0) :
    ipM M (ENNReal.ofReal c • μ) 𝓕 T T' = (c : ℂ) * ipM M μ 𝓕 T T' := by
  obtain ⟨v, hv⟩ := hv
  by_cases h : ∃ k, IsMultIP M μ 𝓕 T T' k
  · have hs := isMultiplicityInner_smul_measure M μ 𝓕 T T' hc (ipM_spec M μ 𝓕 T T' h)
    exact hasPeterssonInner_unique M _ 𝓕 T T' v hv (ipM_spec M _ 𝓕 T T' ⟨_, hs⟩) hs
  · have h' : ¬ ∃ k, IsMultIP M (ENNReal.ofReal c • μ) 𝓕 T T' k := by
      rintro ⟨k, hk⟩
      have e : ENNReal.ofReal c⁻¹ • ENNReal.ofReal c • μ = μ := by
        rw [smul_smul, ← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), inv_mul_cancel₀ hc.ne', ENNReal.ofReal_one, one_smul]
      have := isMultiplicityInner_smul_measure M _ 𝓕 T T' (inv_pos.2 hc) hk
      rw [e] at this
      exact h ⟨_, this⟩
    unfold ipM
    rw [dite_eq_right h, dite_eq_right h', mul_zero]

theorem mmap_eq_zero (M : DSModel V S) (hv : ¬ ∃ v : M.Vec, ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0) (T : MMap M) :
    T = 0 := by
  classical
  have : ∃ τ, ∀ w : M.sm τ, w = 0 := by
    by_contra hne
    push_neg at hne
    choose w hw using hne
    refine hv ⟨w, Finset.prod_ne_zero_iff.2 fun τ _ => ?_⟩
    rw [inner_self_ne_zero]
    exact fun h0 => hw τ (Subtype.ext h0)
  obtain ⟨τ, hτ⟩ := this
  ext v g
  rw [T.map_coord_zero τ (hτ (v τ))]
  rfl

end Scale

end GlobalTheory.Mem.R3.RowsLvl

namespace GlobalTheory.Mem.R3.RowsLvl



theorem range_eE_and_norm : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → LinearMap.range Y.eE = (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)).comap R.HE.e ∧ ∀ x, ‖Y.eE x‖ ^ 2 = RealDat.nP F.lv2 true * ‖x‖ ^ 2 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP _
  have hE : R.models_HE := hP.char.base.models.HE
  have hEEc : (toChainReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop).EEc true =
      (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)).map
        (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap := rfl
  have hlift : Function.Injective (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _) :=
    LinearEquiv.injective _
  refine ⟨?_, fun x => ?_⟩
  · ext h
    constructor
    · rintro ⟨x, rfl⟩
      have hm := (Y.Ish.jE x).2
      rw [Y.eE_read, hEEc] at hm
      obtain ⟨u, hu, he⟩ := hm
      have : u = R.HE.e (Y.eE x) := hlift he
      rw [Submodule.mem_comap, ← this]
      exact hu
    · intro hh
      rw [Submodule.mem_comap] at hh
      have hm : (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _) (R.HE.e h) ∈
          (toChainReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop).EEc true := by
        rw [hEEc]; exact ⟨_, hh, rfl⟩
      refine ⟨Y.Ish.jE.symm ⟨_, hm⟩, ?_⟩
      have e1 := Y.eE_read (Y.Ish.jE.symm ⟨_, hm⟩)
      rw [LinearEquiv.apply_symm_apply] at e1
      exact (hE.1 (hlift e1)).symm
  · have hx := Y.tied.sharp.ee x x
    have hy := hE.2.2 (Y.eE x) (Y.eE x)
    have hnP : 0 < RealDat.nP F.lv2 true := by
      unfold RealDat.nP; exact_mod_cast Nat.card_pos
    by_cases hv : ∃ v : (R.MY 0).Vec, ∏ τ, ⟪(v τ : (R.MY 0).H τ), (v τ : (R.MY 0).H τ)⟫_ℂ ≠ 0
    · have e : ⟪x, x⟫_ℂ = (((RealDat.nP F.lv2 true)⁻¹ : ℝ) : ℂ) * ⟪Y.eE x, Y.eE x⟫_ℂ := by
        rw [hx, hy]
        show ipMT _ _ _ _ _ = _
        unfold ipMT
        rw [Y.eE_read]
        erw [LinearEquiv.symm_apply_apply]
        exact ipM_smul _ _ _ _ _ (inv_pos.2 hnP) hv
      rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at e
      have e' : ‖x‖ ^ 2 = (RealDat.nP F.lv2 true)⁻¹ * ‖Y.eE x‖ ^ 2 := by
        apply Complex.ofReal_injective
        rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_pow]
        exact e
      rw [e', ← mul_assoc, mul_inv_cancel₀ hnP.ne', one_mul]
    · have h0 : Y.eE x = 0 :=
        hE.1 (by rw [mmap_eq_zero _ hv (R.HE.e (Y.eE x)), mmap_eq_zero _ hv (R.HE.e 0)])
      have h1 : (Y.Ish.jE x).1 = 0 := by
        rw [Y.eE_read, h0, map_zero]; exact map_zero _
      have hx0 : x = 0 := (LinearEquiv.map_eq_zero_iff _).1 (Submodule.coe_eq_zero.1 h1)
      simp [h0, hx0]

end GlobalTheory.Mem.R3.RowsLvl
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelThreeToFour

section

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.SRe.UpS

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.ConcreteSettingExists Formalism.MainNotions Formalism.L2.Forms MeasureTheory NumberField IsDedekindDomain
  GlobalTheory.EX GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.SRe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def RowHyp {D : D7} (p : RowPk D) : Prop :=
  p.R.toLevCh.Is p.A.μ0 ∧ p.R.grp_levels p.F ∧ GrpPin p.R ∧ p.R.IsModels ∧
    LinearMap.range p.eE = (p.R.EEat (p.R.levR p.F true)).comap p.R.HE.e ∧
    (∀ x, ‖p.eE x‖ ^ 2 = RealDat.nP p.F true * ‖x‖ ^ 2) ∧ DallTie p.R p.F



theorem rowHyp_read {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (cG : G0 R.Pg D.R.r ≃* G0g D.nd) {X0 : BaseLevelRowSide D} (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (hP : R3.Pins R F cG)
    (hH : R3.Holds R F) : RowHyp (⟨G, Pl0, T, A3.A, Ks, R.toRealDat, F.lv2, Y.eE⟩ : RowPk D) := by
  have hr := R3.RowsLvl.range_eE_and_norm D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH
  obtain ⟨plg, iso, h⟩ := hP.keep.grp
  exact ⟨hP.char.base.lev, hP.char.base.grp.levels, ⟨R.eG.trans cG, plg, iso, h⟩, hP.char.base.models, hr.1, hr.2, Y.dall⟩

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}



theorem rowHyp_pkOf {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (r : RowsT K w Z Wt p0) : RowHyp (pkOf r) :=
  (by with_unfolding_all exact ((rowHyp_read r.r.z.R r.r.z.F r.r.z.cG r.r.Y r.r.z.pins r.r.intersectionNumber_baseChange) :))

def reSt {C : Cols B} (a : Late B C) (Zs : SNew a.D) : SStage B C a.W := reStage a.st Zs

def SatNew : Prop :=
  ∀ (B : Base) (C : Cols B) (a : Late B C) (p : RowPk a.D) (F0 : ∀ u, Forms0 a.D u) (P : SPack a.D F0), GapHyp a.D →
    Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I) → Formalism.L2.SG.Pf.LocCP.LocTied a.D → RealTied a.D →
    a.D.what₂.Dstar = StandardLattice.DstarD a.D → IdempotentRealFixed a.D → RowHyp p →
    ∃ Zs : SNew a.D, ∀ (N : ∀ u, Submodule (𝓞 a.D.what₂.LL) (a.D.div.Nu u).V) (hh : a.D.what₂.Word → ℝ)
      (F₁ : ∀ u, Forms0 (reL a ⟨Zs, N, hh⟩).D u), SameL a ⟨Zs, N, hh⟩ F0 F₁ → Nonempty (SAtL a ⟨Zs, N, hh⟩ p.R p.F p.eE F₁)


theorem satOfDiscreteSeries (h1 : GlobalTheory.Dec.DSInfChar) (h2 : GlobalTheory.Published.HarishChandraFinite) (h3 : GlobalTheory.Published.CuspRapidDecay)
    (h4 : GlobalTheory.Published.DiscreteSeriesUpqUnique) (h5 : Formalism.L2.SG.RowsDef.RowsFinDim) : SatNew :=
  fun B C a p F0 P g i l r d e ⟨a1, a2, a3, a4, a5, a6, a7⟩ =>
    GlobalTheory.T.exists_spectralObjects_over_replacedStages h1 h2 h3 h4 h5 B C a p.G' p.Pl0 p.T p.A p.Ks p.R p.F F0 p.eE P g i l r d a1 a2 a3 e a4 a5 a6 a7



theorem sat_col (a : w.Lt) (col : ColT w a) (p : RowPk (Late.D a)) (Zs : SNew (Late.D a))
    (H : ∀ (N : ∀ u, Submodule (𝓞 (Late.D a).what₂.LL) ((Late.D a).div.Nu u).V) (hh : (Late.D a).what₂.Word → ℝ)
      (F₁ : ∀ u, Forms0 (reL a ⟨Zs, N, hh⟩).D u), SameL a ⟨Zs, N, hh⟩ (fun u => (col.C.forms u).to0) F₁ →
        Nonempty (SAtL a ⟨Zs, N, hh⟩ p.R p.F p.eE F₁))
    (N : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V) (h : B.Word → ℝ) (col' : ColT w (upL a (reSt a Zs) N h)) :
    Nonempty ((p.up a (reSt a Zs) N h).SAt fun u => (col'.C.forms u).to0) := by
  let Zn : New (Late.D a) := ⟨Zs, (by with_unfolding_all exact (N :)), (by with_unfolding_all exact (h :))⟩
  obtain ⟨C', hC⟩ := ColRe.exists_colsTiedSym (Late.D a) Zn col.C
  let F₀ : ∀ u, Forms0 (reD (Late.D a) Zn) u := fun u => (C'.forms u).to0
  let F₁ : ∀ u, Forms0 (reL a Zn).D u := (by with_unfolding_all exact (F₀ :))
  have hF : SameL a Zn (fun u => (col.C.forms u).to0) F₁ := (by with_unfolding_all exact (hC :))
  obtain ⟨s⟩ := H Zn.N Zn.h F₁ hF
  have c := CarModel.sameStd B f T w a Zn col ((by with_unfolding_all exact (col' :))) F₁ hF
  exact ⟨CarModel.satCar (D := Late.D (upL a (reSt a Zs) N h)) (F := (by with_unfolding_all exact (F₁ :))) ((by with_unfolding_all exact (c :))) (p.up a (reSt a Zs) N h) ((by with_unfolding_all exact (s :)))⟩

def RealOf : Prop := ∀ D : D7, VolTieG D → D.s.cdScale = Vol.trueScale D.cd → (∀ τ, D.dsig τ = Vol.trueDsig D.R (D.hc τ)) → RealTied D

def PackEx : Prop := ∀ (D : D7) (F : ∀ u, Forms0 D u), GapHyp D → Formalism.L2.SG.Pf.LocCP.LocTied D →
  ∃ P : SPack D F, Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I)



theorem real_of (hR : RealOf) (a : w.Lt) (g : GIs2 K w a.G) (hs : a.S.s.cdScale = Vol.trueScale a.G.cd)
    (hd : ∀ τ, a.S.dsig τ = Vol.trueDsig B.R (B.hc τ)) : RealTied (w.D a) :=
  hR (w.D a) (g a.W a.V a.S a.N).1 ((by with_unfolding_all exact (hs :))) ((by with_unfolding_all exact (hd :)))



theorem realOf (h1 : Vol.DiscreteSeriesExist) (h2 : Vol.FormalDegreeFormula₂) : RealOf := by
  intro D hv hs hd
  refine ⟨?_, ?_, ?_, hv⟩
  · rw [Vol.cdScaleTie_iff, hs]
    exact GlobalTheory.Mem.Vol.ScaleExists.trueScale_isScale D.cd
  · intro τ
    unfold Formalism.L2.Theta.IsDsig
    rw [hs, hd τ]
    exact (GlobalTheory.T.exists_discreteSeries_formalDegree_product h1 h2 D.cd D.R (D.hc τ)).1
  · intro τ H _ _ σ d hσ hf
    rw [hs] at hf
    rw [hd τ]
    exact (GlobalTheory.T.exists_discreteSeries_formalDegree_product h1 h2 D.cd D.R (D.hc τ)).2 H σ d hσ hf

theorem goodIdempotent_real_of_harishChandra_series (D : D7) (h : GlobalTheory.GLq.ESerTie D) : IdempotentRealFixed D :=
  GlobalTheory.GoodIdemReal.star_coeff_of_reverse D fun k g hm h0 x => by
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    obtain ⟨L, -, he⟩ := h k
    rw [he, he]
    exact DFunLike.congr_fun (GlobalTheory.GLq.GalSer.eSerC_map L _ D.R.r hm (GlobalTheory.SeriesSupport.rel_dual L hm h0)) x

end GlobalTheory.Mem.SRe.UpS

end
end
end
