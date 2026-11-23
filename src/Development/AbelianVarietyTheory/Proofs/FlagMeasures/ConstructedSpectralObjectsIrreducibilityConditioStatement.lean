module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.See
public import Formalism.LocalToGlobal.IndefiniteReal.TensCastR
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMaximalCompactReductionStandardFrameStatement
public import Formalism.LocalToGlobal.IndefiniteReal.ConjSubConjSub
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedVectorIdentityIsotypicConjugateType
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemRowsFixedByLabelTupleOpOfSumFixed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumSeriesIdempotentCoeffRightTranslationStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalActIntertwines
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTIota
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedVectorIdentityIsotypicConjugateTypeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

theorem _root_.GlobalTheory.T.fixedVectorIdentity_isotypic_conjugateType : ∀ (D : D7) (n : ℕ) (A : Type) [AddCommGroup A] [Module ℂ A] (ρ : GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A) (π : Formalism.L2.NG.FinTyp D.host.E n) (U : Set (GAf D.host.E n)) (ι : Type) [Finite ι] (a : ι → ℂ) (lf : ι → GAf D.host.E n), (∀ φ ∈ π.S, (∀ κ ∈ U, Formalism.L2.NG.rt D.host.E n κ φ = φ) → ∑ᶠ i, a i • Formalism.L2.NG.rt D.host.E n (lf i) φ = φ) → ∀ S ∈ isotIn ρ C (FinTyp.conjT π), (∀ κ ∈ U, ρ κ S = S) → ∑ᶠ i, star (a i) • ρ (lf i) S = S := by
  first | exact @GlobalTheory.IsotConjFix.isotIn_conjT_fix_sum | exact GlobalTheory.IsotConjFix.isotIn_conjT_fix_sum | (intros; apply GlobalTheory.IsotConjFix.isotIn_conjT_fix_sum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemRowsFixedByLabelTupleOpOfSumFixedStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

theorem _root_.GlobalTheory.T.mem_rowsFixedByLabelTupleOp_of_sum_fixed : ∀ (D : D7) (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd) (sec : G0g D.nd → X.B.I.Gf), IsRedHom X red → IsSec X red sec → ∀ (t : Tup2 D), (∀ k v, IsLabel D k (t k v)) → ∀ f ∈ HHX X, ∑ᶠ γ, serCoef t γ • X.B.R ((1, sec γ) : X.B.I.GA) f = f → f ∈ VT X t := by
  first | exact @GlobalTheory.LabFix.mem_VT_of_sum_fixed | exact GlobalTheory.LabFix.mem_VT_of_sum_fixed | (intros; apply GlobalTheory.LabFix.mem_VT_of_sum_fixed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LabelsFixedByTupleOperatorOfTypeSeries

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

noncomputable section

namespace GlobalTheory.LabPinTop

theorem kap_mem_GfC {D : D7} (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0))
    (k : X.B.I.Gf) : kap X h t k ∈ GfC (Yc D 0) := by
  have aux : ∀ (I : Formalism.MainNotions.S.AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (k : I.Gf),
      ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA hI.symm)).symm ((1, k) : I.GA) ∈ GfC (D.sp.Y 0) := by
    intro I hI k
    subst hI
    have e : ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA (rfl : Formalism.L2.SG.InstExistsPf.instOf D = _).symm)).symm (1, k) =
        (Formalism.IndefR.RationalEmbedding.iota D).symm (1, k) := rfl
    rw [e]
    exact (Formalism.L2.SG.EvalTIota.brg_mem_GfC_i (D := D) (1, k)).2 rfl
  have hy : (iotaX X h).symm ((1, k) : X.B.I.GA) ∈ GfC (D.sp.Y 0) := aux X.B.I h k
  show (t⁻¹ * (iotaX X h).symm (1, k) * t : GA D (D.sp.Y 0)) ∈ GfC (D.sp.Y 0)
  unfold GfC at hy ⊢
  rw [MonoidHom.mem_ker] at hy ⊢
  rw [map_mul, map_mul, hy, mul_one, map_inv, inv_mul_cancel]

theorem R_translate_ae {D : D7} (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0))
    (Φ : GA D (D.sp.Y 0) → ℂ) (hinv : ∀ γ ∈ GQ (D.sp.Y 0), ∀ g, Φ (γ * g) = Φ g) (f : L2X X)
    (hf : f =ᵐ[muX X] fun x => Φ ((iotaX X h).symm x * t)) (k : X.B.I.Gf) :
    ((X.B.R (1, k) f : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X] fun x =>
      Φ ((iotaX X h).symm x * t * (show GA D (D.sp.Y 0) from kap X h t k)) := by
  have hU : X.B.μf.IsMulRightInvariant := Formalism.L2.SG.Closed.GfUnimod_holds X.B.I X.B.μf
  have := Formalism.MainNotions.LeviCoordinates.rr_muA_left X.B.I X.B.μf
  have hFD := Formalism.MainNotions.LeviCoordinates.rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec
  have hφinv : ∀ γ ∈ X.B.I.GFset, ∀ y : X.B.I.GA,
      Φ ((iotaX X h).symm (γ * y) * t) = Φ ((iotaX X h).symm y * t) := by
    intro γ hγ y
    rw [map_mul, mul_assoc]
    exact hinv _ (iotaX_symm_rat X h γ hγ) _
  have hP : Formalism.L2.SG.Pf.RPres (X.B.I.muA X.B.μf) ((1, k) : X.B.I.GA) :=
    Formalism.L2.SG.Pf.RowDictPf.rp_fin X.B.I X.B.μf k
  have hPi : Formalism.L2.SG.Pf.RPres (X.B.I.muA X.B.μf) (((1, k) : X.B.I.GA)⁻¹) := by
    have : ((1, k) : X.B.I.GA)⁻¹ = (1, k⁻¹) := Prod.ext inv_one rfl
    rw [this]; exact Formalism.L2.SG.Pf.RowDictPf.rp_fin X.B.I X.B.μf k⁻¹
  obtain ⟨h1, h2⟩ := Formalism.L2.SG.Pf.rp_map hFD hP hPi
  have e1 := X.B.R_spec (1, k) f
  have e3 : ∀ᵐ x ∂(muX X), (f : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * (1, k))) =
      Φ ((iotaX X h).symm (X.B.I.rep X.B.fund (x * (1, k))) * t) := by
    refine ae_of_ae_map (p := fun y => (f : X.B.I.GA → ℂ) y = Φ ((iotaX X h).symm y * t)) h1 ?_
    rw [h2]
    exact hf
  filter_upwards [e1, e3] with x a1 a3
  rw [a1]
  show (f : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * (1, k))) = _
  rw [a3]
  obtain ⟨γ, hγ, hrep, -⟩ := Formalism.MainNotions.LeviCoordinates.rr_rep_spec hFD (x * (1, k))
  rw [Formalism.MainNotions.LeviCoordinates.rr_rep_eq_rep, show (Formalism.MainNotions.LeviCoordinates.rr_rep X.B.I.GFset X.B.fund (x * (1, k))) = γ * (x * (1, k)) from hrep,
    hφinv γ hγ]
  congr 1
  unfold kap
  rw [map_mul]
  group

end GlobalTheory.LabPinTop

namespace GlobalTheory.LabPinTop

theorem labTie_of_series : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) (PY : RowPsi (Yc D 0) D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H) (G : GoodOp X) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G) (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X) (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (C : Submodule ℂ (MMap (R.MY 0))), StdPsi hF PY → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ F, ι (D.sEE F) = conjHH X G (j F)) → RowJ R eE X h G t j → (∀ σ, R.HE.e (eE (D.what₂.onb σ)) ∈ isotIn (actM PY (R.MY 0)) C (FinTyp.conjT (rep (D.what₂.ft σ)))) → (∀ σ, ∀ k ∈ X.B.I.Kg X.B.g, ∀ v y, R.HE.e (eE (D.what₂.onb σ)) v (y * kap X h t k) = R.HE.e (eE (D.what₂.onb σ)) v y) → (∀ σ v, ∀ γ ∈ Formalism.L2.Theta.GQ (Yc D 0), ∀ y, R.HE.e (eE (D.what₂.onb σ)) v (γ * y) = R.HE.e (eE (D.what₂.onb σ)) v y) → TypeLab D rep → (∀ σ, D.ntypes.goodTuple (labOf σ)) → LabTie X ι := by
  intro D X h t PY hF G' _ _ Pl0 T A Ks _ _ _ R eE G j ι rep C hStd hHEq hι hJ hiso hK hQ hTL hgood
  let _ : Fintype (G0g D.nd) := Formalism.MainNotions.PrimeDegreeVariant.finiteLevelGroupFintype D
  have hlab : ∀ σ k v, IsLabel D k (D.nd.lab k (D.what₂.ft σ) v) := fun σ k v => ((hTL (D.what₂.ft σ)) k v).1
  refine ⟨hlab, hgood, fun σ => ?_⟩
  obtain ⟨c, red, hFR⟩ := GlobalTheory.T.exists_maximalCompact_reduction_standardFrame D X h t PY hF hStd hHEq
  have hRH : IsRedHom X red := hFR.1
  choose sec hsec using hRH.2.2.1
  have hIS : IsSec X red sec := fun γ => hsec γ
  choose lf hlf using fun γ => PY.onto _ (kap_mem_GfC X h t (sec γ))
  have hser := GlobalTheory.T.sum_seriesIdempotentCoeff_rightTranslation D X h t PY c red sec lf hFR hIS hlf (rep (D.what₂.ft σ)) (labOf σ) (hTL (D.what₂.ft σ))
  have hS := GlobalTheory.T.fixedVectorIdentity_isotypic_conjugateType D D.R.r (MMap (R.MY 0)) (actM PY (R.MY 0)) C (rep (D.what₂.ft σ))
    {κ | ∃ k ∈ X.B.I.Kg X.B.g, PY.ψ κ = kap X h t k} (G0g D.nd) (serCoef (labOf σ)) lf
    (fun φ hφ hU => hser φ hφ (fun k hk κ hκ => hU κ ⟨k, hk, hκ⟩)) (R.HE.e (eE (D.what₂.onb σ))) (hiso σ)
    (by
      rintro κ ⟨k, hk, hκ⟩
      refine MultilinearMap.ext fun v => funext fun y => ?_
      rw [actM_apply, hκ]
      exact hK σ k hk v y)
  have hpt : ∀ v y, ∑ γ, star (serCoef (labOf σ) γ) * R.HE.e (eE (D.what₂.onb σ)) v (y * kap X h t (sec γ)) =
      R.HE.e (eE (D.what₂.onb σ)) v y := by
    intro v y
    have e := congrArg (fun T : MMap (R.MY 0) => T v y) hS
    simp only [finsum_eq_sum_of_fintype] at e
    rw [← e, sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [smul_apply, Pi.smul_apply, smul_eq_mul, actM_apply, hlf]
  obtain ⟨v₀, -, a, -, hj⟩ := hJ
  refine GlobalTheory.T.mem_rowsFixedByLabelTupleOp_of_sum_fixed D X red sec hRH hIS (labOf σ) (fun k v => hlab σ k v) (bRow X ι σ)
    (ι (D.sEE (D.what₂.onb σ))).2 ?_
  set Φ : GA D (D.sp.Y 0) → ℂ := fun y => star ((a : ℂ) * R.HE.e (eE (D.what₂.onb σ)) v₀ y) with hΦ
  have hΦinv : ∀ γ ∈ GQ (D.sp.Y 0), ∀ g, Φ (γ * g) = Φ g := fun γ hγ g =>
    congrArg (fun z => star ((a : ℂ) * z)) (hQ σ v₀ γ hγ g)
  have hb : bRow X ι σ = star ((j (D.what₂.onb σ) : EEC X G) : L2X X) := by
    show ((ι (D.sEE (D.what₂.onb σ)) : HHX X) : L2X X) = _
    rw [hι]
    rfl
  have hbr : (bRow X ι σ : X.B.I.GA → ℂ) =ᵐ[muX X] fun x => Φ ((iotaX X h).symm x * t) := by
    rw [hb]
    filter_upwards [Lp.coeFn_star ((j (D.what₂.onb σ) : EEC X G) : L2X X), hj (D.what₂.onb σ)] with x b1 b2
    rw [b1, Pi.star_apply, b2]
    rfl
  have htr := fun γ => R_translate_ae X h t Φ hΦinv (bRow X ι σ) hbr (sec γ)
  rw [finsum_eq_sum_of_fintype]
  apply Lp.ext
  filter_upwards [coeFn_sum_smul (μ := muX X) (serCoef (labOf σ)) (fun γ => X.B.R ((1, sec γ) : X.B.I.GA) (bRow X ι σ)),
    ae_all_iff.2 htr, hbr] with x b1 b2 b3
  rw [b1, b3]
  simp only [b2, hΦ]
  rw [← hpt v₀ ((iotaX X h).symm x * t)]
  rw [Finset.mul_sum, star_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  have e : ∀ (c b s : ℂ), c * star (b * s) = star (b * (star c * s)) := fun c b s => by
    simp only [star_mul', star_star]; ring
  exact e _ _ _

end GlobalTheory.LabPinTop
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LabelsFixedByTupleOperatorOfTypeSeriesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

theorem _root_.GlobalTheory.T.labels_fixed_by_tupleOperator_of_typeSeries : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) (PY : RowPsi (Yc D 0) D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H) (G : GoodOp X) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G) (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X) (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (C : Submodule ℂ (MMap (R.MY 0))), StdPsi hF PY → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ F, ι (D.sEE F) = conjHH X G (j F)) → RowJ R eE X h G t j → (∀ σ, R.HE.e (eE (D.what₂.onb σ)) ∈ isotIn (actM PY (R.MY 0)) C (FinTyp.conjT (rep (D.what₂.ft σ)))) → (∀ σ, ∀ k ∈ X.B.I.Kg X.B.g, ∀ v y, R.HE.e (eE (D.what₂.onb σ)) v (y * kap X h t k) = R.HE.e (eE (D.what₂.onb σ)) v y) → (∀ σ v, ∀ γ ∈ Formalism.L2.Theta.GQ (Yc D 0), ∀ y, R.HE.e (eE (D.what₂.onb σ)) v (γ * y) = R.HE.e (eE (D.what₂.onb σ)) v y) → TypeLab D rep → (∀ σ, D.ntypes.goodTuple (labOf σ)) → LabTie X ι := by
  first | exact @GlobalTheory.LabPinTop.labTie_of_series | exact GlobalTheory.LabPinTop.labTie_of_series | (intros; apply GlobalTheory.LabPinTop.labTie_of_series <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealisationLabelsNormalisedOfRowsTypesLevels

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

open scoped TensorProduct

namespace GlobalTheory.LabPinAt

theorem mult_lev_left {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : T ∈ Mult θ M J χ) :
    (∀ v, ∀ k ∈ J, ∀ g, T v (g * k) = χ k * T v g) ∧ ∀ v, ∀ γ ∈ GQ V, ∀ g, T v (γ * g) = T v g := by
  induction hT using Submodule.span_induction with
  | mem x hx => exact ⟨hx.lev, fun v γ hγ g => (hx.aut v).left γ hγ g⟩
  | zero => exact ⟨fun v k _ g => by simp, fun v γ _ g => by simp⟩
  | add x y _ _ hx hy =>
    refine ⟨fun v k hk g => ?_, fun v γ hγ g => ?_⟩
    · simp only [MultilinearMap.add_apply, Pi.add_apply, hx.1 v k hk g, hy.1 v k hk g]; ring
    · simp only [MultilinearMap.add_apply, Pi.add_apply, hx.2 v γ hγ g, hy.2 v γ hγ g]
  | smul c x _ hx =>
    refine ⟨fun v k hk g => ?_, fun v γ hγ g => ?_⟩
    · simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hx.1 v k hk g]; ring
    · simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hx.2 v γ hγ g]

end GlobalTheory.LabPinAt

theorem GlobalTheory.LabPinAt.labTie_at : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) (PY : RowPsi (Yc D 0) D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H) (G : GoodOp X) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G) (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X) (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (F : Face D A), StdPsi hF PY → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ y, ι (D.sEE y) = conjHH X G (j y)) → RowJ R eE X h G t j → LevelMatchA R F X h t → (∀ σ, R.HE.e (eE (D.what₂.onb σ)) ∈ isotE R.θ PY (R.MY 0) (JR R F) (chiR R F) R.e0 (rep (D.what₂.ft σ))) → TypeLab D rep → GoodFTAll D → LabTie X ι := by
  intro D X h t PY hF G' _ _ Pl0 T A Ks _ _ _ R eE G j ι rep F hPsi hE hι hRJ hLev hIso hTL hGood
  have hM : ∀ σ, R.HE.e (eE (D.what₂.onb σ)) ∈ Mult R.θ (R.MY 0) (JR R F) (chiR R F) := fun σ => (hIso σ).1.1
  refine GlobalTheory.T.labels_fixed_by_tupleOperator_of_typeSeries D X h t PY hF G' Pl0 T A Ks R eE G j ι rep (Minf R.θ PY (R.MY 0)) hPsi hE hι hRJ
    (fun σ => (hIso σ).2) ?_ ?_ hTL (fun σ => hGood (D.what₂.ft σ))
  · intro σ k hk v y
    obtain ⟨hk2, hc⟩ := (Formalism.L2.SG.Closed.level_subgroup_properties X).1 k hk
    obtain ⟨hJ, hχ⟩ := hLev k hk2
    rw [(GlobalTheory.LabPinAt.mult_lev_left R.θ (hM σ)).1 v _ hJ y, show chiR R F (kap X h t k) = star (X.chi2 k) from hχ, hc,
      star_one, one_mul]
  · intro σ v γ hγ y
    exact (GlobalTheory.LabPinAt.mult_lev_left R.θ (hM σ)).2 v γ hγ y
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealisationLabelsNormalisedOfRowsTypesLevelsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

theorem _root_.GlobalTheory.T.realisationLabels_normalised_of_rowsTypes_levels : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) (PY : RowPsi (Yc D 0) D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H) (G : GoodOp X) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G) (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X) (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (F : Face D A), StdPsi hF PY → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ y, ι (D.sEE y) = conjHH X G (j y)) → RowJ R eE X h G t j → LevelMatchA R F X h t → (∀ σ, R.HE.e (eE (D.what₂.onb σ)) ∈ isotE R.θ PY (R.MY 0) (JR R F) (chiR R F) R.e0 (rep (D.what₂.ft σ))) → TypeLab D rep → GoodFTAll D → LabTie X ι := by
  first | exact @GlobalTheory.LabPinAt.labTie_at | exact GlobalTheory.LabPinAt.labTie_at | (intros; apply GlobalTheory.LabPinAt.labTie_at <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConstructedSpectralObjectsIrreducibilityConditio

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists Formalism.MainNotions Formalism.L2.Forms Formalism.L2.SG.PackageTie2 MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe GlobalTheory.Mem.Top.Bl Formalism.IndefR.principalLevelFrame
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

namespace GlobalTheory.Sat

theorem ties_at : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H) (F0 : ∀ u, Forms0 D u) (s : SAt R F eE F0) (PY : RowPsi (Yc D 0) D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E) (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r), StdPsi hF PY → (∀ σ, R.HE.e (eE (D.what₂.onb σ)) ∈ isotE R.θ PY (R.MY 0) (JR R F) (chiR R F) R.e0 (rep (D.what₂.ft σ))) → GlobalTheory.LabPin.TypeLab D rep → GoodFTAll D → Formalism.MainNotions.S.AutTie D s.P.X.B s.P.X.pl ∧ RowDictTie s.P.X s.P.G s.S.hI.eHH ∧ GlobalTheory.LabPin.LabTie s.P.X s.S.hI.eHH := by
  intro D G' _ _ Pl0 T A Ks _ _ _ R F eE F0 s PY hF rep hP hiso hT hG
  exact ⟨s.S.autTie, s.S.rowTie,
    GlobalTheory.T.realisationLabels_normalised_of_rowsTypes_levels D s.P.X s.P.inst s.t PY hF G' Pl0 T A Ks R eE s.P.G s.S.j s.S.hI.eHH rep F hP s.P.pin s.S.rowPin s.rowJ
      s.see.levelMatchA hiso hT hG⟩

end GlobalTheory.Sat
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConstructedSpectralObjectsIrreducibilityConditioStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists Formalism.MainNotions Formalism.L2.Forms Formalism.L2.SG.PackageTie2 MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe GlobalTheory.Mem.Top.Bl Formalism.IndefR.principalLevelFrame
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

theorem _root_.GlobalTheory.T.constructedSpectralObjects_irreducibilityConditions : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H) (F0 : ∀ u, Forms0 D u) (s : SAt R F eE F0) (PY : RowPsi (Yc D 0) D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E) (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r), StdPsi hF PY → (∀ σ, R.HE.e (eE (D.what₂.onb σ)) ∈ isotE R.θ PY (R.MY 0) (JR R F) (chiR R F) R.e0 (rep (D.what₂.ft σ))) → GlobalTheory.LabPin.TypeLab D rep → GoodFTAll D → Formalism.MainNotions.S.AutTie D s.P.X.B s.P.X.pl ∧ RowDictTie s.P.X s.P.G s.S.hI.eHH ∧ GlobalTheory.LabPin.LabTie s.P.X s.S.hI.eHH := by
  first | exact @GlobalTheory.Sat.ties_at | exact GlobalTheory.Sat.ties_at | (intros; apply GlobalTheory.Sat.ties_at <;> assumption)
end
end
