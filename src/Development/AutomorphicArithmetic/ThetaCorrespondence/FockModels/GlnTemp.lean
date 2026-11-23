module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TemperedProductOfSquareIntegrable
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.EssSquareIntegrableSegments
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.GlnSuff
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.CasselmanSuffTemp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TSchur
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TUnitcent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.GlnTOrderfree
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TCosocleUnit
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TProdExp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFreeStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLanglandsOfIrreducibleAdmissibleStatement
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsTemperedCoeff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedLanglandsFactorsSquareIntegrableStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientSegmentProductEquivStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosocleOfContragredientSocle
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOne
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLengthStatement
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityCuspidalProductStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentTermInjectiveStatement
import GroundTheory.LocalFields.PadicLogSeries
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Development

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.GlnTCentred

section

@[expose] public section

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

theorem UpperTheory.Lit.Cas.centred :
    GlobalTheory.Published.EssSquareIntegrableSegments → GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (Δ : Segment k) (y : IrrGL (k := k)), IsLSeg Δ y.rep → (∀ (t : kˣ) (c : ℂ), ScalarBy y t c → ‖c‖ = 1) → IsSqIntCoeff y.rep := by
  intro H HA k _ _ _ _ _ Δ δ h hu
  have hpos : 0 < δ.1 := by
    obtain ⟨hd, -⟩ := h
    rw [← hd]
    have h1 : ∀ a, (Δ.term a).1 = Δ.first.1 := fun a => rfl
    simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    exact Nat.mul_pos Δ.len_pos Δ.isCusp_first.1
  obtain ⟨χ, hχ, hsq⟩ := (H k δ hpos).2 ⟨Δ, h⟩
  let e := δ.twEquiv χ hχ
  let τ := (δ.tw χ hχ).rep
  have he : ∀ g w, e.toLinearEquiv.symm (τ g w) =
      ((detChar (Fin δ.1) χ g : ℂˣ) : ℂ) • δ.rep g (e.toLinearEquiv.symm w) := fun g w => by
    obtain ⟨u, rfl⟩ := e.toLinearEquiv.surjective w
    have := e.toIntertwiningMap.isIntertwining _ _ g u
    rw [LinearEquiv.symm_apply_apply]
    refine e.toLinearEquiv.injective ?_
    rw [LinearEquiv.apply_symm_apply]
    exact this.symm
  have hτ : UnitaryCentral τ :=
    UpperTheory.Lit.Cas.unitcent k _ _ τ 2 (δ.tw χ hχ).2.rep.smooth (δ.tw χ hχ).2.rep.irr hsq
  have hχ1 : ∀ a : kˣ, ‖((χ a : ℂˣ) : ℂ)‖ = 1 := by
    intro a
    let z := Matrix.GeneralLinearGroup.scalar (Fin δ.1) a
    obtain ⟨c, hc⟩ := (UpperTheory.Lit.Cas.schur HA k δ a).1
    have hc1 := hu a c hc
    have hz1 : ‖((detChar (Fin δ.1) χ z : ℂˣ) : ℂ) * c‖ = 1 := by
      refine hτ a _ fun w => ?_
      refine e.toLinearEquiv.symm.injective ?_
      refine (he z w).trans ?_
      rw [map_smul, mul_smul]
      exact congrArg _ (hc _)
    rw [norm_mul, hc1, mul_one] at hz1
    have hdz : ((detChar (Fin δ.1) χ z : ℂˣ) : ℂ) = ((χ a : ℂˣ) : ℂ) ^ δ.1 := by
      have hdet : Matrix.GeneralLinearGroup.det z = a ^ δ.1 := Units.ext (by
        simp [z, Matrix.GeneralLinearGroup.scalar, Matrix.algebraMap_eq_diagonal, Matrix.det_diagonal])
      rw [detChar_apply, hdet, map_pow, Units.val_pow_eq_pow_val]
    rw [hdz, norm_pow] at hz1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hpos.ne').1 hz1
  intro m bm μ hμ v ℓ hℓ'
  let l' : Module.Dual ℂ _ := ℓ ∘ₗ e.toLinearEquiv.symm.toLinearMap
  have hc : ∀ g, ‖l' (τ g (e.toLinearEquiv v))‖ = ‖((detChar (Fin δ.1) χ g : ℂˣ) : ℂ)‖ * ‖ℓ (δ.rep g v)‖ := fun g => by
    simp only [l', LinearMap.comp_apply, LinearEquiv.coe_coe, he, LinearEquiv.symm_apply_apply, map_smul, smul_eq_mul,
      norm_mul]
  have hFc0 : ∀ g : GL (Fin δ.1) k, ‖l' (τ g (e.toLinearEquiv v))‖ = ‖((detChar (Fin δ.1) χ g : ℂˣ) : ℂ)‖ * ‖ℓ (δ.rep g v)‖ :=
    fun g => hc g
  have hopen : IsOpen {g : GL (Fin δ.1) k | l' ∘ₗ τ g = l'} := by
    have hk : IsOpen ((detChar (Fin δ.1) χ).ker : Set (GL (Fin δ.1) k)) := hχ.detChar
    refine isOpen_iff_mem_nhds.2 fun g hg => ?_
    have hg' : l' ∘ₗ τ g = l' := hg
    have hU : {x | ℓ ∘ₗ δ.rep x = ℓ} ∩ ((detChar (Fin δ.1) χ).ker : Set (GL (Fin δ.1) k)) ∈ nhds (g⁻¹ * g) := by
      rw [inv_mul_cancel]; exact Filter.inter_mem (hℓ'.mem_nhds (by show ℓ ∘ₗ δ.rep 1 = ℓ; rw [map_one, Module.End.one_eq_id, LinearMap.comp_id]))
        (hk.mem_nhds (one_mem _))
    refine Filter.mem_of_superset ((continuous_const_mul g⁻¹).continuousAt.preimage_mem_nhds hU) fun x hx => ?_
    obtain ⟨h1, h2⟩ := hx
    have h1' : ℓ ∘ₗ δ.rep (g⁻¹ * x) = ℓ := h1
    have h2' : detChar (Fin δ.1) χ (g⁻¹ * x) = 1 := h2
    show l' ∘ₗ τ x = l'
    have hx' : τ x = τ g * τ (g⁻¹ * x) := (congrArg τ (mul_inv_cancel_left g x)).symm.trans (map_mul τ g (g⁻¹ * x))
    rw [hx', Module.End.mul_eq_comp, ← LinearMap.comp_assoc, hg']
    ext w
    simp only [l', LinearMap.comp_apply, LinearEquiv.coe_coe]
    refine (congrArg ℓ (he (g⁻¹ * x) w)).trans ?_
    rw [map_smul, h2', Units.val_one, one_smul]
    exact LinearMap.congr_fun h1' _
  obtain ⟨F, hF, hL⟩ := @hsq m bm μ hμ (e.toLinearEquiv v) l' hopen
  refine ⟨F, fun g => ?_, hL⟩
  refine ((hF g).trans (hFc0 g)).trans ?_
  rw [detChar_apply, hχ1, one_mul]
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareIntegrableUnitarizable

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.SqIntUnit

theorem isUnitarisable_of_isSqIntCoeff : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)), IsSqIntCoeff x.rep → IsUnitarisable x.rep := by
  intro k _ _ _ _ x h
  exact GlobalTheory.SqIntUnit.main k x.1 _ x.rep x.2.rep.smooth x.2.rep.irr h

end GlobalTheory.CompanionTheory.SqIntUnit
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareIntegrableUnitarizableStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

theorem _root_.GlobalTheory.T.square_integrable_unitarizable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)), IsSqIntCoeff x.rep → IsUnitarisable x.rep := by
  first | exact @GlobalTheory.CompanionTheory.SqIntUnit.isUnitarisable_of_isSqIntCoeff | exact GlobalTheory.CompanionTheory.SqIntUnit.isUnitarisable_of_isSqIntCoeff | (intros; apply GlobalTheory.CompanionTheory.SqIntUnit.isUnitarisable_of_isSqIntCoeff <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentSubquotients.ExistsSocleSegmentProduct

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.LkSegSocle

theorem dec_injective {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) :
    Function.Injective (dec Δ) :=
  (GlobalTheory.T.segment_term_injective hA Δ).comp Fin.rev_injective

theorem ncard_perm_dec_le_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) :
    Set.ncard {e : Fin Δ.len ≃ Fin Δ.len | ∀ a, dec Δ a = dec Δ (e a)} ≤ 1 := by
  have hinj := dec_injective hA Δ
  have hsub : {e : Fin Δ.len ≃ Fin Δ.len | ∀ a, dec Δ a = dec Δ (e a)} ⊆ {Equiv.refl _} := by
    intro e he
    simp only [Set.mem_setOf_eq] at he
    rw [Set.mem_singleton_iff]
    exact Equiv.ext fun a => (hinj (he a)).symm
  calc _ ≤ ({Equiv.refl _} : Set (Fin Δ.len ≃ Fin Δ.len)).ncard :=
        Set.ncard_le_ncard hsub (Set.finite_singleton _)
    _ = 1 := Set.ncard_singleton _

theorem exists_isSocle_prodIrr_dec : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ}
    (hd : ∑ a, (dec Δ a).1 = N), ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr (dec Δ) hd) := by
  intro k _ _ _ _ hA Δ N hd
  apply GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_jm_le_one hA (dec Δ) hd
  have hc : ∀ a, (dec Δ a).IsCusp := fun a => Δ.isCusp_term (Fin.rev a)
  rw [GlobalTheory.T.jacquet_multiplicity_cuspidal_product hA (dec Δ) (dec Δ) hd hd hc hc]
  exact_mod_cast ncard_perm_dec_le_one hA Δ

end GlobalTheory.CompanionTheory.LkSegSocle

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentSubquotients.ExistsSocleSegmentProductStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
theorem _root_.GlobalTheory.TL.exists_socle_segment_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ} (hd : ∑ a, (dec Δ a).1 = N), ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr (dec Δ) hd) := by
  first | exact @GlobalTheory.CompanionTheory.LkSegSocle.exists_isSocle_prodIrr_dec | exact GlobalTheory.CompanionTheory.LkSegSocle.exists_isSocle_prodIrr_dec
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentSubquotients.ExistsSegmentRepresentation

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.LkSegExists

theorem hasFiniteLength_prodIrr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL (k := k))
    (hd : ∑ a, (x a).1 = N) : HasFiniteLength (prodIrr x hd) := by
  exact GlobalTheory.T.parabolic_induction_finite_length k (Fin h) (Fin N) (fun a => Fin (x a).1) (stdBlocks (fun a => (x a).1) hd) _
    (piTensor fun a => (x a).rep)
    (isSmooth_piTensor fun a => (x a).snd.rep.smooth)
    (hasFiniteLength_of_isIrreducible (GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hA x))

theorem exists_isLSeg : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k), ∃ π : IrrRep (GL (Fin Δ.deg) k), IsLSeg Δ π.ρ := by
  intro k _ _ _ _ hA Δ
  have hd : ∑ a, (Δ.term a).1 = Δ.deg := Δ.sum_term_fst
  obtain ⟨hd', ⟨φ⟩⟩ := GlobalTheory.T.contragredient_segment_product_equiv hA Δ hd
  obtain ⟨τ', hτ'⟩ := GlobalTheory.TL.exists_socle_segment_product hA (segDual Δ) hd'
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompanionTheory.CosocleContra.isCosocle_of_isSocle_contra hA (prodIrr Δ.term hd)
    (isSmooth_prodIrr _ _) (hasFiniteLength_prodIrr hA _ _) τ' (hτ'.of_equiv (.refl _) φ.symm)
  exact ⟨τ, hd, hτ⟩

end GlobalTheory.CompanionTheory.LkSegExists

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentSubquotients.ExistsSegmentRepresentationStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
theorem _root_.GlobalTheory.TL.exists_segment_representation : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k), ∃ π : IrrRep (GL (Fin Δ.deg) k), IsLSeg Δ π.ρ := by
  first | exact @GlobalTheory.CompanionTheory.LkSegExists.exists_isLSeg | exact GlobalTheory.CompanionTheory.LkSegExists.exists_isLSeg
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.GlnTemp

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL

namespace UpperTheory.Lit.Cas

theorem temperedProduct (hG : GlobalTheory.Published.GeometricLemma) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hF : GlobalTheory.Published.StandardFunctorsFiniteLength)
    (hE : GlobalTheory.Published.LanglandsExhaustionGL) (hC : GlobalTheory.Published.StandardCosocleGL) (hM : GlobalTheory.Published.LanglandsMultisegments)
    (hS : GlobalTheory.Published.EssSquareIntegrableSegments) : GlobalTheory.Published.TemperedProductOfSquareIntegrable := by
  intro k _ _ _ _ _ N hN V _ _ π hs hi
  constructor
  · intro ht
    have hO : Zc.LOrderFree k := orderfree hC hM k
    have hSo : Zc.LSocleGL k := GlobalTheory.T.langlands_socle_of_order_free hA (GlobalTheory.T.local_langlands_of_irreducible_admissible hA) hO
    have hL : Zc.LSegExists k := fun Δ => GlobalTheory.TL.exists_segment_representation hA Δ
    obtain ⟨𝔪, h𝔪⟩ := hE k (IrrGL.of π hs hi)
    have h𝔪' : IsL 𝔪 π := h𝔪.of_equiv (IrrGL.equivOf π hs hi).symm
    obtain ⟨h, x, hd, hx, hu⟩ := GlobalTheory.T.tempered_langlands_factors_square_integrable k hSo (Zl.JC.casselmanNecTemp_holds k) hL 𝔪 N π hN hs hi ht h𝔪'
    obtain ⟨Δ, hΔo, hΔ⟩ := hx
    have hsq : ∀ a, IsSqIntCoeff (x a).rep := fun a => centred hS hA k (Δ a) (x a) (hΔ a) (hu a)
    have e := cosocleUnit hBZ k h N x hd V π (fun a => GlobalTheory.T.square_integrable_unitarizable k (x a) (hsq a)) (hO 𝔪 h N x hd ⟨Δ, hΔo, hΔ⟩ π h𝔪')
    refine ⟨h, x, hd, fun a => ⟨?_, hsq a⟩, e⟩
    have h1 := (hΔ a).deg_eq
    have h2 := Nat.mul_pos (Δ a).len_pos (Δ a).d_pos
    simp only [Segment.deg] at h1
    omega
  · rintro ⟨h, δ, hd, hδ, e⟩
    obtain ⟨hu, hw⟩ := prodExp hG hBZ hA k (Zl.JC.casselmanNecSq_holds k) h N δ hd hδ V π hi e
    have H := casselmanSuffTemp hA hF k N π hN hs hi hu hw
    intro ε hε
    exact H ε hε

end UpperTheory.Lit.Cas

end
end
end
