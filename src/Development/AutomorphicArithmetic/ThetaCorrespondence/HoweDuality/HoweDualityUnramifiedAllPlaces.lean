module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgAtLeAlgD
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelInfAlt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.FactorApply
public import Development.WeilBound.ThetaLifts.SphericalLattices.HoweInert
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLinearTensorPolyVacuumPureTensorsStatement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstMemberLieAlgebraPreservesPolynomialFock
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstMemberMaximalCompactPreservesPolynomialFockStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HoweDualityRealPlacesPolynomialVectorsSmallPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsIntertwining
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankSchwartzBruhatAdicCompletionPiLeAleph0
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryDualPairGlobalToLocalTensorTransferStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.Imports
public import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.KerV
public import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.KerVp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.RadIrr
public import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.RadSph
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.WeilBound.ThetaLifts.SphericalLattices.ExistsFixedSum
public import Development.WeilBound.ThetaLifts.SphericalLattices.HoweDuality
public import Development.WeilBound.ThetaLifts.SphericalLattices.ThetaSubSup
public import Development.WeilBound.ThetaLifts.SphericalSplitting.SphSplitGeo

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstMemberLieAlgebraPreservesPolynomialFockStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix


theorem _root_.GlobalTheory.T.firstMember_lieAlgebra_preserves_polynomialFock : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → GlobalTheory.LFun.IsHecke F E χX → GlobalTheory.LFun.IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w, (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
        ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, ∀ f ∈ M.Pol ψ τ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ → f₁ ∈ M.Pol ψ τ := by
  first | exact @GlobalTheory.RealLieFockX.lie_deriv_polX | exact GlobalTheory.RealLieFockX.lie_deriv_polX | (intros; apply GlobalTheory.RealLieFockX.lie_deriv_polX <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.HoweDualityRealPlacesPolynomialVectorsSmallPairStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix


theorem _root_.GlobalTheory.T.howeDuality_realPlaces_polynomialVectors_smallPair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' N →
        N ≠ G.M'.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p' f = 0) →
    (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.V', ∀ f ∈ G.M'.Pol Bs.ψ Bs.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om' (γ (Multiplicative.ofAdd t), 1)) f f₁ → f₁ ∈ G.M'.Pol Bs.ψ Bs.emb) →
    (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.V' Bs.emb, ∀ f ∈ G.M'.Pol Bs.ψ Bs.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om' (k, 1)) f f₁ → f₁ ∈ G.M'.Pol Bs.ψ Bs.emb) →
    Module.rank ℂ ↥(G.M'.Pol Bs.ψ Bs.emb) ≤ Cardinal.aleph0 ∧
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ↥(G.M'.Pol Bs.ψ Bs.emb)), StrictMono N →
        (∀ j, GlobalTheory.HoweGlobalPair.relInf G.M' Bs.ψ Bs.emb om' ≤ N j ∧ ∀ g ∈ GlobalTheory.HoweGlobalPair.opInf G.M' Bs.ψ Bs.emb om', ∀ x ∈ N j, g x ∈ N j) → m ≤ L) ∧
    (∀ N : Submodule ℂ ↥(G.M'.Pol Bs.ψ Bs.emb), GlobalTheory.HoweGlobalPair.relInf G.M' Bs.ψ Bs.emb om' ≤ N → (∀ g ∈ GlobalTheory.HoweGlobalPair.opInf G.M' Bs.ψ Bs.emb om', ∀ x ∈ N, g x ∈ N) → N ≠ ⊤ → N ≤ LinearMap.ker (R.p' ∘ₗ (G.M'.Pol Bs.ψ Bs.emb).subtype)) ∧
    GlobalTheory.HoweGlobalPair.relInf G.M' Bs.ψ Bs.emb om' ≤ LinearMap.ker (R.p' ∘ₗ (G.M'.Pol Bs.ψ Bs.emb).subtype) ∧
    ∀ g ∈ GlobalTheory.HoweGlobalPair.opInf G.M' Bs.ψ Bs.emb om', ∀ x ∈ LinearMap.ker (R.p' ∘ₗ (G.M'.Pol Bs.ψ Bs.emb).subtype), g x ∈ LinearMap.ker (R.p' ∘ₗ (G.M'.Pol Bs.ψ Bs.emb).subtype) := by
  first | exact @GlobalTheory.HoweGlobalPair.RealPlaceSmall.realTransfer' | exact GlobalTheory.HoweGlobalPair.RealPlaceSmall.realTransfer' | (intros; apply GlobalTheory.HoweGlobalPair.RealPlaceSmall.realTransfer' <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsGaussianKernel

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix

noncomputable section

namespace GlobalTheory.HoweGlobalPair

theorem decomp {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀] {ι : Type} [Fintype ι] {M : ι → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (t : M₀ ⊗[ℂ] (⨂[ℂ] i, M i)) :
    ∃ (m : ℕ) (f : Fin m → M₀) (φ : Fin m → ∀ i, M i), t = ∑ j, f j ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (φ j) := by
  apply GlobalTheory.HoweGlobal.decomp <;> assumption

theorem det_ne_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h

  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let B : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have key : Bᵀ * M * B.map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]
    ext i j
    simp [B, Matrix.mul_apply]
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul] at hdet
  intro h0
  rw [h0, mul_zero, zero_mul, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one] at hdet
  exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero) hdet.symm

theorem det_ne_sig_map {E : Type} [Field E] {n r s : ℕ} {J : Matrix (Fin n) (Fin n) E} (τ : E →+* ℂ) (c : ℂ)
    (h : HasSig (c • J.map τ) r s) : J.det ≠ 0 := by
  intro h0
  apply det_ne_hasSig h
  have hmap : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
  rw [Matrix.det_smul, hmap, h0, map_zero, mul_zero]

theorem hecke_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : Chr F E} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') := by
  refine ⟨?_, fun x => ?_⟩
  · have hc : Continuous fun z => χ z / χ' z := h.1.div' h'.1
    exact hc
  · rw [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]

theorem resEta_div {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
    {χ χ' : Aˣ →* Circle} {n m k : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) (hk : k = n + m) :
    ResEtaPow K (χ / χ') k := by
  subst hk
  intro x
  rw [MonoidHom.div_apply, Circle.coe_div, h x, h' x]
  split_ifs
  · exact div_one 1
  · rw [pow_add, div_eq_mul_inv, ← inv_pow, inv_neg, inv_one]

end GlobalTheory.HoweGlobalPair

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.RelStable

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.Lit.HoweDuality GlobalTheory.HoweGlobalPair

theorem UpperTheory.Lit.HoweDuality.relStable :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W} {v : Pl (F := F)} {ω : UA σ X.J × UA σ W.J → Module.End ℂ (PositivityTheory.ThK.Fn F n d v)} {ρ : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Module.End ℂ (PositivityTheory.ThK.Fn F n d v)}, PositivityTheory.ThK.IsLocRep M ψ om v ω ρ → Stable (opFin om v) (relFin om v) := by
  intro F E _ _ _ _ _ σ n d X W M ψ om v ω ρ hL g hg x hx
  obtain ⟨h, hh, hact⟩ := hg
  have h1X : (1 : UA σ X.J) ∈ UAt σ X ⇑(evFin F v) := by
    show At _ (mat (1 : UA σ X.J) - 1)
    intro u _
    rw [show mat (1 : UA σ X.J) = 1 from rfl, sub_self, smul_zero]
  have h1W : (1 : UA σ W.J) ∈ UAt σ W ⇑(evFin F v) := by
    show At _ (mat (1 : UA σ W.J) - 1)
    intro u _
    rw [show mat (1 : UA σ W.J) = 1 from rfl, sub_self, smul_zero]
  have hgx : ((g x : SB (Fin n × Fin d → Fv F v)) : (Fin n × Fin d → Fv F v) → ℂ) = ω (1, h) (x : (Fin n × Fin d → Fv F v) → ℂ) :=
    (hL.acts 1 h1X h hh x x.2 _).1 (hact x)
  have key : augAt om v ≤ (augAt om v).comap (ω (1, h)) := by
    refine Submodule.span_le.mpr ?_
    rintro z ⟨g', hg', φ, hφ, φ₁, hφ₁, hA, rfl⟩
    have e1 : φ₁ = ω (g', 1) φ := (hL.acts g' hg' 1 h1W φ hφ φ₁).1 hA
    subst e1
    have m1 := hL.mul 1 h1X h hh g' hg' 1 h1W φ hφ
    have m2 := hL.mul g' hg' 1 h1W 1 h1X h hh φ hφ
    simp only [one_mul, mul_one] at m1 m2
    have hp : ω (1, h) φ ∈ SB (Fin n × Fin d → Fv F v) := hL.pres 1 h1X h hh φ hφ
    simp only [SetLike.mem_coe, Submodule.mem_comap, map_sub]
    rw [← m1, m2]
    exact Submodule.subset_span ⟨g', hg', ω (1, h) φ, hp, ω (g', 1) (ω (1, h) φ),
      hL.pres g' hg' 1 h1W _ hp, (hL.acts g' hg' 1 h1W _ hp _).2 rfl, rfl⟩
  have hx' : (x : (Fin n × Fin d → Fv F v) → ℂ) ∈ augAt om v := hx
  show ((g x : SB (Fin n × Fin d → Fv F v)) : (Fin n × Fin d → Fv F v) → ℂ) ∈ augAt om v
  rw [hgx]
  exact key hx'
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.HoweDualityUnramifiedAllPlaces

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix

noncomputable section

namespace UpperTheory.Lit.HoweDuality

open GlobalTheory.HoweGlobalPair

theorem sphTri : PositivityTheory.Sph.SphTri :=
  PositivityTheory.Sph.sphTri_of PositivityTheory.Sph.sphSplit_geo (PositivityTheory.Sph.vacInert PositivityTheory.Sph.howeInert)

theorem locV {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {Bs : Base F E} {a a' : ℕ}
    {G : Geo σ a a'} {Xc : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {R : RealMaps F a a'} {Rf : FinMaps F a a'}
    (hM : IsMatched Bs G Xc om om' R Rf) (v : Pl (F := F)) :
    Stable (opFin om v) (relFin om v) ∧
      Rad (opFin om v) (relFin om v) (LinearMap.ker (Rf.p v ∘ₗ (SB (Fin a × Fin (a + a') → Fv F v)).subtype)) := by
  obtain ⟨ω, ρ, L⟩ := (PositivityTheory.Sph.locRep_tri hM.triple v).1
  have hk := kerV hM v
  refine ⟨relStable L, ?_⟩
  rcases (sphTri F E σ Bs a a' G Xc om om' hM.triple v).1 with h | h
  · exact radSph L h _ hk.1 hk.2.1 hk.2.2.1
  · exact radIrr L h _ hk.1 hk.2.1 hk.2.2.1

theorem locVp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {Bs : Base F E} {a a' : ℕ}
    {G : Geo σ a a'} {Xc : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {R : RealMaps F a a'} {Rf : FinMaps F a a'}
    (hM : IsMatched Bs G Xc om om' R Rf) (v : Pl (F := F)) :
    Stable (opFin om' v) (relFin om' v) ∧
      Rad (opFin om' v) (relFin om' v) (LinearMap.ker (Rf.p' v ∘ₗ (SB (Fin a' × Fin (a + a') → Fv F v)).subtype)) := by
  obtain ⟨ω, ρ, L⟩ := (PositivityTheory.Sph.locRep_tri hM.triple v).2
  have hk := kerVp hM v
  refine ⟨relStable L, ?_⟩
  rcases (sphTri F E σ Bs a a' G Xc om om' hM.triple v).2 with h | h
  · exact radSph L h _ hk.1 hk.2.1 hk.2.2.1
  · exact radIrr L h _ hk.1 hk.2.1 hk.2.2.1

theorem stageVp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' N →
        N ≠ G.M'.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p' f = 0) →
    ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ), GlobalTheory.SquareAgree.IsThetaSubG G.M' Bs.ψ Bs.emb om' N →
      ∀ T : Finset (Pl (F := F)), Xc.T ⊆ T →
        GlobalTheory.HoweGlobal.algAt G.M' Bs.ψ Bs.emb T ≤ N ∨
          ∀ Φ ∈ N, Φ ∈ GlobalTheory.HoweGlobal.algAt G.M' Bs.ψ Bs.emb T → PolMatch Bs G Xc R Rf 0 Φ := by
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM hreal N hN T hT
  classical
  have hTr := hM.triple
  have hg := hTr.geo
  have hc := hTr.chars
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have dV' : G.V'.J.det ≠ 0 := det_ne_sig_map (Bs.emb w₀).1 1 (by rw [one_smul]; exact hg.hV'.sig w₀)
  have dW : G.W.J.det ≠ 0 := det_ne_sig_map (Bs.emb w₀).1 Complex.I (hg.hW.sig w₀)
  have hres := resEta_div hc.resα hc.resβ (Nat.add_comm a a')
  have hhk := hecke_div hc.heckeα hc.heckeβ
  have hlie := GlobalTheory.T.firstMember_lieAlgebra_preserves_polynomialFock F E σ hTr.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' hTr.base.std
    hg.hV'.herm dV' hg.hW.skew dW hc.resα hres hc.heckeα hhk hTr.weil' Bs.emb hg.hV'.cartan hg.hW.cartan
  have hcpt := GlobalTheory.T.firstMember_maximalCompact_preserves_polynomialFock F E σ hTr.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' hTr.base.std
    hg.hV'.herm dV' hg.hW.skew dW hc.resα hres hc.heckeα hhk hTr.weil' Bs.emb hg.hV'.cartan hg.hW.cartan
  obtain ⟨L, hL, hrange⟩ := GlobalTheory.T.exists_linear_tensor_polyVacuum_pureTensors G.M' Bs.ψ Bs.emb hg.hM'.std T
  have hloc := GlobalTheory.T.howeDuality_realPlaces_polynomialVectors_smallPair F E σ Bs a a' G Xc om om' R Rf hM hreal hlie hcpt
  have hfl := fun v => locVp hM v
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.unitaryDualPair_global_to_local_tensor_transfer G.M' Bs.ψ Bs.emb om' (fun v => (hg.hM'.vac v).1) hg.hM'.std N hN T L hL
  have key := tens (ι := T) (M₀ := ↥(G.M'.Pol Bs.ψ Bs.emb))
    (M := fun v : T => ↥(SB (Fin a' × Fin (a + a') → Fv F v.1)))
    (opInf G.M' Bs.ψ Bs.emb om') (fun v => opFin om' v.1)
    (relInf G.M' Bs.ψ Bs.emb om') (fun v => relFin om' v.1)
    (R.p' ∘ₗ (G.M'.Pol Bs.ψ Bs.emb).subtype) (fun v => Rf.p' v.1 ∘ₗ (SB _).subtype)
    hloc.1 (fun v => GlobalTheory.TripleAssembly.rank_SB_adicCompletion_le F _ v.1) hloc.2.1 hloc.2.2.1 hloc.2.2.2.1 hloc.2.2.2.2
    (fun v => (hfl v.1).1) (fun v => (kerVp hM v.1).2.1) (fun v => (hfl v.1).2) (fun v => (kerVp hM v.1).2.2.2)
    (N.comap L) h1 h2 h3 h4
  rcases key with htop | hker
  · left
    intro Φ hΦ
    obtain ⟨t, rfl⟩ := hrange hΦ
    have ht : t ∈ N.comap L := by rw [htop]; exact Submodule.mem_top
    exact ht
  · right
    intro Φ hΦN hΦT
    obtain ⟨t, rfl⟩ := hrange hΦT
    have ht0 := hker (show t ∈ N.comap L from hΦN)
    obtain ⟨m, f, φ, rfl⟩ := GlobalTheory.HoweGlobalPair.decomp t
    refine ⟨T, hT, 0, m, Fin.elim0, Fin.elim0, fun j => ((f j : ↥(G.M'.Pol Bs.ψ Bs.emb)) : SInf F (Fin a' × Fin (a + a'))),
      fun j v => if h : v ∈ T then ((φ j ⟨v, h⟩ : ↥(SB _)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) else G.M'.vac v,
      fun j => Fin.elim0 j, fun j => ⟨(f j).2, fun v => ?_, fun v hv => by simp only [dif_neg hv]⟩, ?_, ?_, ?_⟩
    · by_cases h : v ∈ T
      · simp only [dif_pos h]; exact (φ j ⟨v, h⟩).2
      · simp only [dif_neg h]; exact (hg.hM'.vac v).1
    · simp
    · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => hL _ _ _ (fun v h => by simp only [dif_pos h]) (fun v h => by simp only [dif_neg h])
    · set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearMap.mem_ker, map_sum] at ht0
      rw [Fin.sum_univ_zero, ← ht0]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [TensorProduct.map_tmul, PiTensorProduct.map_tprod]
      simp

theorem allVp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' N →
        N ≠ G.M'.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p' f = 0) →
    ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ), GlobalTheory.SquareAgree.IsThetaSubG G.M' Bs.ψ Bs.emb om' N →
      N ≠ GlobalTheory.SquareAgree.algD G.M' Bs.ψ Bs.emb → ∀ Φ ∈ N, PolMatch Bs G Xc R Rf 0 Φ := by
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM hreal N hN hne Φ hΦ
  by_contra hcon
  obtain ⟨T, hT, hΦT⟩ := GlobalTheory.HoweGlobal.exists_algAt G.M' Bs.ψ Bs.emb (hN.le hΦ) Xc.T
  apply hne
  refine le_antisymm hN.le fun Ψ hΨ => ?_
  obtain ⟨T', hT', hΨT'⟩ := GlobalTheory.HoweGlobal.exists_algAt G.M' Bs.ψ Bs.emb hΨ T
  rcases stageVp F E σ Bs a a' G Xc om om' R Rf hM hreal N hN T' (hT.trans hT') with h | h
  · exact h hΨT'
  · exact absurd (h Φ hΦ (GlobalTheory.HoweGlobal.algAt_mono G.M' Bs.ψ Bs.emb hT' hΦT)) hcon

end UpperTheory.Lit.HoweDuality

end
end
end
