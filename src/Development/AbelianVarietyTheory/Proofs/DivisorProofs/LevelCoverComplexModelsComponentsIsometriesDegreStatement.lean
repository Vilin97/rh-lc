module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenScal
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfA
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverComparisonScalarEqOneStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqArithmeticGroupMulScalarOfMovedFramesStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexConjIsometryFlagDomainGroupNeZero
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverComponentIndexSumEqConstStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverComponentOverBaseRationalIsometry
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverPullbackReadingEqUnitConstPowMulStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticGroupConjIsometryMovesCoverPoint

section

@[expose] public section

noncomputable section

namespace GlobalTheory.LevModel

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

theorem exists_frBor_of_frOver {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) {S : Type} [CommRing S] [Algebra c.F S]
    [Algebra d.c₂.F S] {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S} {p p' : FrPt d.Xo₂ d.c₂ S}
    (h : FrOver d p y) (h' : FrOver d p' y') (hb : FrBor t p p') : ∃ t' : Ix Dw → Sˣ, FrBor t' y y' := by
  obtain ⟨e, hu, -⟩ := h
  obtain ⟨e', hu', -⟩ := h'
  obtain ⟨ex, au, -⟩ := hb
  refine (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c S y y' y').2.1 (by rw [← e, ← e', ex]) fun τ i => ?_
  obtain ⟨cf, c₁, c₂, hcf⟩ := au τ i
  refine ⟨cf, by rw [c₁]; exact (t _).isUnit, c₂, ?_⟩
  have k := (GlobalTheory.FrameLift.comb_iff d.m e (fun j => (p.tan τ j).1) cf (ex ▸ (p'.tan τ i).1)).1 hcf
  rw [funext (hu τ), hu'] at k
  exact k

theorem lact_conj_eq_rmul : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ (k₂ : (U₂ σ₂).Comp) (k : (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : GL (Fin D.R.r) D.host.E), ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Gm → (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) → GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ k δ → ∀ γ₂ ∈ ((U₂ σ₂).X k₂).Γ, ∀ x ∈ ((U₂ σ₂).X k₂).dom, ∀ x' : Frame ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Ψ D.R.r, GlobalTheory.LevModel.Moved ((U₂ σ₂).X k₂) ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k) δ x x' → ∃ γ ∈ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ, ∃ b ∈ Bor ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Ψ D.R.r, lact (MulAut.conj δ γ₂) x' = rmul (lact γ x') b := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hLev σ₂ hσ₂ k₂ k δ hG hδ hOv γ₂ hγ₂ x hx x' hM
  have hσ : GoodEmb c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) := by
    unfold GoodEmb at hσ₂ ⊢
    rw [← hσ₂]
    rfl
  have hU := hL.unf _ hσ
  have hU₂ := hL₂.unf _ hσ₂
  have hγx : lact γ₂ x ∈ ((U₂ σ₂).X k₂).dom := (ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.lact_mem_dom_iff _ hγ₂ x).2 hx
  obtain ⟨t₀, ht₀⟩ := (hU₂.2.2.2.1 k₂ k₂ ⟨x, hx⟩ ⟨lact γ₂ x, hγx⟩).2
    ⟨γ₂, hγ₂, ExtFPf.oneF _, ExtFPf.oneF_mem _, by rw [ExtFPf.rmul_oneF]⟩
  have hM' : Moved ((U₂ σ₂).X k₂) ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k) δ (lact γ₂ x) (lact (MulAut.conj δ γ₂) x') := by
    intro τ h₂ h₁
    have e := hM τ h₂ h₁
    show ((MulAut.conj δ γ₂ : GL _ _) : Matrix _ _ _).map τ * mat x' ⟨τ, h₁⟩ =
      (δ : Matrix _ _ _).map τ * ((γ₂ : Matrix _ _ _).map τ * mat x ⟨τ, h₂⟩)
    rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul (f := τ), ← Matrix.map_mul (f := τ),
      ← Units.val_mul, ← Units.val_mul, MulAut.conj_apply, inv_mul_cancel_right]
  obtain ⟨hx', t₁, -, y, hy₁, hy₂⟩ := hOv x hx x' hM
  obtain ⟨hx'', t₂, -, y', hy₁', hy₂'⟩ := hOv (lact γ₂ x) hγx _ hM'
  letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra
  obtain ⟨t', ht'⟩ := exists_frBor_of_frOver d hy₂ hy₂' ht₀
  have G := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid _ H Dw l Xo c (CAt σ₂)
  have hb := G.2.1 _ _ _ _ _ (G.2.1 _ _ _ _ _ hy₁ ht') (G.2.2.1 _ _ _ hy₁')
  obtain ⟨γ, hγ, b, hb', e⟩ := (hU.2.2.2.1 k k ⟨x', hx'⟩ ⟨_, hx''⟩).1 ⟨_, hb⟩
  exact ⟨γ, hγ, b, hb', eq_of_heq (Sigma.mk.inj e).2⟩

end GlobalTheory.LevModel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticGroupConjIsometryMovesCoverPointStatement

section

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

theorem _root_.GlobalTheory.T.arithmeticGroup_conj_isometry_moves_cover_point : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ (k₂ : (U₂ σ₂).Comp) (k : (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : GL (Fin D.R.r) D.host.E), ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Gm → (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) → GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ k δ → ∀ γ₂ ∈ ((U₂ σ₂).X k₂).Γ, ∀ x ∈ ((U₂ σ₂).X k₂).dom, ∀ x' : Frame ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Ψ D.R.r, GlobalTheory.LevModel.Moved ((U₂ σ₂).X k₂) ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k) δ x x' → ∃ γ ∈ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ, ∃ b ∈ Bor ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Ψ D.R.r, lact (MulAut.conj δ γ₂) x' = rmul (lact γ x') b := by
  first | exact @GlobalTheory.LevModel.lact_conj_eq_rmul | exact GlobalTheory.LevModel.lact_conj_eq_rmul | (intros; apply GlobalTheory.LevModel.lact_conj_eq_rmul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexConjIsometryFlagDomainGroupNeZeroStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD

theorem _root_.GlobalTheory.T.relIndex_conj_isometry_flagDomainGroup_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X₂ X : Data E r) (δ : GL (Fin r) E), X₂.Gm = X.Gm → (∀ v w, herm X₂.Gm ((δ : Matrix (Fin r) (Fin r) E).mulVec v) ((δ : Matrix (Fin r) (Fin r) E).mulVec w) = herm X₂.Gm v w) → (X₂.Γ.map (MulAut.conj δ).toMonoidHom).relIndex X.Γ ≠ 0 := by
  first | exact @GlobalTheory.ArithIndex.relIndex_map_conj_ne_zero | exact GlobalTheory.ArithIndex.relIndex_map_conj_ne_zero | (intros; apply GlobalTheory.ArithIndex.relIndex_map_conj_ne_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjCoverArithmeticGroupLeFiniteIndex

section

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LevModel

theorem goodEmb_comp_eF {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (d : DeltaDat Xo c 0)
    (σ₂ : d.c₂.F →+* ℂ) (h : GoodEmb d.c₂ σ₂) : GoodEmb c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) := by
  unfold GoodEmb at h ⊢
  rw [← h]
  rfl

theorem conj_arithGroup_le : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ (k₂ : (U₂ σ₂).Comp) (k : (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : GL (Fin D.R.r) D.host.E), ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Gm → (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) → GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ k δ → ((U₂ σ₂).X k₂).Γ.map (MulAut.conj δ).toMonoidHom ≤ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ ∧ (((U₂ σ₂).X k₂).Γ.map (MulAut.conj δ).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ ≠ 0 := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hlev σ₂ hσ₂ k₂ k δ hGm hδ hov
  have hσ := goodEmb_comp_eF d σ₂ hσ₂
  have hΨ : ((U₂ σ₂).X k₂).Ψ = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Ψ := by
    ext τ
    rw [((hL₂.unf σ₂ hσ₂).2.1 k₂).2 τ, ((hL.unf _ hσ).2.1 k).2 τ]
  refine ⟨?_, GlobalTheory.T.relIndex_conj_isometry_flagDomainGroup_ne_zero _ _ δ hGm hδ⟩
  intro g hg
  obtain ⟨γ₂, hγ₂, rfl⟩ := Subgroup.mem_map.1 hg
  obtain ⟨γ, hγ, ζ, hζ⟩ := GlobalTheory.T.eq_arithmeticGroup_mul_scalar_of_moved_frames _ _ δ (MulAut.conj δ γ₂) hΨ
    (fun x hx x' hm => GlobalTheory.T.arithmeticGroup_conj_isometry_moves_cover_point D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hlev σ₂ hσ₂ k₂ k δ hGm hδ hov γ₂ hγ₂ x hx x' hm)
  have h1 := GlobalTheory.T.coverComparison_scalar_eq_one D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hlev σ₂ hσ₂ k₂ k δ hGm hδ hov γ₂ hγ₂ γ hγ ζ hζ
  have e : (MulAut.conj δ).toMonoidHom γ₂ = γ := by
    apply Units.ext
    show ((MulAut.conj δ γ₂ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) = _
    rw [hζ, h1, mul_one]
  rw [e]
  exact hγ

end GlobalTheory.LevModel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjCoverArithmeticGroupLeFiniteIndexStatement

section

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

theorem _root_.GlobalTheory.T.conj_coverArithmeticGroup_le_finite_index : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ (k₂ : (U₂ σ₂).Comp) (k : (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : GL (Fin D.R.r) D.host.E), ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Gm → (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) → GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ k δ → ((U₂ σ₂).X k₂).Γ.map (MulAut.conj δ).toMonoidHom ≤ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ ∧ (((U₂ σ₂).X k₂).Γ.map (MulAut.conj δ).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ ≠ 0 := by
  first | exact @GlobalTheory.LevModel.conj_arithGroup_le | exact GlobalTheory.LevModel.conj_arithGroup_le | (intros; apply GlobalTheory.LevModel.conj_arithGroup_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverComponentOverBaseRationalIsometryStatement

section

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

theorem _root_.GlobalTheory.T.levelCover_component_over_base_rational_isometry : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ k₂ : (U₂ σ₂).Comp, ∃ (k : (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : GL (Fin D.R.r) D.host.E), ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Gm ∧ (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) ∧ GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ k δ := by
  first | exact @GlobalTheory.LevModel.over_comp | exact GlobalTheory.LevModel.over_comp | (intros; apply GlobalTheory.LevModel.over_comp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverComplexModelsComponentsIsometriesDegre

section

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

namespace GlobalTheory.LevModel

theorem levCover_model : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∃ (π : (U₂ σ₂).Comp → (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : (U₂ σ₂).Comp → GL (Fin D.R.r) D.host.E) (N : ℕ), 0 < N ∧ (∀ k₂, ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Gm ∧ (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) ∧ ((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom ≤ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ∧ (((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ≠ 0) ∧ (∀ k, ∑ᶠ k₂ : {k₂ // π k₂ = k}, (((U₂ σ₂).X k₂.1).Γ.map (MulAut.conj (δ k₂.1)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ = N) ∧ ∃ t : (U₂ σ₂).Comp → ℂ, (∀ k₂, ‖t k₂‖ = 1) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ sec Xo c a n, ∀ g ∈ sec d.Xo₂ d.c₂ a n, Pull d f g → ∀ k₂ (x : Frame ((U₂ σ₂).X k₂).Ψ D.R.r) (x' : Frame ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Ψ D.R.r), x ∈ ((U₂ σ₂).X k₂).dom → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ ((U₂ σ₂).X k₂).Ψ) (h₁ : τ ∈ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Ψ), mat x' ⟨τ, h₁⟩ = (δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → Even n → rdU (U₂ σ₂) g k₂ x = t k₂ ^ n * rdU (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) f (π k₂) x' := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ
  have h1 := GlobalTheory.T.levelCover_component_over_base_rational_isometry D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ
  choose π δ hGm hIso hOv using h1
  have h2 := fun k₂ => GlobalTheory.T.conj_coverArithmeticGroup_le_finite_index D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ k₂ (π k₂) (δ k₂) (hGm k₂) (hIso k₂) (hOv k₂)
  obtain ⟨N, hN, hsum⟩ := GlobalTheory.T.levelCover_component_index_sum_eq_const D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ π δ
    (fun k₂ => ⟨hGm k₂, hIso k₂, (h2 k₂).1, (h2 k₂).2, hOv k₂⟩)
  have h4 := fun k₂ => GlobalTheory.T.levelCover_pullback_reading_eq_unitConst_pow_mul D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ k₂ (π k₂) (δ k₂) (hGm k₂) (hIso k₂) (hOv k₂)
  choose t ht hread using h4
  refine ⟨π, δ, N, hN, fun k₂ => ⟨hGm k₂, hIso k₂, (h2 k₂).1, (h2 k₂).2⟩, hsum, t, ht, ?_⟩
  intro a n hD f hf g hg hP k₂ x x' hx hm hn
  exact hread k₂ a n hD f hf g hg hP x x' hx hm hn

end GlobalTheory.LevModel
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverComplexModelsComponentsIsometriesDegreStatement

section

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

theorem _root_.GlobalTheory.T.levelCover_complexModels_components_isometries_degree : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∃ (π : (U₂ σ₂).Comp → (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : (U₂ σ₂).Comp → GL (Fin D.R.r) D.host.E) (N : ℕ), 0 < N ∧ (∀ k₂, ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Gm ∧ (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) ∧ ((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom ≤ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ∧ (((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ≠ 0) ∧ (∀ k, ∑ᶠ k₂ : {k₂ // π k₂ = k}, (((U₂ σ₂).X k₂.1).Γ.map (MulAut.conj (δ k₂.1)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ = N) ∧ ∃ t : (U₂ σ₂).Comp → ℂ, (∀ k₂, ‖t k₂‖ = 1) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ sec Xo c a n, ∀ g ∈ sec d.Xo₂ d.c₂ a n, Pull d f g → ∀ k₂ (x : Frame ((U₂ σ₂).X k₂).Ψ D.R.r) (x' : Frame ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Ψ D.R.r), x ∈ ((U₂ σ₂).X k₂).dom → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ ((U₂ σ₂).X k₂).Ψ) (h₁ : τ ∈ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Ψ), mat x' ⟨τ, h₁⟩ = (δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → Even n → rdU (U₂ σ₂) g k₂ x = t k₂ ^ n * rdU (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) f (π k₂) x' := by
  first | exact @GlobalTheory.LevModel.levCover_model | exact GlobalTheory.LevModel.levCover_model | (intros; apply GlobalTheory.LevModel.levCover_model <;> assumption)
end
end
