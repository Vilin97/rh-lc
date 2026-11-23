module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseCoverFramesDifferByRationalIsometry
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverComponentEqImpliesBaseComponentEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverReadingEqPowMulMovedFrameReading
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoverDictionaryAdelicElementComponent
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalIsometryMapsFlagDomainFrames
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitConstantCoverPullbackReadingStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseCoverFramesDifferByRationalIsometryStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.base_cover_frames_differ_by_rational_isometry : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ h : GA D (T.V j σ), ∃ γ : GL (Fin D.R.r) D.host.E, (((T.U j σ).X (T.dict j σ h).1).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X (C.dict₂ h).1).Λ : Set _) ∧ (∀ v w, herm ((T.U j σ).X (T.dict j σ h).1).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X (C.dict₂ h).1).Gm v w) ∧ (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat (T.dict j σ h).2 ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h).2 ⟨τ, h₂⟩) := by
  first | exact @GlobalTheory.CoverFrameMove.frames_differ | exact GlobalTheory.CoverFrameMove.frames_differ | (intros; apply GlobalTheory.CoverFrameMove.frames_differ <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverComponentEqImpliesBaseComponentEqStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.cover_component_eq_implies_base_component_eq : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ h h' : GA D (T.V j σ), (C.dict₂ h).1 = (C.dict₂ h').1 → (T.dict j σ h).1 = (T.dict j σ h').1 := by
  first | exact @GlobalTheory.CoverRead.CompIndep.comp_eq_of_cover | exact GlobalTheory.CoverRead.CompIndep.comp_eq_of_cover | (intros; apply GlobalTheory.CoverRead.CompIndep.comp_eq_of_cover <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverReadingEqPowMulMovedFrameReadingStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.coverReading_eq_pow_mul_movedFrameReading : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (h : GA D (T.V j σ)) (γ : GL (Fin D.R.r) D.host.E), (((T.U j σ).X (T.dict j σ h).1).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X (C.dict₂ h).1).Λ : Set _) → (∀ v w, herm ((T.U j σ).X (T.dict j σ h).1).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X (C.dict₂ h).1).Gm v w) → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat (T.dict j σ h).2 ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h).2 ⟨τ, h₂⟩) → ∀ (x : Frame (C.U₂.X (C.dict₂ h).1).Ψ D.R.r) (x' : Frame ((T.U j σ).X (T.dict j σ h).1).Ψ D.R.r), x ∈ (C.U₂.X (C.dict₂ h).1).dom → x' ∈ ((T.U j σ).X (T.dict j σ h).1).dom → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → ∃ t : ℂ, t ≠ 0 ∧ ∀ n : ℕ, ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → rdU C.U₂ f₂ (C.dict₂ h).1 x = t ^ n * rdU (T.U j σ) f (T.dict j σ h).1 x' := by
  first | exact @GlobalTheory.CoverFrameRead.rdU_cover_eq | exact GlobalTheory.CoverFrameRead.rdU_cover_eq | (intros; apply GlobalTheory.CoverFrameRead.rdU_cover_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoverDictionaryAdelicElementComponentStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_coverDictionary_adelic_element_component : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ k₂ : C.U₂.Comp, ∃ h : GA D (T.V j σ), (C.dict₂ h).1 = k₂ := by
  first | exact @GlobalTheory.CoverOnto.exists_dict₂_comp | exact GlobalTheory.CoverOnto.exists_dict₂_comp | (intros; apply GlobalTheory.CoverOnto.exists_dict₂_comp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalIsometryMapsFlagDomainFramesStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.rationalIsometry_maps_flagDomain_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (γ : GL (Fin r) E), X.p0 = X'.p0 → (∀ τ, τ ∈ X.Ψ ↔ τ ∈ X'.Ψ) → (∀ v w, herm X.Gm ((γ : Matrix (Fin r) (Fin r) E).mulVec v) ((γ : Matrix (Fin r) (Fin r) E).mulVec w) = herm X'.Gm v w) → ∀ (x : Frame X'.Ψ r) (x' : Frame X.Ψ r), x ∈ X'.dom → (∀ (τ : E →+* ℂ) (h₂ : τ ∈ X'.Ψ) (h₁ : τ ∈ X.Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin r) (Fin r) E).map τ * mat x ⟨τ, h₂⟩) → x' ∈ X.dom := by
  first | exact @GlobalTheory.FrameDom.mem_dom_of_isometry | exact GlobalTheory.FrameDom.mem_dom_of_isometry | (intros; apply GlobalTheory.FrameDom.mem_dom_of_isometry <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverComponentOverBaseComponentRationalIsometry

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverFrame

theorem comp_over_comp : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ k₂ : C.U₂.Comp, ∃ (k : (T.U j σ).Comp) (γ : GL (Fin D.R.r) D.host.E), (((T.U j σ).X k).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X k₂).Λ : Set _) ∧ (∀ v w, herm ((T.U j σ).X k).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X k₂).Gm v w) ∧ (∀ h, (C.dict₂ h).1 = k₂ → (T.dict j σ h).1 = k) ∧ ∀ (x : Frame (C.U₂.X k₂).Ψ D.R.r) (x' : Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ (C.U₂.X k₂).dom → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X k₂).Ψ) (h₁ : τ ∈ ((T.U j σ).X k).Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → x' ∈ ((T.U j σ).X k).dom ∧ ∃ t : ℂ, t ≠ 0 ∧ ∀ n : ℕ, ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → rdU C.U₂ f₂ k₂ x = t ^ n * rdU (T.U j σ) f k x' := by
  intro D T hT j hj σ hσ C hC k₂
  obtain ⟨h₀, rfl⟩ := GlobalTheory.T.exists_coverDictionary_adelic_element_component D T hT j hj σ hσ C hC k₂
  obtain ⟨γ, hΛ, hiso, hfr⟩ := GlobalTheory.T.base_cover_frames_differ_by_rational_isometry D T hT j hj σ hσ C hC h₀
  refine ⟨(T.dict j σ h₀).1, γ, hΛ, hiso, fun h hh => GlobalTheory.T.cover_component_eq_implies_base_component_eq D T hT j hj σ hσ C hC h h₀ hh,
    fun x x' hx hxx' => ?_⟩
  have hU := hT.unf j hj σ hσ
  have hU₂ := hC.2.2.2.1
  have hx' : x' ∈ ((T.U j σ).X (T.dict j σ h₀).1).dom :=
    GlobalTheory.T.rationalIsometry_maps_flagDomain_frames _ _ _ _ γ ((hU.2.1 _).1.trans (hU₂.2.1 _).1.symm)
      (fun τ => ((hU.2.1 _).2 τ).trans ((hU₂.2.1 _).2 τ).symm) hiso x x' hx hxx'
  exact ⟨hx', GlobalTheory.T.coverReading_eq_pow_mul_movedFrameReading D T hT j hj σ hσ C hC h₀ γ hΛ hiso hfr x x' hx hx' hxx'⟩

end GlobalTheory.CoverFrame
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverComponentOverBaseComponentRationalIsometryStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.coverComponent_over_baseComponent_rationalIsometry : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ k₂ : C.U₂.Comp, ∃ (k : (T.U j σ).Comp) (γ : GL (Fin D.R.r) D.host.E), (((T.U j σ).X k).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X k₂).Λ : Set _) ∧ (∀ v w, herm ((T.U j σ).X k).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X k₂).Gm v w) ∧ (∀ h, (C.dict₂ h).1 = k₂ → (T.dict j σ h).1 = k) ∧ ∀ (x : Frame (C.U₂.X k₂).Ψ D.R.r) (x' : Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ (C.U₂.X k₂).dom → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X k₂).Ψ) (h₁ : τ ∈ ((T.U j σ).X k).Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → x' ∈ ((T.U j σ).X k).dom ∧ ∃ t : ℂ, t ≠ 0 ∧ ∀ n : ℕ, ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → rdU C.U₂ f₂ k₂ x = t ^ n * rdU (T.U j σ) f k x' := by
  first | exact @GlobalTheory.CoverFrame.comp_over_comp | exact GlobalTheory.CoverFrame.comp_over_comp | (intros; apply GlobalTheory.CoverFrame.comp_over_comp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniformisedLevelCoverExistsConstantsDominantWeig

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverRead.Cover

theorem exists_pinned_dom : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ,
    GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ n : ℕ, ∃ cc₂ : C.U₂.Comp → ℂ,
      ∀ a : (D.host.E →+* ℂ) × ℕ → ℕ, Dom a n → ({ C with cc₂ := cc₂ } : Cover T j σ).IsPinned a n := by
  intro D T hT j hj σ hσ C hC n
  obtain ⟨u, hu1, hu⟩ := GlobalTheory.T.exists_unitConstant_coverPullbackReading D T hT j hj σ hσ C hC n
  choose k γ hk using fun k₂ => GlobalTheory.T.coverComponent_over_baseComponent_rationalIsometry D T hT j hj σ hσ C hC k₂
  have hu0 : ∀ k₂, u k₂ ≠ 0 := fun k₂ h => by simpa [h] using hu1 k₂
  refine ⟨fun k₂ => T.cE j σ (k k₂) / u k₂, fun a ha => ⟨?_, ?_⟩⟩
  · intro k₂
    show ‖T.cE j σ (k k₂) / u k₂‖ = 1
    rw [norm_div, hu1, hT.cUnit j hj σ hσ, div_one]
  · intro f hf f₂ hf₂ hp
    funext g
    have hp' : C.IsPull f f₂ := hp
    have h3 : (T.dict j σ g).1 = k (C.dict₂ g).1 := (hk (C.dict₂ g).1).2.2.1 g rfl
    show (lieFac (T.Q.Dw j) (xiR D) a : ℂ) *
        (T.cE j σ (k (C.dict₂ g).1) / u (C.dict₂ g).1 * T.mu j σ g * rdU C.U₂ f₂ (C.dict₂ g).1 (C.dict₂ g).2) =
      (lieFac (T.Q.Dw j) (xiR D) a : ℂ) *
        (T.cE j σ (T.dict j σ g).1 * T.mu j σ g * rdU (T.U j σ) f (T.dict j σ g).1 (T.dict j σ g).2)
    rw [hu a ha f hf f₂ hf₂ hp' g, ← h3]
    field_simp [hu0 (C.dict₂ g).1]

end GlobalTheory.CoverRead.Cover
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniformisedLevelCoverExistsConstantsDominantWeigStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.uniformisedLevelCover_exists_constants_dominantWeights : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ n : ℕ, ∃ cc₂ : C.U₂.Comp → ℂ, ∀ a : (D.host.E →+* ℂ) × ℕ → ℕ, Dom a n → ({ C with cc₂ := cc₂ } : Cover T j σ).IsPinned a n := by
  first | exact @GlobalTheory.CoverRead.Cover.exists_pinned_dom | exact GlobalTheory.CoverRead.Cover.exists_pinned_dom | (intros; apply GlobalTheory.CoverRead.Cover.exists_pinned_dom <;> assumption)
end
end
