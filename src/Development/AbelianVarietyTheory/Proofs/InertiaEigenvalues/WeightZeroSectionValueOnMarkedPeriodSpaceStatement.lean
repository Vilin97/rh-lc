module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CXiValIff
public import Formalism.LocalToGlobal.IndefiniteReal.FWTie
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MarkedIsometryHalf
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AutConjTranslatesDetCharacterMarkings
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryMatrixOfLatticeIsometry
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinitePartPreservesFormDetNormOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingConjugateComponentAdelic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RationalPointsAdelicUnitaryEqUnitaryStatement
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FamilyUniformisationPointsEqMarkedIsometryStatement
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NegBaseElementImNegBaseEmbedding
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitFrameEqOrthonormalMulTriangular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.WeightZeroSectionValueConjPoint
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCharacterEqOfMarkedLatticeIsometry

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix
namespace GlobalTheory.MarkIso

open GlobalTheory.Member



theorem xi_det_eq_of_marked_isometry : ∀ {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} (l : Level H) (V : HSp D)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hio : LinearMap.range io = latG V 1)
    (A A' : Datum H) (t : Dw.La →ₗ[𝓞 D.host.E] A.La) (t' : Dw.La →ₗ[𝓞 D.host.E] A'.La)
    (X X' : Data D.host.E V.rank) (φ : A.La ≃ₗ[𝓞 D.host.E] X.Λ) (φ' : A'.La ≃ₗ[𝓞 D.host.E] X'.Λ) (g g' : GA D V)
    (hW : ModelW V rfl X) (hW' : ModelW V rfl X')
    (hE : ∀ a b, ((A.EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (-X.ξ0 * herm X.Gm (φ a : Fin V.rank → D.host.E) (φ b)))
    (hE' : ∀ a b, ((A'.EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (-X'.ξ0 * herm X'.Gm (φ' a : Fin V.rank → D.host.E) (φ' b)))
    (hL : (X.Λ : Set (Fin V.rank → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast rfl) '' (latG V g : Set _))
    (hL' : (X'.Λ : Set (Fin V.rank → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast rfl) '' (latG V g' : Set _))
    (hm : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g, finVec V ((φ (t a) : Fin V.rank → D.host.E) ∘ Fin.cast rfl) -
        (finHom V g).1.mulVec (finVec V (io a)) = (l.M : ℕ) • w)
    (hm' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g', finVec V ((φ' (t' a) : Fin V.rank → D.host.E) ∘ Fin.cast rfl) -
        (finHom V g').1.mulVec (finVec V (io a)) = (l.M : ℕ) • w)
    (gam : A.La ≃ₗ[𝓞 D.host.E] A'.La) (hgE : ∀ a b, A'.EF (gam a) (gam b) = A.EF a b)
    (hgm : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ x, gam (t a) = t' a + l.M • x)
    (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)
    (hxi1 : ∀ u : GA D V, gLat V u = latHat V → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)),
      ((Matrix.GeneralLinearGroup.det (finHom V u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
        (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (l.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom V u)) = 1)
    (hxi2 : ∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V γ)) = 1), xi (Matrix.GeneralLinearGroup.det (finHom V g')) = xi (Matrix.GeneralLinearGroup.det (finHom V g)) := by
  intro D H Dw l V io hio A A' t t' X X' φ φ' g g' hW hW' hE hE' hL hL' hm hm' gam hgE hgm xi hxi1 hxi2
  have hGm : X'.Gm = X.Gm := hW'.1.trans hW.1.symm
  have hξ : X'.ξ0 = X.ξ0 := hW'.2.trans hW.2.symm
  let φL : A.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) := X.Λ.subtype ∘ₗ φ.toLinearMap
  let φL' : A'.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) := X'.Λ.subtype ∘ₗ φ'.toLinearMap
  have hr : Set.range φL = X.Λ := by
    ext v
    exact ⟨by rintro ⟨a, rfl⟩; exact (φ a).2, fun hv => ⟨φ.symm ⟨v, hv⟩,
      congrArg Subtype.val (φ.apply_symm_apply ⟨v, hv⟩)⟩⟩
  have hr' : Set.range φL' = X'.Λ := by
    ext v
    exact ⟨by rintro ⟨a, rfl⟩; exact (φ' a).2, fun hv => ⟨φ'.symm ⟨v, hv⟩,
      congrArg Subtype.val (φ'.apply_symm_apply ⟨v, hv⟩)⟩⟩
  have hcc : cc (-X.ξ0) = -(-X.ξ0) := by
    have := X.ξ0_im
    simp only [cc, map_neg] at this ⊢
    rw [this]
  obtain ⟨δ', hδ1, hδ2⟩ := GlobalTheory.IsoExt.exists_unitary_of_isometry _ H A A' V.rank (-X.ξ0) X.Gm φL φL' gam hcc
    ⟨Subtype.val_injective.comp φ.injective, by rw [hr]; exact X.Λ_span, X.Gm_herm, X.Gm_det,
      fun x y => hE x y⟩
    ⟨Subtype.val_injective.comp φ'.injective, by rw [hr']; exact X'.Λ_span, hGm ▸ X'.Gm_herm, hGm ▸ X'.Gm_det,
      fun x y => by rw [hE' x y, hGm, hξ]; rfl⟩ hgE
  have hG0 : X.Gm = -(HSpace.gram V)ᵀ := by
    rw [hW.1]
    simp
  obtain ⟨r1, -, r3, -⟩ := GlobalTheory.T.rational_points_adelicUnitary_eq_unitary D V
  obtain ⟨δ, hδ⟩ := r3 δ' (by rw [← hG0]; exact hδ1)
  have hLg : Set.range φL = latG V g := hr.trans (hL.trans (Set.image_id _))
  have hLg' : Set.range φL' = latG V g' := hr'.trans (hL'.trans (Set.image_id _))
  obtain ⟨u, h1, h2, h3⟩ := GlobalTheory.ConjMark.exists_of_matched V g g' δ δ' 1 l.M (by have := l.three_le; omega) l.Mb _
    l.prod hδ (fun v => by
      rw [← SetLike.mem_coe, ← SetLike.mem_coe, ← hLg, ← hLg']
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨_, hδ2 a⟩
      · rintro ⟨a, ha⟩
        refine ⟨gam.symm a, ?_⟩
        have e := hδ2 (gam.symm a)
        rw [LinearEquiv.apply_symm_apply, ha] at e
        have e' := congrArg (fun t => ((δ'⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ t) e
        simpa only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] using e'.symm)
    (fun v hv => by rw [Matrix.one_mulVec]; exact hv)
    (fun b hb x hx => by
      rw [← hio] at hx
      obtain ⟨x, rfl⟩ := hx
      have hv : b • x ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La) :=
        Submodule.smul_mem_smul hb trivial
      rw [← map_smul]
      refine ⟨φL (t (b • x)), φL' (t' (b • x)), hm _ hv, hm' _ hv, ?_⟩
      obtain ⟨z, hz⟩ := hgm _ hv
      refine ⟨-φL' z, ?_, ?_⟩
      · rw [← SetLike.mem_coe, ← hLg']
        exact ⟨-z, map_neg _ _⟩
      · rw [Matrix.one_mulVec, ← hδ2, hz, map_add (f := _), map_nsmul, smul_neg]
        abel)
  have hδQ : δ ∈ GQ V := (r1 δ).2 ⟨δ', hδ⟩
  have h3' : (finHom V u).1.det * 1 - 1 ∈
      GlobalTheory.AdLat.hat1 D.host.F ((algebraMap (𝓞 D.host.E) D.host.E) '' (l.Mb : Set (𝓞 D.host.E))) := by
    simpa [Algebra.TensorProduct.one_def] using h3
  have hq := GlobalTheory.DetTranslate.quot_cong_one D.host.F (cF D) l.M l.Mb _ l.coprime l.prod
    (fun b hb => ⟨H.bar b, Ideal.mem_map_of_mem (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) hb, H.bar_eq b⟩)
    _ _ 1 (GlobalTheory.DetTranslate.det_int_of_gLat V h1) (GlobalTheory.DetTranslate.det_int_of_gLat V (GlobalTheory.DetTranslate.gLat_one V))
    (finHom_herm_det D V u).2.1 (finHom_herm_det D V 1).2.1 h3' (by simp)
  have hK := hxi1 u h1 (by
    obtain ⟨w, hw, e⟩ := hq
    refine ⟨w, hw, ?_⟩
    simpa using e)
  have h4 := congrArg (fun g => xi (Matrix.GeneralLinearGroup.det g)) h2
  simp only [map_mul] at h4
  rw [hK, hxi2 δ hδQ, mul_one, one_mul] at h4
  exact h4

end GlobalTheory.MarkIso
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCharacterEqOfMarkedLatticeIsometryStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.detCharacter_eq_of_marked_lattice_isometry : ∀ {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} (l : Level H) (V : HSp D)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hio : LinearMap.range io = latG V 1)
    (A A' : Datum H) (t : Dw.La →ₗ[𝓞 D.host.E] A.La) (t' : Dw.La →ₗ[𝓞 D.host.E] A'.La)
    (X X' : Data D.host.E V.rank) (φ : A.La ≃ₗ[𝓞 D.host.E] X.Λ) (φ' : A'.La ≃ₗ[𝓞 D.host.E] X'.Λ) (g g' : GA D V)
    (hW : ModelW V rfl X) (hW' : ModelW V rfl X')
    (hE : ∀ a b, ((A.EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (-X.ξ0 * herm X.Gm (φ a : Fin V.rank → D.host.E) (φ b)))
    (hE' : ∀ a b, ((A'.EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (-X'.ξ0 * herm X'.Gm (φ' a : Fin V.rank → D.host.E) (φ' b)))
    (hL : (X.Λ : Set (Fin V.rank → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast rfl) '' (latG V g : Set _))
    (hL' : (X'.Λ : Set (Fin V.rank → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast rfl) '' (latG V g' : Set _))
    (hm : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g, finVec V ((φ (t a) : Fin V.rank → D.host.E) ∘ Fin.cast rfl) -
        (finHom V g).1.mulVec (finVec V (io a)) = (l.M : ℕ) • w)
    (hm' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g', finVec V ((φ' (t' a) : Fin V.rank → D.host.E) ∘ Fin.cast rfl) -
        (finHom V g').1.mulVec (finVec V (io a)) = (l.M : ℕ) • w)
    (gam : A.La ≃ₗ[𝓞 D.host.E] A'.La) (hgE : ∀ a b, A'.EF (gam a) (gam b) = A.EF a b)
    (hgm : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ x, gam (t a) = t' a + l.M • x)
    (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)
    (hxi1 : ∀ u : GA D V, gLat V u = latHat V → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)),
      ((Matrix.GeneralLinearGroup.det (finHom V u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
        (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (l.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom V u)) = 1)
    (hxi2 : ∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V γ)) = 1), xi (Matrix.GeneralLinearGroup.det (finHom V g')) = xi (Matrix.GeneralLinearGroup.det (finHom V g)) := by
  first | exact @GlobalTheory.MarkIso.xi_det_eq_of_marked_isometry | exact GlobalTheory.MarkIso.xi_det_eq_of_marked_isometry | (intros; apply GlobalTheory.MarkIso.xi_det_eq_of_marked_isometry <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDictionaryFrameMemOpenFrames

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix
open scoped ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DictDom

theorem frame_mem_dom : ∀ {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {σ : c.F →+* ℂ} (V : HSp D) (U : Unf Xo c σ V.rank) (dict : GA D V → Σ k, Frame (U.X k).Ψ V.rank)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hσ : GoodEmb c σ) (hA : l.A = 1) (hU : IsUnf U) (hW : ∀ k, ModelW V rfl (U.X k))
    (hD : DictLat U V rfl dict io e F ik φ th x₀) (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ))
    (hx₀ : ∀ k, IsOrthogonalFrame (U.X k) x₀), ∀ h, (dict h).2 ∈ (U.X (dict h).1).dom := by
  intro D H Dw l Xo c σ V U dict io g e F ik φ th x₀ hσ hA hU hW hD hth hx₀ h
  obtain ⟨γ, -, -, -, hmat⟩ := hD.2 h
  have hX := hW (dict h).1
  refine ((GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular _ _ (U.X (dict h).1).p0 (U.X (dict h).1).Ψ
    (U.X (dict h).1).Gm (U.X (dict h).1).Gm_herm).2.1 _ fun τ => ?_).1
  rw [← hx₀ (dict h).1 τ.1 τ.2, hmat τ, GlobalTheory.RecDictModel.gram_eq, GlobalTheory.RecDictModel.gram_eq, hX.1]
  have hu := GlobalTheory.RecDictModel.archM_unitary V (hth (dict h).1 τ) (γ * h)
  have e1 : ∀ A : Matrix (Fin V.rank) (Fin V.rank) ℂ, Matrix.reindex (finCongr rfl) (finCongr rfl) A = A :=
    fun A => rfl
  have e2 : ((-(Matrix.reindex (finCongr rfl) (finCongr rfl) V.gram).transpose).map τ.1).transpose =
      -(V.gram.map τ.1) := by
    ext a b; simp
  rw [e1, e2, Matrix.conjTranspose_mul]
  congr 1
  conv_rhs => rw [← hu]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

end GlobalTheory.DictDom
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDictionaryFrameMemOpenFramesStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.latticeDictionary_frame_mem_open_frames : ∀ {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {σ : c.F →+* ℂ} (V : HSp D) (U : Unf Xo c σ V.rank) (dict : GA D V → Σ k, Frame (U.X k).Ψ V.rank)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hσ : GoodEmb c σ) (hA : l.A = 1) (hU : IsUnf U) (hW : ∀ k, ModelW V rfl (U.X k))
    (hD : DictLat U V rfl dict io e F ik φ th x₀) (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ))
    (hx₀ : ∀ k, IsOrthogonalFrame (U.X k) x₀), ∀ h, (dict h).2 ∈ (U.X (dict h).1).dom := by
  first | exact @GlobalTheory.DictDom.frame_mem_dom | exact GlobalTheory.DictDom.frame_mem_dom | (intros; apply GlobalTheory.DictDom.frame_mem_dom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightZeroSectionValueOnMarkedPeriodSpace

section

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.MarkVal

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH
  Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix



theorem val_at_mark {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {n r : ℕ} (V : HSp D) (hr : V.rank = r) (σ0 : c.F →+* ℂ) (d : DeltaDat Xo c n)
    (U₂ : Unf d.Xo₂ d.c₂ (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)) r)
    (dict₂ : GA D V → Σ k, Frame (U₂.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (C : GlobalTheory.Member.Ctx d.Xo₂ d.c₂ (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)) V r) (hC : C.OK) (hι : C.ι = ι)
    (hx : C.x₀ = x₀) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (c0 : ℂ) (hf : d.cδ ∈ sec d.Xo₂ d.c₂ 0 0)
    (hxi1 : ∀ u : GA D V, gLat V u = latHat V → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)),
      ((Matrix.GeneralLinearGroup.det (finHom V u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
        (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (d.l₂.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom V u)) = 1)
    (hxi2 : ∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V γ)) = 1)
    (hv : GlobalTheory.OneMapAll.CXiAt V hr σ0 d U₂ dict₂ ι x₀ xi c0)
    (y : FrPt d.Xo₂ d.c₂ (CAt (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)))) (k : Fin C.F.n) (P : (C.F.Di k).La →+ (Fin C.g → ℂ))
    (hP : IsPeriod (C.F.Di k) (fun j => relab d.c₂ (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)) (C.e j).1) P)
    (hy : y.x = C.F.u k P) (h γ : GA D V) (hM : C.Mark h k γ) :
    toC (evR d.Xo₂ d.c₂ d.cδ y) = c0 * ((xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) : ℂ) := by
  classical
  subst hr hι hx
  obtain ⟨hU, hW, g₀, e₀, F, ik, φ, th, hth, hD, hval⟩ := hv
  have hσ : GoodEmb d.c₂ (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)) := hC.good
  have hor : ∀ j, IsOrthogonalFrame (U₂.X j) C.x₀ := by
    intro j τ hτ
    have h1 := hC.orth k
    have hG : (U₂.X j).Gm = (C.M.X k).Gm := by rw [(hW j).1, (hC.modelW k).1]
    have hp : (U₂.X j).p0 = (C.M.X k).p0 := ((hU.2.1 j).1).trans (hC.base.type k).1.symm
    have hΨ : τ ∈ (C.M.X k).Ψ := ((hC.base.type k).2 τ).2 (((hU.2.1 j).2 τ).1 hτ)
    rw [hG, hp]
    exact h1 τ hΨ

  have hdom := GlobalTheory.T.latticeDictionary_frame_mem_open_frames V U₂ dict₂ C.ι e₀ F ik φ th C.x₀ hσ hC.lA hU hW hD hth hor
  obtain ⟨h', hh'⟩ := GlobalTheory.TwistTie.exists_dict_over V U₂ dict₂ C.ι e₀ F ik φ th C.x₀ hσ hC.lA hC.pos hU hW hD hC.iota
    hth hor hdom y
  obtain ⟨P', -, hP', hy', -⟩ := hD.1.2 (dict₂ h').1 ⟨_, hdom h'⟩
  have hpt : C.F.u k P = F.u (ik (dict₂ h').1) P' := hy.symm.trans (hh'.trans hy')
  have hg : (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)) (IntermediateField.inclusion d.c₂.le (baseKA d.l₂).ρ) = H.rt0 := hC.good
  obtain ⟨gam, hgE, hgm⟩ := GlobalTheory.T.familyUniformisation_points_eq_marked_isometry C.F F hC.pos hg
    ((GlobalTheory.Relab.relab_good _ H d.l₂ d.c₂ _ hσ).2.2.2 Dw C.g C.e)
    ((GlobalTheory.Relab.relab_good _ H d.l₂ d.c₂ _ hσ).2.2.2 Dw g₀ e₀) (C.e.trans e₀.symm)
    (fun j => by simp) k (ik (dict₂ h').1) P P' hP hP' hpt
  obtain ⟨γ', hγ', hΛ', hm', -⟩ := hD.2 h'
  have hxe := GlobalTheory.T.detCharacter_eq_of_marked_lattice_isometry d.l₂ V C.ι hC.iota.emb.2 (C.F.Di k) (F.Di (ik (dict₂ h').1)) (C.F.t k) (F.t (ik (dict₂ h').1))
    (C.M.X k) (U₂.X (dict₂ h').1) (C.M.φ k) (φ (dict₂ h').1) (γ * h) (γ' * h') (hC.modelW k) (hW _)
    (hC.base.ef k) (hD.1.1 _) hM.2.1 hΛ' hM.2.2 hm' gam hgE hgm xi hxi1 hxi2
  have hv := hval h' γ' ⟨hγ', hΛ', hm'⟩
  rw [GlobalTheory.WeightZeroValue.evR_eq_of_same_point hf hh', ← hxe, ← hv]
  show _ = (if h'' : (dict₂ h').2 ∈ (U₂.X (dict₂ h').1).dom then toC (evR d.Xo₂ d.c₂ d.cδ (U₂.un _ ⟨_, h''⟩)) else 0)
  rw [dite_eq_left (hdom h')]

end GlobalTheory.MarkVal

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.MarkVal



theorem val_on_marked_space : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (a : Tp) (C : GlobalTheory.Member.Ctx (M.dδ a).Xo₂ (M.dδ a).c₂ ((inC M.c').comp ((M.dδ a).eF.symm : (M.dδ a).c₂.F →+* M.c'.F)) (Wc D i) D.R.r), C.OK → C.ι = iotaW T i → C.x₀ = T.x₀ ((i : ℕ) + 1) M.s0 → ∀ (f : Rul (M.dδ a).Xo₂ (M.dδ a).c₂) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (c0 : ℂ), f ∈ sec (M.dδ a).Xo₂ (M.dδ a).c₂ 0 0 → (∀ u : GA D (Wc D i), gLat (Wc D i) u = latHat (Wc D i) → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)), ((Matrix.GeneralLinearGroup.det (finHom (Wc D i) u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = ((M.dδ a).l₂.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) u)) = 1) → (∀ γ ∈ GQ (Wc D i), xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) γ)) = 1) → GlobalTheory.OneMapAll.CXiAt (Wc D i) (rank_Wc i) (inC M.c') { M.dδ a with cδ := f } (M.U₂ a) (M.dict₂ a) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) xi c0 → ∀ (y : FrPt (M.dδ a).Xo₂ (M.dδ a).c₂ (CAt ((inC M.c').comp ((M.dδ a).eF.symm : (M.dδ a).c₂.F →+* M.c'.F)))) (k : Fin C.F.n) P, IsPeriod (C.F.Di k) (fun j => relab (M.dδ a).c₂ ((inC M.c').comp ((M.dδ a).eF.symm : (M.dδ a).c₂.F →+* M.c'.F)) (C.e j).1) P → y.x = C.F.u k P → ∀ h γ : GA D (Wc D i), C.Mark h k γ → toC (evR (M.dδ a).Xo₂ (M.dδ a).c₂ f y) = c0 * ((xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) (γ * h))) : ℂˣ) : ℂ) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hcore hfw i Tp tup M hM a C hOK hι hx f xi c0 hf hxi1 hxi2 hCX y k P hPer hy h γ hmk
  exact val_at_mark (Wc D i) (rank_Wc i) (inC M.c') { M.dδ a with cδ := f } (M.U₂ a) (M.dict₂ a) (iotaW T i)
    (T.x₀ ((i : ℕ) + 1) M.s0) C hOK hι hx xi c0 hf hxi1 hxi2 hCX y k P hPer hy h γ hmk

end GlobalTheory.MarkVal
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightZeroSectionValueOnMarkedPeriodSpaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

theorem _root_.GlobalTheory.T.weightZeroSection_value_on_markedPeriodSpace : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (a : Tp) (C : GlobalTheory.Member.Ctx (M.dδ a).Xo₂ (M.dδ a).c₂ ((inC M.c').comp ((M.dδ a).eF.symm : (M.dδ a).c₂.F →+* M.c'.F)) (Wc D i) D.R.r), C.OK → C.ι = iotaW T i → C.x₀ = T.x₀ ((i : ℕ) + 1) M.s0 → ∀ (f : Rul (M.dδ a).Xo₂ (M.dδ a).c₂) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (c0 : ℂ), f ∈ sec (M.dδ a).Xo₂ (M.dδ a).c₂ 0 0 → (∀ u : GA D (Wc D i), gLat (Wc D i) u = latHat (Wc D i) → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)), ((Matrix.GeneralLinearGroup.det (finHom (Wc D i) u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = ((M.dδ a).l₂.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) u)) = 1) → (∀ γ ∈ GQ (Wc D i), xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) γ)) = 1) → GlobalTheory.OneMapAll.CXiAt (Wc D i) (rank_Wc i) (inC M.c') { M.dδ a with cδ := f } (M.U₂ a) (M.dict₂ a) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) xi c0 → ∀ (y : FrPt (M.dδ a).Xo₂ (M.dδ a).c₂ (CAt ((inC M.c').comp ((M.dδ a).eF.symm : (M.dδ a).c₂.F →+* M.c'.F)))) (k : Fin C.F.n) P, IsPeriod (C.F.Di k) (fun j => relab (M.dδ a).c₂ ((inC M.c').comp ((M.dδ a).eF.symm : (M.dδ a).c₂.F →+* M.c'.F)) (C.e j).1) P → y.x = C.F.u k P → ∀ h γ : GA D (Wc D i), C.Mark h k γ → toC (evR (M.dδ a).Xo₂ (M.dδ a).c₂ f y) = c0 * ((xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) (γ * h))) : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.MarkVal.val_on_marked_space | exact GlobalTheory.MarkVal.val_on_marked_space | (intros; apply GlobalTheory.MarkVal.val_on_marked_space <;> assumption)
end
end
