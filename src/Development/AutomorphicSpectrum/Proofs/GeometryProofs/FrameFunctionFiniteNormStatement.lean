module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBareNormDisc
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteConstantAllHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatZeroFromResolutionAndGagaStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexUniformisationHolds
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitAnalyticFunction
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionAnalyticNorm
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsConstMul
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFramesInvertibleChange
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FramedPointSpecialization
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.MemOfFixedByAutomorphisms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBareNormDisc
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodReductionDvrModelExistsStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IrreducibleComponentClopenStatement
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FrameRatioConstantRational

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

namespace PositivityTheory.Xgn.FrameRatioConstant

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem ratio_frames {U : Set (Xo.XF c)} {τ : E →+* ℂ} {φ φ' : FrameFn Xo c} (h : IsLineFn U τ φ)
    (h' : IsLineFn U τ φ') {F : Type} [Field F] {β : c.F →+* F} {y : Sp F ⟶ Xo.XF c} {v v' : Vecs y D.p}
    {w w' : Vecs y D.q} (hf : IsFramed U τ β y v w) (hf' : IsFramed U τ β y v' w') {r : F}
    (hr : φ' F y v w = r * φ F y v w) : φ' F y v' w' = r * φ F y v' w' := by
  obtain ⟨-, A, hA, A', hA', -⟩ := GlobalTheory.CompanionTheory.Ar.LocFn.FrameChange.eigFrame_change _ F Xo.univ.t.G (under y) _
    Xo.univ.t.act _ _ _ v v' hf.2.2.1 hf'.2.2.1
  obtain ⟨-, B, hB, -⟩ := GlobalTheory.CompanionTheory.Ar.LocFn.FrameChange.eigFrame_change _ F Xo.univ.t.G (under y) _
    Xo.univ.t.act _ _ _ w w' hf.2.2.2 hf'.2.2.2
  have hd : A.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hA'
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have e := h.chg F β y v w v' w' A B hf hf' hA hB
  have e' := h'.chg F β y v w v' w' A B hf hf' hA hB
  apply mul_right_cancel₀ hd
  rw [e', hr, _root_.mul_assoc, _root_.mul_assoc, e]

theorem ratio_spec {U : Set (Xo.XF c)} {τ : E →+* ℂ} {φ φ' : FrameFn Xo c} {κ : ℂ} (h : IsLineFn U τ φ)
    (h' : IsLineFn U τ φ')
    (hκ : ∀ y v w, IsFramed U τ (algebraMap c.F ℂ) y v w → φ' ℂ y v w = κ * φ ℂ y v w)
    {F : Type} [Field F] {β : c.F →+* F} {y : Sp F ⟶ Xo.XF c} {v : Vecs y D.p}
    {w : Vecs y D.q} (hf : IsFramed U τ β y v w) :
    ∃ (k : Type) (_ : Field k) (β₀ : c.F →+* k) (f : k →+* F) (j : k →+* ℂ) (r : k), r ≠ 0 ∧ f.comp β₀ = β ∧
      j.comp β₀ = algebraMap c.F ℂ ∧ φ' F y v w = f r * φ F y v w ∧
      ∀ j' : k →+* ℂ, j'.comp β₀ = algebraMap c.F ℂ → j' r = κ := by
  obtain ⟨k, _, β₀, y₀, v₀, w₀, f, j, h₀, hβ, hj, rfl, up⟩ :=
    PositivityTheory.Xgn.framed_point_specialization E H D l Xo c U τ F β y v w hf
  have n0 := h.ne k β₀ y₀ v₀ w₀ h₀
  have n0' := h'.ne k β₀ y₀ v₀ w₀ h₀
  refine ⟨k, inferInstance, β₀, f, j, φ' k y₀ v₀ w₀ / φ k y₀ v₀ w₀, div_ne_zero n0' n0, hβ, hj, ?_, ?_⟩
  · obtain ⟨v', w', hf', ev, ew⟩ := up F f
    rw [hβ] at hf'
    refine ratio_frames h h' hf' hf ?_
    rw [h.nat k F f β₀ y₀ v₀ w₀ _ v' w' h₀ rfl ev ew, h'.nat k F f β₀ y₀ v₀ w₀ _ v' w' h₀ rfl ev ew, ← map_mul,
      div_mul_cancel₀ _ n0]
  · intro j' hj'
    obtain ⟨v', w', hf', ev, ew⟩ := up ℂ j'
    rw [hj'] at hf'
    have e := hκ _ v' w' hf'
    rw [h.nat k ℂ j' β₀ y₀ v₀ w₀ _ v' w' h₀ rfl ev ew, h'.nat k ℂ j' β₀ y₀ v₀ w₀ _ v' w' h₀ rfl ev ew] at e
    rw [map_div₀, e, mul_div_cancel_right₀ _ ((map_ne_zero j').2 n0)]

end PositivityTheory.Xgn.FrameRatioConstant

open PositivityTheory.Xgn.FrameRatioConstant in
theorem PositivityTheory.Xgn.frame_ratio_constant_rational : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ φ' : FrameFn Xo c) (κ : ℂ), τ (H.rt : E) = H.rt0 → IsLineFn U τ φ → IsLineFn U τ φ' → (∀ y v w, IsFramed U τ (algebraMap c.F ℂ) y v w → φ' ℂ y v w = κ * φ ℂ y v w) → ∃ x : c.F, x ≠ 0 ∧ ∀ (F : Type) [Field F] (βF : c.F →+* F) y v w, IsFramed U τ βF y v w → φ' F y v w = βF x * φ F y v w := by
  intro E _ _ _ H D l Xo c U τ φ φ' κ _ h h' hκ
  by_cases hex : ∃ (F : Type) (_ : Field F) (β : c.F →+* F) (y : Sp F ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q),
      IsFramed U τ β y v w
  · obtain ⟨F₀, _, β₁, y₁, v₁, w₁, hf₁⟩ := hex
    obtain ⟨k, _, β₀, -, j, r, hr, -, hj, -, hall⟩ := ratio_spec h h' hκ hf₁
    have hjr := hall j hj
    have hmem : κ ∈ c.F := by
      refine PositivityTheory.Xgn.mem_of_fixed_by_automorphisms c.F κ c.fin fun g hg => ?_
      have := hall (g.toRingHom.comp j) (by
        rw [RingHom.comp_assoc, hj]
        ext a
        exact hg a a.2)
      rw [RingHom.comp_apply, hjr] at this
      exact this
    refine ⟨⟨κ, hmem⟩, fun h0 => ?_, fun F _ βF y v w hf => ?_⟩
    · have : κ = 0 := congrArg Subtype.val h0
      exact (map_ne_zero j).2 hr (hjr.trans this)
    · obtain ⟨k', _, β₀', f, j', r', -, hβ, hj', e, hall'⟩ := ratio_spec h h' hκ hf
      have : r' = β₀' ⟨κ, hmem⟩ := j'.injective (by
        rw [hall' j' hj']
        exact (DFunLike.congr_fun hj' ⟨κ, hmem⟩).symm)
      rw [e, this, ← hβ]
      rfl
  · exact ⟨1, one_ne_zero, fun F _ βF y v w hf => absurd ⟨F, inferInstance, βF, y, v, w, hf⟩ hex⟩
end
end

-- Source module: Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.LineFunctionModelRatio

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

namespace PositivityTheory.Xgn.LineFunctionModelRatio₂

theorem exists_typeFn {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q : ℕ) :
    ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H p q ty := by
  classical
  let m : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then p else q
  let e := Fintype.equivFin (Σ τ : E →+* ℂ, Fin (m τ))
  refine ⟨_, fun i => (e.symm i).1, ?_⟩
  have key : ∀ τ : E →+* ℂ, Nat.card {i // (e.symm i).1 = τ} = m τ := by
    intro τ
    have e1 : {i // (e.symm i).1 = τ} ≃ Fin (m τ) :=
      (e.symm.subtypeEquiv (fun _ => Iff.rfl)).trans (Equiv.sigmaSubtype τ)
    rw [Nat.card_congr e1, Nat.card_fin]
  intro τ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [key]; simp [m, h]
  · rw [key]; simp [m, h]

end PositivityTheory.Xgn.LineFunctionModelRatio₂

theorem PositivityTheory.Xgn.line_function_model_ratio : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Y' : Model Xo c β') (U : Set (Xo.XF c)) (Z : CptOver Y U) (Z' : CptOver Y' U) (τ : E →+* ℂ) (φ φ' : FrameFn Xo c), FracBase β → FracBase β' → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → Z.IsGeom → Z'.IsGeom → FlatOnModel Z τ φ → FlatOnModel Z' τ φ' → ∃ x : c.F, x ≠ 0 ∧ ∀ (F : Type) [Field F] (βF : c.F →+* F) y v w, IsFramed U τ βF y v w → φ' F y v w = βF x * φ F y v w := by
  intro hR hG E _ _ _ H D l Xo c O _ β Y O' _ β' Y' U Z Z' τ φ φ' hO hO' hpq hτ hZ hZ' hφ hφ'
  obtain ⟨g, ty, hty⟩ := PositivityTheory.Xgn.LineFunctionModelRatio₂.exists_typeFn H D.p D.q
  obtain ⟨FU⟩ := GlobalTheory.CompanionTheory.Ar.Top.complex_uniformisation_holds E H D l Xo
    ((algebraMap c.F ℂ).comp (IntermediateField.inclusion c.le).toRingHom) g ty hpq rfl hty
  obtain ⟨Φ, hΦ, -⟩ := GlobalTheory.CompanionTheory.Ar.Flat.anUnit E H D l Xo c τ τ (algebraMap c.F ℂ) g ty FU hty hτ (fun _ => rfl)
  obtain ⟨κ, hκ, h₁⟩ := GlobalTheory.CompanionTheory.Ar.Flat.flat_eq_const_mul_unitAn hR hG E H D l Xo c O β Y U Z τ
    (algebraMap c.F ℂ) Φ φ hO hpq hτ hτ hZ hΦ hφ.1 hφ
  obtain ⟨κ', -, h₂⟩ := GlobalTheory.CompanionTheory.Ar.Flat.flat_eq_const_mul_unitAn hR hG E H D l Xo c O' β' Y' U Z' τ
    (algebraMap c.F ℂ) Φ φ' hO' hpq hτ hτ hZ' hΦ hφ'.1 hφ'
  refine PositivityTheory.Xgn.frame_ratio_constant_rational E H D l Xo c U τ φ φ' (κ' / κ) hτ hφ.1 hφ'.1 fun y v w hf => ?_
  rw [h₁ y v w hf, h₂ y v w hf]
  field_simp
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionTwoModelsRelay

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

theorem _root_.GlobalTheory.CompanionTheory.Relay.frame_function_two_models_relay : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Y' : Model Xo c β') (U : Set (Xo.XF c)) (Z : CptOver Y U) (Z' : CptOver Y' U) (τ : E →+* ℂ) (φ φ' : FrameFn Xo c), FracBase β → FracBase β' → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → Z.IsGeom → Z'.IsGeom → FlatOnModel Z τ φ → FlatOnModel Z' τ φ' → ∃ x : c.F, x ≠ 0 ∧ ∀ (F : Type) [Field F] (βF : c.F →+* F) y v w, IsFramed U τ βF y v w → φ' F y v w = βF x * φ F y v w := by
  first | exact @PositivityTheory.Xgn.line_function_model_ratio | exact PositivityTheory.Xgn.line_function_model_ratio
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionTwoModelsRelayStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

theorem _root_.GlobalTheory.T.frame_function_two_models_relay : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Y' : Model Xo c β') (U : Set (Xo.XF c)) (Z : CptOver Y U) (Z' : CptOver Y' U) (τ : E →+* ℂ) (φ φ' : FrameFn Xo c), FracBase β → FracBase β' → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → Z.IsGeom → Z'.IsGeom → FlatOnModel Z τ φ → FlatOnModel Z' τ φ' → ∃ x : c.F, x ≠ 0 ∧ ∀ (F : Type) [Field F] (βF : c.F →+* F) y v w, IsFramed U τ βF y v w → φ' F y v w = βF x * φ F y v w := by
  first | exact @GlobalTheory.CompanionTheory.Relay.frame_function_two_models_relay | exact GlobalTheory.CompanionTheory.Relay.frame_function_two_models_relay | (intros; apply GlobalTheory.CompanionTheory.Relay.frame_function_two_models_relay <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionFiniteNorm

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br.FinGood

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

theorem finGood : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (φ : FrameFn Xo c) (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), FracBase β → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → U ∈ irreducibleComponents (Xo.XF c) → Z.IsGeom → FlatOnModel Z τ φ → l.GoodAt p → ∃ t : ℝ, HasFinNorm U τ φ p κ t := by
  intro hRes hGaga E _ _ _ H D l Xo c O _ β Y U Z τ φ p κ hβ hpq hrt hU hZ hφ hgood
  obtain ⟨O', _, _, _, β', Y', hβ', hκ, hsplit, hN3⟩ := GlobalTheory.T.good_reduction_dvr_model_exists E H D l Xo c p κ hpq hgood
  obtain ⟨-, hne, hgeom⟩ := GlobalTheory.T.irreducible_component_clopen E H D l Xo c U hU
  obtain ⟨Z'⟩ := hne O' β' Y' hβ'
  have hZ' : Z'.IsGeom := hgeom O β Y O' β' Y' Z Z' hβ hβ' hZ
  obtain ⟨φ', hline', hflat', -⟩ := GlobalTheory.T.flat_zero_from_resolution_and_gaga hRes hGaga E H D l Xo c O' β' Y' U Z' τ hβ' hpq hrt hZ'
  obtain ⟨t', ht'⟩ := GlobalTheory.T.finite_constant_all_holds E H D l Xo c O' β' Y' U Z' τ p κ φ' hrt hβ'.1 hκ hsplit hN3 hZ' hflat' hline'
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.T.frame_function_two_models_relay hRes hGaga E H D l Xo c O β Y O' β' Y' U Z Z' τ φ φ' hβ hβ' hpq hrt hZ hZ' hφ hflat'
  refine ⟨t' - Real.log ‖κ x‖, ?_⟩
  unfold GlobalTheory.CompanionTheory.Ar.Fl.HasFinNorm
  intro V K _ _ _ _ _ _ j β₁ y v w T tK m m' hj hjβ hfr hv hw
  have h1 := ht' V K j β₁ y v w T tK m m' hj hjβ hfr hv hw
  have hjx : j (β₁ x) = κ x := by rw [← hjβ]; rfl
  have hφne : j (φ K y v w) ≠ 0 := (map_ne_zero j).mpr (hφ.1.ne K β₁ y v w hfr)
  have hxne : j (β₁ x) ≠ 0 := (map_ne_zero j).mpr ((map_ne_zero β₁).mpr hx0)
  rw [hx K β₁ y v w hfr, map_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hxne) (norm_ne_zero_iff.mpr hφne), hjx] at h1
  linarith

end GlobalTheory.CompanionTheory.Ar.Br.FinGood
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionFiniteNormStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

theorem _root_.GlobalTheory.T.frame_function_finite_norm : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (φ : FrameFn Xo c) (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), FracBase β → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → U ∈ irreducibleComponents (Xo.XF c) → Z.IsGeom → FlatOnModel Z τ φ → l.GoodAt p → ∃ t : ℝ, HasFinNorm U τ φ p κ t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Br.FinGood.finGood | exact GlobalTheory.CompanionTheory.Ar.Br.FinGood.finGood | (intros; apply GlobalTheory.CompanionTheory.Ar.Br.FinGood.finGood <;> assumption)
end
end
