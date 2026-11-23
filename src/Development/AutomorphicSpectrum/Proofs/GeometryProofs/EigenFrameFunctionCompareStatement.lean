module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AffineChartBundleSectionsStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeVectorBundleStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameAtComponentPointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapFromSpecStalk
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermStalkClosedPointToBaseChange
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.UnitAtOfIsLineGenOn
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeLineLatticeVectorBundleStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PullbackFramesComplexPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.VectorsAtComplexPointStatement
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.PairFramesOnSet

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.LineGenerator

theorem exists_ιMulti_eq_smul {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ}
    {v b : Fin r → E} (h : ∀ i, v i ∈ Submodule.span Ω (Set.range b)) :
    ∃ α : Ω, exteriorPower.ιMulti Ω r v = α • exteriorPower.ιMulti Ω r b := by
  classical
  have hc : ∀ i, ∃ c : Fin r → Ω, ∑ j, c j • b j = v i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun Ω).1 (h i)
  choose c hc using hc
  have hv : v = fun i => ∑ j, c i j • b j := funext fun i => (hc i).symm
  have hsum : exteriorPower.ιMulti Ω r v =
      ∑ f : Fin r → Fin r, (∏ i, c i (f i)) • exteriorPower.ιMulti Ω r (fun i => b (f i)) := by
    rw [hv]
    refine ((exteriorPower.ιMulti Ω r (M := E)).toMultilinearMap.map_sum
      (fun i j => c i j • b j)).trans (Finset.sum_congr rfl fun f _ => ?_)
    exact (exteriorPower.ιMulti Ω r (M := E)).toMultilinearMap.map_smul_univ
      (fun i => c i (f i)) (fun i => b (f i))
  have hmem : exteriorPower.ιMulti Ω r v ∈ Submodule.span Ω {exteriorPower.ιMulti Ω r b} := by
    rw [hsum]
    refine Submodule.sum_mem _ fun f _ => Submodule.smul_mem _ _ ?_
    by_cases hf : Function.Injective f
    · let σ : Equiv.Perm (Fin r) := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf)
      have h5 : (fun i => b (f i)) = b ∘ σ := rfl
      rw [h5, (exteriorPower.ιMulti Ω r (M := E)).map_perm b σ]
      have hm := Submodule.mem_span_singleton_self (R := Ω) (exteriorPower.ιMulti Ω r b)
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
      · rw [hs, one_smul]
        exact hm
      · rw [hs, Units.neg_smul, one_smul]
        exact neg_mem hm
    · have h6 : ¬ Function.Injective (fun i => b (f i)) := fun hh =>
        hf (Function.Injective.of_comp (f := b) hh)
      rw [(exteriorPower.ιMulti Ω r (M := E)).map_eq_zero_of_not_injective _ h6]
      exact zero_mem _
  obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.1 hmem
  exact ⟨α, hα.symm⟩

theorem frame_mem_of_isVBOn {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {E : Type} [AddCommGroup E] [Module Ω E] {L : Lat ξ E} {T : Set (Cpt ξ)} {r : ℕ}
    {V : Submodule Ω E} {v : Fin r → E} {x : Cpt ξ} (hx : x ∈ T) (hL : L.IsVBOn T r V)
    (hv : L.IsFrameAt v x) (i : Fin r) : v i ∈ V := by
  obtain ⟨U, hU, e, he, hfr⟩ := hL x hx
  have h1 : v i ∈ L x := hv.2 ▸ Submodule.subset_span ⟨i, rfl⟩
  rw [(hfr x hx hU).2] at h1
  have h2 : Submodule.span (regAt ξ x) (Set.range e) ≤
      (Submodule.span Ω (Set.range e)).restrictScalars (regAt ξ x) :=
    Submodule.span_le.2 fun _ hy => Submodule.subset_span hy
  exact he ▸ h2 h1

theorem exists_wedge_coeff {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {E : Type} [AddCommGroup E] [Module Ω E] {L : Lat ξ E} {T : Set (Cpt ξ)} {r : ℕ}
    {V : Submodule Ω E} {v b : Fin r → E} {x : Cpt ξ} (hx : x ∈ T) (hL : L.IsVBOn T r V)
    (hb : Submodule.span Ω (Set.range b) = V) (hv : L.IsFrameAt v x) :
    ∃ α : Ω, α ≠ 0 ∧ exteriorPower.ιMulti Ω r v = α • exteriorPower.ιMulti Ω r b := by
  obtain ⟨α, hα⟩ := exists_ιMulti_eq_smul (v := v) (b := b)
    fun i => hb ▸ frame_mem_of_isVBOn hx hL hv i
  refine ⟨α, ?_, hα⟩
  rintro rfl
  exact GenModel.ιMulti_ne_zero hv.1 (by rw [hα, zero_smul])

theorem isGenAt_div : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (A B : Lat ξ V) (p q : ℕ) (Vp Vq : Submodule Ω V) (T : Set (Cpt ξ)) (b₁ v₁ : Fin p → V) (b₂ v₂ : Fin q → V) (x : Cpt ξ), x ∈ T → A.IsVBOn T p Vp → B.IsVBOn T q Vq → LinearIndependent Ω b₁ → Submodule.span Ω (Set.range b₁) = Vp → LinearIndependent Ω b₂ → Submodule.span Ω (Set.range b₂) = Vq → A.IsFrameAt v₁ x → B.IsFrameAt v₂ x → ∃ α κ : Ω, α ≠ 0 ∧ κ ≠ 0 ∧ exteriorPower.ιMulti Ω p v₁ = α • exteriorPower.ιMulti Ω p b₁ ∧ exteriorPower.ιMulti Ω q v₂ = κ • exteriorPower.ιMulti Ω q b₂ ∧ (lineLat A B p q (exteriorPower.ιMulti Ω p b₁) (exteriorPower.ιMulti Ω q b₂)).IsGenAt x (α / κ) := by
  intro X Ω _ ξ V _ _ A B p q Vp Vq T b₁ v₁ b₂ v₂ x hx hA hB hb₁ hs₁ hb₂ hs₂ hv₁ hv₂
  obtain ⟨α, hα, e₁⟩ := exists_wedge_coeff hx hA hs₁ hv₁
  obtain ⟨κ, hκ, e₂⟩ := exists_wedge_coeff hx hB hs₂ hv₂
  have hco : IsCoeffAt A B p q (exteriorPower.ιMulti Ω p b₁) (exteriorPower.ιMulti Ω q b₂) x (κ / α) :=
    ⟨α, κ, hα, hκ, by rw [GenModel.wedge_of_frame hv₁, e₁], by rw [GenModel.wedge_of_frame hv₂, e₂],
      div_mul_cancel₀ _ hα⟩
  have key := GlobalTheory.T.wedge_line_lattice_vector_bundle X Ω ξ V A B p q Vp Vq T _ _ hA hB (GenModel.ιMulti_ne_zero hb₁)
    (GenModel.ιMulti_ne_zero hb₂) ⟨x, hx, _, hco⟩
  exact ⟨α, κ, hα, hκ, e₁, e₂, key.2.2 x hx v₁ v₂ α κ hv₁ hv₂ e₁ e₂⟩

end GlobalTheory.CompanionTheory.Ar.Flat.LineGenerator
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.PairFramesOnSetStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.pair_frames_on_set : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (A B : Lat ξ V) (p q : ℕ) (Vp Vq : Submodule Ω V) (T : Set (Cpt ξ)) (b₁ v₁ : Fin p → V) (b₂ v₂ : Fin q → V) (x : Cpt ξ), x ∈ T → A.IsVBOn T p Vp → B.IsVBOn T q Vq → LinearIndependent Ω b₁ → Submodule.span Ω (Set.range b₁) = Vp → LinearIndependent Ω b₂ → Submodule.span Ω (Set.range b₂) = Vq → A.IsFrameAt v₁ x → B.IsFrameAt v₂ x → ∃ α κ : Ω, α ≠ 0 ∧ κ ≠ 0 ∧ exteriorPower.ιMulti Ω p v₁ = α • exteriorPower.ιMulti Ω p b₁ ∧ exteriorPower.ιMulti Ω q v₂ = κ • exteriorPower.ιMulti Ω q b₂ ∧ (lineLat A B p q (exteriorPower.ιMulti Ω p b₁) (exteriorPower.ιMulti Ω q b₂)).IsGenAt x (α / κ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.LineGenerator.isGenAt_div | exact GlobalTheory.CompanionTheory.Ar.Flat.LineGenerator.isGenAt_div | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.LineGenerator.isGenAt_div <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.PullbackFramesComplexPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.pullback_frames_complex_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) (b₁ v₁ : Fin D.p → Z.V) (b₂ v₂ : Fin D.q → Z.V) (X' : Scheme.{0}) (π : X' ⟶ Y.X) (ξ' : Sp Z.Ω ⟶ X') (y' : Sp ℂ ⟶ X') (yy : Sp ℂ ⟶ Xo.XF c) (v vz : Vecs yy D.p) (w wz : Vecs yy D.q) (α κ : Z.Ω) (r : ℂ), ξ' ≫ π = Z.ξ₀ ≫ Y.j → IsCptGen ξ' → yy ≫ Y.j = y' ≫ π → IsUnitAn τ σ Φ → IsFramed Set.univ τ σ yy v w → IsFramed Set.univ τ σ yy vz wz → (∀ i, ∃ v', Z.M.ValAt (yy ≫ Y.j) (b₁ i) v' ∧ SameVec Y yy (v i) v') → (∀ j, ∃ w', Z.M.ValAt (yy ≫ Y.j) (b₂ j) w' ∧ SameVec Y yy (w j) w') → (∀ i, ∃ v', Z.M.ValAt (yy ≫ Y.j) (v₁ i) v' ∧ SameVec Y yy (vz i) v') → (∀ j, ∃ w', Z.M.ValAt (yy ≫ Y.j) (v₂ j) w' ∧ SameVec Y yy (wz j) w') → (∀ q : Cpt (Z.ξ₀ ≫ Y.j), q.1 = centre (yy ≫ Y.j) → (Z.eig τ).IsFrameAt v₁ q ∧ (Z.eig (ComplexEmbedding.conjugate τ)).IsFrameAt v₂ q) → (∀ i, b₁ i ∈ eigSp Z.ρ (Z.inc.comp (tauIn c τ))) → (∀ j, b₂ j ∈ eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ)))) → α ≠ 0 → κ ≠ 0 → exteriorPower.ιMulti Z.Ω D.p v₁ = α • exteriorPower.ιMulti Z.Ω D.p b₁ → exteriorPower.ιMulti Z.Ω D.q v₂ = κ • exteriorPower.ιMulti Z.Ω D.q b₂ → ValAt ξ' y' (α / κ) r → Φ yy v w = Φ yy vz wz * r := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.PointCompare.point_compare | exact GlobalTheory.CompanionTheory.Ar.Flat.PointCompare.point_compare | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.PointCompare.point_compare <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFrameFunctionCompare

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_vecs {S : Scheme.{0}} {G : Over S} {R R' : Type} [CommRing R] [CommRing R'] (x : Sp R ⟶ S) (f : R →+* R')
    (y : Sp R' ⟶ S) (hy : y = spMap f ≫ x) {n : ℕ} (u : Fin n → (epsAt x ⟶ G)) :
    ∃ u' : Fin n → (epsAt y ⟶ G), ∀ i, (u' i).left = spMap (dualMap f) ≫ (u i).left :=
  ⟨fun i => LieCarrier.epsHom f x y hy.symm ≫ u i, fun i => rfl⟩

theorem extendsUnitAt_resolution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (X' : Scheme.{0}) (π : X' ⟶ Y.X) (s' : X' ⟶ Sp c.F) (d : ℕ) (ξ' : Sp Z.Ω ⟶ X') (W' W : X'.Opens) (jW : W'.toScheme ⟶ Xo.XF c) (F : (Sp ℂ ⟶ X') → ℂ), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → σ (tauIn c τ H.rt) = H.rt0 → IsUnitAn τ σ Φ → LinearIndependent Z.Ω b₁ → Submodule.span Z.Ω (Set.range b₁) = eigSp Z.ρ (Z.inc.comp (tauIn c τ)) → LinearIndependent Z.Ω b₂ → Submodule.span Z.Ω (Set.range b₂) = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) → π ≫ Y.s = s' ≫ spMap β → SmoothOfRelativeDimension d s' → Geo.ResK.HasSncCoords s' d (W' : Set X')ᶜ → ξ' ≫ π = Z.ξ₀ ≫ Y.j → IsCptGen ξ' → jW ≫ Y.j = W'.ι ≫ π → jW ≫ pullback.snd _ _ = W'.ι ≫ s' → W ≤ W' → (∀ (y' : Sp ℂ ⟶ X') (y : Sp ℂ ⟶ Xo.XF c), y' ≫ s' = spMap σ → ⊤ ≤ y' ⁻¹ᵁ W → genPt ξ' ⤳ centre y' → y ≫ Y.j = y' ≫ π → y ≫ pullback.snd _ _ = spMap σ → ∃ (v : Vecs y D.p) (w : Vecs y D.q), IsFramed Set.univ τ σ y v w ∧ ((∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b₁ i) v' ∧ SameVec Y y (v i) v') ∧ ∀ j, ∃ w', Z.M.ValAt (y ≫ Y.j) (b₂ j) w' ∧ SameVec Y y (w j) w') ∧ F y' = Φ y v w) → (∀ p : Cpt ξ', p.1 ∈ W → ((lineLat (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q (exteriorPower.ιMulti Z.Ω D.p b₁) (exteriorPower.ιMulti Z.Ω D.q b₂)).pull ξ' π (AddMonoidHom.id _)).IsGenAt p 1) → ∀ (x : Sp ℂ ⟶ X') (h : genPt ξ' ⤳ centre x), x ≫ s' = spMap σ → ∃ t : Z.Ω, ((lineLat (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q (exteriorPower.ιMulti Z.Ω D.p b₁) (exteriorPower.ιMulti Z.Ω D.q b₂)).pull ξ' π (AddMonoidHom.id _)).IsGenAt ⟨centre x, h⟩ t ∧ ExtendsUnitAt s' σ ξ' W F t x := by
  intro E _ _ _ H D l Xo c O _ β Y U Z τ σ Φ b₁ b₂ X' π s' d ξ' W' W jW F hβ hpq hτ hσ hΦ hb₁ hs₁ hb₂ hs₂ hπ hsm hsnc hξ hgen hj hjs hWW' hF hgen1 x h hx
  have hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' (Z.ξ₀ ≫ Y.j) π (RingHom.id Z.Ω) := by
    have e : Spec.map (CommRingCat.ofHom (RingHom.id Z.Ω)) = 𝟙 _ := Spec.map_id _
    show ξ' ≫ π = Spec.map (CommRingCat.ofHom (RingHom.id Z.Ω)) ≫ Z.ξ₀ ≫ Y.j
    rw [hξ, e, Category.id_comp]
  obtain ⟨hp, -, hpull⟩ := pull_reg_and_gen _ _ _ _ _ _ π _ hd ⟨centre x, h⟩
  let p₀ : Cpt (Z.ξ₀ ≫ Y.j) := ⟨π (centre x), hp⟩
  have hp₀ : p₀ ∈ Z.genFib := ⟨pullback.lift π s' hπ (centre x), by
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]⟩
  obtain ⟨hVB₁, hVB₂, -, -⟩ := GlobalTheory.T.eigen_lattice_vector_bundle E H D l Xo c O β Y U Z τ hβ hτ
  obtain ⟨A, hA, EB, _, _, MB, e₁, e₂, v₁, v₂, hp₀A, hfr, heig, hval⟩ :=
    GlobalTheory.T.frame_at_component_point E H D l Xo c O β Y U Z τ σ b₁ b₂ p₀ hβ hτ hb₁ hs₁ hb₂ hs₂ hp₀
  obtain ⟨hv₁, hv₂⟩ := hfr p₀ hp₀A
  obtain ⟨α, κ, hα, hκ, hαe, hκe, hgen0⟩ := GlobalTheory.T.pair_frames_on_set _ _ _ _ (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q _ _ Z.genFib
    b₁ v₁ b₂ v₂ p₀ hp₀ hVB₁ hVB₂ hb₁ hs₁ hb₂ hs₂ hv₁ hv₂
  refine ⟨α / κ, hpull _ _ hgen0, ?_⟩
  intro m B y hB hy hyσ b₀ hb₀ hyx
  have hxA : ⊤ ≤ x ⁻¹ᵁ (π ⁻¹ᵁ A) := fun q _ => by
    have : q = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    rw [this]
    exact hp₀A
  obtain ⟨ε, hh, hε, hdiff, hne, key⟩ := GlobalTheory.T.affine_chart_bundle_sections E H D l Xo c O β Y τ σ Φ X' π s' d W' jW A hA EB MB e₁ e₂ x hpq hτ hσ hΦ hπ hsm hsnc hj hjs hx hxA heig m B y hB hy hyσ b₀ hb₀ hyx
  refine ⟨ε, hh, hε, hdiff, hne, fun b hbB hbW r hr => ?_⟩
  obtain ⟨f, hf, hk⟩ := key b hbB
  have hc : genPt ξ' ⤳ centre (y b) := hr.choose
  have hW' : ⊤ ≤ y b ⁻¹ᵁ W' := fun q hq => hWW' (hbW hq)
  have hrange : Set.range (y b) ⊆ Set.range W'.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨q, rfl⟩
    exact hW' (show q ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  let y₀ : Sp ℂ ⟶ W'.toScheme := IsOpenImmersion.lift W'.ι (y b) hrange
  have e₀ : y₀ ≫ W'.ι = y b := IsOpenImmersion.lift_fac _ _ _
  let yy : Sp ℂ ⟶ Xo.XF c := y₀ ≫ jW
  have hyj : yy ≫ Y.j = y b ≫ π := by
    show (y₀ ≫ jW) ≫ Y.j = _
    rw [Category.assoc, hj, ← Category.assoc, e₀]
  have hys : yy ≫ pullback.snd _ _ = spMap σ := by
    show (y₀ ≫ jW) ≫ _ = _
    rw [Category.assoc, hjs, ← Category.assoc, e₀, hyσ b hbB.1]
  obtain ⟨v, w, hfrvw, ⟨hvv, hww⟩, hFe⟩ := hF (y b) yy (hyσ b hbB.1) hbW hc hyj hys
  have hyf : yy ≫ Y.j = spMap f ≫ hA.fromSpec := hyj.trans hf.symm
  obtain ⟨u₁, hu₁⟩ := exists_vecs hA.fromSpec f (yy ≫ Y.j) hyf (fun i => MB.pt (e₁ i))
  obtain ⟨u₂, hu₂⟩ := exists_vecs hA.fromSpec f (yy ≫ Y.j) hyf (fun i => MB.pt (e₂ i))
  have hover : (yy ≫ Y.j) ≫ Y.s = spMap (σ.comp β) := by
    rw [hyj, Category.assoc, hπ, ← Category.assoc, hyσ b hbB.1, ← Spec.map_comp]
    rfl
  obtain ⟨hE₁, hE₂⟩ := heig f (yy ≫ Y.j) u₁ u₂ hyf hover hu₁ hu₂
  have hspec : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (yy ≫ Y.j) := by
    have e : centre (yy ≫ Y.j) = π (centre (y b)) := by
      rw [hyj]; rfl
    rw [e, ← RegAtDom.map_genPt hd]
    exact hc.map π.continuous
  obtain ⟨hV₁, hV₂⟩ := hval f (yy ≫ Y.j) u₁ u₂ hyf hspec hu₁ hu₂
  choose a₁ ha₁ using fun i => exists_sameVec_left Y yy (u₁ i)
  choose a₂ ha₂ using fun i => exists_sameVec_left Y yy (u₂ i)
  have hfr₀ : IsFramed Set.univ τ σ yy a₁ a₂ := GlobalTheory.T.vectors_at_complex_point E H D l Xo c O β Y τ σ yy a₁ a₂ u₁ u₂ hys ha₁ ha₂ hE₁ hE₂
  have h₁ := (hk hW') yy a₁ a₂ u₁ u₂ hyj hys ha₁ ha₂ hu₁ hu₂
  have hqA : ∀ q : Cpt (Z.ξ₀ ≫ Y.j), q.1 = centre (yy ≫ Y.j) → q.1 ∈ A := fun q hq => by
    rw [hq, hyf, ← SetLike.mem_coe, ← hA.range_fromSpec]
    exact ⟨_, rfl⟩
  have h₂ := GlobalTheory.T.pullback_frames_complex_point E H D l Xo c O β Y U Z τ σ Φ b₁ v₁ b₂ v₂ X' π ξ' (y b) yy v a₁ w a₂ α κ r hξ hgen hyj hΦ hfrvw hfr₀ hvv hww
    (fun i => ⟨_, hV₁ i, ha₁ i⟩) (fun j => ⟨_, hV₂ j, ha₂ j⟩) (fun q hq => hfr q (hqA q hq))
    (fun i => hs₁ ▸ Submodule.subset_span ⟨i, rfl⟩) (fun j => hs₂ ▸ Submodule.subset_span ⟨j, rfl⟩)
    hα hκ hαe hκe hr
  rw [hFe, h₂, h₁]

end GlobalTheory.CompanionTheory.Ar.Flat
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFrameFunctionCompareStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.eigen_frame_function_compare : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (X' : Scheme.{0}) (π : X' ⟶ Y.X) (s' : X' ⟶ Sp c.F) (d : ℕ) (ξ' : Sp Z.Ω ⟶ X') (W' W : X'.Opens) (jW : W'.toScheme ⟶ Xo.XF c) (F : (Sp ℂ ⟶ X') → ℂ), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → σ (tauIn c τ H.rt) = H.rt0 → IsUnitAn τ σ Φ → LinearIndependent Z.Ω b₁ → Submodule.span Z.Ω (Set.range b₁) = eigSp Z.ρ (Z.inc.comp (tauIn c τ)) → LinearIndependent Z.Ω b₂ → Submodule.span Z.Ω (Set.range b₂) = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) → π ≫ Y.s = s' ≫ spMap β → SmoothOfRelativeDimension d s' → Geo.ResK.HasSncCoords s' d (W' : Set X')ᶜ → ξ' ≫ π = Z.ξ₀ ≫ Y.j → IsCptGen ξ' → jW ≫ Y.j = W'.ι ≫ π → jW ≫ pullback.snd _ _ = W'.ι ≫ s' → W ≤ W' → (∀ (y' : Sp ℂ ⟶ X') (y : Sp ℂ ⟶ Xo.XF c), y' ≫ s' = spMap σ → ⊤ ≤ y' ⁻¹ᵁ W → genPt ξ' ⤳ centre y' → y ≫ Y.j = y' ≫ π → y ≫ pullback.snd _ _ = spMap σ → ∃ (v : Vecs y D.p) (w : Vecs y D.q), IsFramed Set.univ τ σ y v w ∧ ((∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b₁ i) v' ∧ SameVec Y y (v i) v') ∧ ∀ j, ∃ w', Z.M.ValAt (y ≫ Y.j) (b₂ j) w' ∧ SameVec Y y (w j) w') ∧ F y' = Φ y v w) → (∀ p : Cpt ξ', p.1 ∈ W → ((lineLat (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q (exteriorPower.ιMulti Z.Ω D.p b₁) (exteriorPower.ιMulti Z.Ω D.q b₂)).pull ξ' π (AddMonoidHom.id _)).IsGenAt p 1) → ∀ (x : Sp ℂ ⟶ X') (h : genPt ξ' ⤳ centre x), x ≫ s' = spMap σ → ∃ t : Z.Ω, ((lineLat (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q (exteriorPower.ιMulti Z.Ω D.p b₁) (exteriorPower.ιMulti Z.Ω D.q b₂)).pull ξ' π (AddMonoidHom.id _)).IsGenAt ⟨centre x, h⟩ t ∧ ExtendsUnitAt s' σ ξ' W F t x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.extendsUnitAt_resolution | exact GlobalTheory.CompanionTheory.Ar.Flat.extendsUnitAt_resolution | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.extendsUnitAt_resolution <;> assumption)
end
end
